#!/usr/bin/env bash
set -euo pipefail

LEAN_VERSION='4.32.2'
LEAN_TOOLCHAIN="leanprover/lean4:v${LEAN_VERSION}"
MATHLIB_TAG='v4.32.2'
MATHLIB_COMMIT='905b95818eb32af7874a58b427f50c1711a5e96c'
MATHLIB_LAKE_MANIFEST_SHA256='015c7e00ead0f05f2a72b32d9bdef782d4689d05a6297f0ceb0ab5d196c164bd'
RELEASE_ARTIFACT="lean-${LEAN_VERSION}-linux.tar.zst"
RELEASE_SHA256='5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa'
RELEASE_BYTES='563991635'
MAX_PART_BYTES=$((450 * 1024 * 1024))
SPLIT_BYTES=$((440 * 1024 * 1024))

repo_root="${GITHUB_WORKSPACE:-$(pwd)}"
work_root="${RUNNER_TEMP:-/tmp}/lean-toolchain-factory"
out_dir="$repo_root/out"
logs_dir="$out_dir/logs"
parts_dir="$out_dir/parts"
package_dir="$work_root/package"
mathlib_dir="$work_root/mathlib4"
gates_file="$out_dir/gates.ndjson"

mkdir -p "$work_root" "$logs_dir" "$parts_dir" "$package_dir"
: > "$gates_file"

record_gate() {
  local id="$1" expected="$2" command="$3" log_file="$logs_dir/$1.log"
  printf '=== %s ===\n$ %s\n' "$id" "$command" | tee "$log_file"
  set +e
  bash -o pipefail -c "$command" >> "$log_file" 2>&1
  local exit_code=$?
  set -e
  cat "$log_file"

  local actual='FAIL'
  [[ $exit_code -eq 0 ]] && actual='PASS'
  jq -nc \
    --arg id "$id" \
    --arg command "$command" \
    --arg expectedOutcome "$expected" \
    --argjson actualExitCode "$exit_code" \
    --arg logFile "logs/$id.log" \
    --arg logSha256 "$(sha256sum "$log_file" | cut -d' ' -f1)" \
    '{id:$id,command:$command,expectedOutcome:$expectedOutcome,actualExitCode:$actualExitCode,logFile:$logFile,logSha256:$logSha256}' >> "$gates_file"

  if [[ "$actual" != "$expected" ]]; then
    echo "gate $id produced $actual, expected $expected" >&2
    return 1
  fi
}

echo "Downloading the pinned official Lean release."
curl --fail --location --retry 3 \
  "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/${RELEASE_ARTIFACT}" \
  --output "$work_root/$RELEASE_ARTIFACT"
printf '%s  %s\n' "$RELEASE_SHA256" "$work_root/$RELEASE_ARTIFACT" | sha256sum --check --strict | tee "$logs_dir/release-sha256.log"
actual_release_bytes="$(stat --format='%s' "$work_root/$RELEASE_ARTIFACT")"
[[ "$actual_release_bytes" == "$RELEASE_BYTES" ]] || { echo "release byte count mismatch" >&2; exit 1; }

mkdir -p "$work_root/lean-release"
tar --use-compress-program=unzstd -xf "$work_root/$RELEASE_ARTIFACT" -C "$work_root/lean-release"
lean_home="$(find "$work_root/lean-release" -mindepth 1 -maxdepth 1 -type d -name 'lean-*' -print -quit)"
[[ -n "$lean_home" ]]
export PATH="$lean_home/bin:$PATH"

record_gate 'lean-version' 'PASS' "lean --version"

echo "Cloning exactly Mathlib ${MATHLIB_TAG}."
git clone --depth 1 --branch "$MATHLIB_TAG" https://github.com/leanprover-community/mathlib4.git "$mathlib_dir" 2>&1 | tee "$logs_dir/mathlib-clone.log"
actual_mathlib_commit="$(git -C "$mathlib_dir" rev-parse HEAD)"
[[ "$actual_mathlib_commit" == "$MATHLIB_COMMIT" ]] || { echo "Mathlib commit mismatch: $actual_mathlib_commit" >&2; exit 1; }
[[ "$(tr -d '\r\n' < "$mathlib_dir/lean-toolchain")" == "$LEAN_TOOLCHAIN" ]] || { echo 'Mathlib Lean toolchain mismatch' >&2; exit 1; }
printf '%s  %s\n' "$MATHLIB_LAKE_MANIFEST_SHA256" "$mathlib_dir/lake-manifest.json" | sha256sum --check --strict | tee "$logs_dir/mathlib-release-manifest.log"
cp "$mathlib_dir/lake-manifest.json" "$work_root/mathlib-release-lake-manifest.json"

cp "$repo_root/MathlibSmoke.lean" "$mathlib_dir/MathlibSmoke.lean"
cp "$repo_root/InvalidTheorem.lean" "$mathlib_dir/InvalidTheorem.lean"
cd "$mathlib_dir"
record_gate 'lake-update' 'PASS' 'lake update'

# `lake update` is deliberately executed and evidenced above. Because dependency
# default branches can move after a Mathlib release, certification then restores
# that release's content-addressed lockfile and discards the transient checkouts.
cp "$work_root/mathlib-release-lake-manifest.json" "$mathlib_dir/lake-manifest.json"
if [[ "$mathlib_dir" != "$work_root/mathlib4" || ! -d "$mathlib_dir/.lake/packages" ]]; then
  echo 'refusing to clear an unexpected dependency directory' >&2
  exit 1
fi
rm -rf -- "$mathlib_dir/.lake/packages"
printf '%s  %s\n' "$MATHLIB_LAKE_MANIFEST_SHA256" "$mathlib_dir/lake-manifest.json" | sha256sum --check --strict | tee -a "$logs_dir/mathlib-release-manifest.log"
record_gate 'mathlib-cache' 'PASS' 'lake exe cache get'
git diff --exit-code -- lake-manifest.json lean-toolchain | tee "$logs_dir/release-lock-clean.log"
record_gate 'lake-build' 'PASS' 'lake build'
record_gate 'mathlib-smoke' 'PASS' 'lake env lean MathlibSmoke.lean'
record_gate 'invalid-theorem' 'FAIL' 'lake env lean InvalidTheorem.lean'

lake_build_exit="$(jq -s -r '.[] | select(.id == "lake-build") | .actualExitCode' "$gates_file")"
smoke_exit="$(jq -s -r '.[] | select(.id == "mathlib-smoke") | .actualExitCode' "$gates_file")"
[[ "$lake_build_exit" == '0' && "$smoke_exit" == '0' ]] || {
  echo 'Refusing to package: lake build and Mathlib smoke must both return exit code 0.' >&2
  exit 1
}

echo "Packaging Lean, Lake, Mathlib sources, dependencies, and compiled cache."
mkdir -p "$package_dir/portable-lean-toolchain"
cp -a "$lean_home" "$package_dir/portable-lean-toolchain/lean"
# Exclude only Mathlib's top-level clone history. Lake needs each locked
# dependency's .git metadata to validate it without attempting a network clone.
rsync -a --exclude='/.git' "$mathlib_dir/" "$package_dir/portable-lean-toolchain/mathlib/"
printf '%s\n' "$MATHLIB_COMMIT" > "$package_dir/portable-lean-toolchain/MATHLIB_COMMIT"
cp "$repo_root/scripts/verify-and-reconstruct.sh" "$package_dir/portable-lean-toolchain/verify-and-reconstruct.sh"
chmod +x "$package_dir/portable-lean-toolchain/verify-and-reconstruct.sh"

(
  cd "$package_dir/portable-lean-toolchain"
  find . -type f -print0 | sort -z | xargs -0 sha256sum
) > "$out_dir/workspace-tree-sha256sums.txt"
workspace_tree_sha256="$(sha256sum "$out_dir/workspace-tree-sha256sums.txt" | cut -d' ' -f1)"

archive="$out_dir/portable-lean-toolchain.tar.zst"
tar --sort=name --mtime='UTC 1970-01-01' --owner=0 --group=0 --numeric-owner \
  --use-compress-program='zstd -T0 -12' -cf "$archive" -C "$package_dir" portable-lean-toolchain
archive_sha256="$(sha256sum "$archive" | cut -d' ' -f1)"
archive_bytes="$(stat --format='%s' "$archive")"

split --bytes="$SPLIT_BYTES" --numeric-suffixes=0 --suffix-length=3 \
  "$archive" "$parts_dir/portable-lean-toolchain.tar.zst.part-"
mapfile -t generated_parts < <(find "$parts_dir" -maxdepth 1 -type f -name 'portable-lean-toolchain.tar.zst.part-*' | sort)
(( ${#generated_parts[@]} > 0 && ${#generated_parts[@]} <= 6 )) || {
  echo "connector transport supports 1-6 archive parts; generated ${#generated_parts[@]}" >&2
  exit 1
}
(
  cd "$parts_dir"
  sha256sum portable-lean-toolchain.tar.zst.part-* > part-sha256sums.txt
)

: > "$out_dir/parts.ndjson"
while IFS= read -r part; do
  bytes="$(stat --format='%s' "$part")"
  (( bytes > 0 && bytes < MAX_PART_BYTES )) || { echo "part is not smaller than 450 MiB: $part" >&2; exit 1; }
  jq -nc --arg filename "$(basename "$part")" --arg sha256 "$(sha256sum "$part" | cut -d' ' -f1)" --argjson bytes "$bytes" \
    '{filename:$filename,sha256:$sha256,bytes:$bytes}' >> "$out_dir/parts.ndjson"
done < <(find "$parts_dir" -maxdepth 1 -type f -name 'portable-lean-toolchain.tar.zst.part-*' | sort)

(
  cd "$parts_dir"
  sha256sum --check --strict part-sha256sums.txt
) | tee "$logs_dir/transport-verification.log"
reassembled_sha256="$(find "$parts_dir" -maxdepth 1 -type f -name 'portable-lean-toolchain.tar.zst.part-*' -print0 | sort -z | xargs -0 cat | sha256sum | cut -d' ' -f1)"
[[ "$reassembled_sha256" == "$archive_sha256" ]] || { echo 'reassembled archive SHA-256 mismatch' >&2; exit 1; }

docker build --tag lean-toolchain-offline-verifier \
  --file "$repo_root/scripts/offline-verifier.Dockerfile" "$repo_root" > "$logs_dir/docker-image.log" 2>&1
: > "$out_dir/offline.ndjson"
for number in 1 2; do
  reconstruction="$work_root/offline-$number"
  bash "$repo_root/scripts/verify-and-reconstruct.sh" "$parts_dir" "$reconstruction" > "$logs_dir/offline-$number-reconstruct.log" 2>&1
  (
    cd "$reconstruction/portable-lean-toolchain"
    find . -type f -print0 | sort -z | xargs -0 sha256sum
  ) > "$out_dir/offline-$number-tree-sha256sums.txt"
  tree_sha256="$(sha256sum "$out_dir/offline-$number-tree-sha256sums.txt" | cut -d' ' -f1)"
  [[ "$tree_sha256" == "$workspace_tree_sha256" ]] || { echo "offline-$number tree mismatch" >&2; exit 1; }

  set +e
  docker run --rm --network none -v "$reconstruction/portable-lean-toolchain:/portable" -w /portable/mathlib lean-toolchain-offline-verifier \
    bash -c 'git config --global --add safe.directory "*"; git -C .lake/packages/plausible remote get-url origin; export PATH=/portable/lean/bin:/usr/bin:/bin; lake build' > "$logs_dir/offline-$number-lake-build.log" 2>&1
  offline_build_exit=$?
  docker run --rm --network none -v "$reconstruction/portable-lean-toolchain:/portable" -w /portable/mathlib lean-toolchain-offline-verifier \
    bash -c 'git config --global --add safe.directory "*"; git -C .lake/packages/plausible remote get-url origin; export PATH=/portable/lean/bin:/usr/bin:/bin; lake env lean MathlibSmoke.lean' > "$logs_dir/offline-$number-smoke.log" 2>&1
  offline_smoke_exit=$?
  set -e
  cat "$logs_dir/offline-$number-lake-build.log"
  cat "$logs_dir/offline-$number-smoke.log"
  [[ $offline_build_exit -eq 0 && $offline_smoke_exit -eq 0 ]] || { echo "offline-$number execution failed" >&2; exit 1; }

  cat "$logs_dir/offline-$number-reconstruct.log" "$logs_dir/offline-$number-lake-build.log" "$logs_dir/offline-$number-smoke.log" > "$logs_dir/offline-$number-complete.log"
  jq -nc \
    --arg id "offline-$number" \
    --arg treeSha256 "$tree_sha256" \
    --arg logSha256 "$(sha256sum "$logs_dir/offline-$number-complete.log" | cut -d' ' -f1)" \
    --argjson lakeBuildExitCode "$offline_build_exit" \
    --argjson smokeExitCode "$offline_smoke_exit" \
    '{id:$id,networkMode:"none",treeSha256:$treeSha256,lakeBuildExitCode:$lakeBuildExitCode,smokeExitCode:$smokeExitCode,logSha256:$logSha256}' >> "$out_dir/offline.ndjson"
done

generated_at="$(date --utc +'%Y-%m-%dT%H:%M:%SZ')"
repository="${GITHUB_REPOSITORY:-local/Toolchain_factory}"
commit="${GITHUB_SHA:-$(git -C "$repo_root" rev-parse HEAD)}"
run_id="${GITHUB_RUN_ID:-local}"

jq -n \
  --arg generatedAt "$generated_at" --arg repository "$repository" --arg commit "$commit" --arg runId "$run_id" \
  --arg leanToolchain "$LEAN_TOOLCHAIN" --arg mathlibTag "$MATHLIB_TAG" --arg mathlibCommit "$MATHLIB_COMMIT" --arg mathlibLakeManifestSha256 "$MATHLIB_LAKE_MANIFEST_SHA256" \
  --arg releaseArtifact "$RELEASE_ARTIFACT" --arg releaseTarballSha256 "$RELEASE_SHA256" --argjson releaseTarballBytes "$RELEASE_BYTES" \
  --arg archiveFilename "$(basename "$archive")" --arg archiveSha256 "$archive_sha256" --arg workspaceTreeSha256 "$workspace_tree_sha256" --argjson archiveBytes "$archive_bytes" \
  --arg leanExecutableSha256 "$(sha256sum "$package_dir/portable-lean-toolchain/lean/bin/lean" | cut -d' ' -f1)" \
  --arg lakeExecutableSha256 "$(sha256sum "$package_dir/portable-lean-toolchain/lean/bin/lake" | cut -d' ' -f1)" \
  --slurpfile parts "$out_dir/parts.ndjson" --slurpfile gates "$gates_file" --slurpfile offline "$out_dir/offline.ndjson" \
  '{
    schemaVersion:"2.0.0", generatedAt:$generatedAt,
    source:{repository:$repository,commit:$commit,workflow:"build-portable-toolchain",runId:$runId,runnerImage:"ubuntu-24.04"},
    anchors:{leanToolchain:$leanToolchain,mathlibTag:$mathlibTag,mathlibCommit:$mathlibCommit,mathlibLakeManifestSha256:$mathlibLakeManifestSha256,releaseArtifact:$releaseArtifact,releaseTarballSha256:$releaseTarballSha256,releaseTarballBytes:$releaseTarballBytes,architecture:"linux-x86_64"},
    transport:{archiveFilename:$archiveFilename,archiveSha256:$archiveSha256,archiveBytes:$archiveBytes,workspaceTreeSha256:$workspaceTreeSha256,verificationExitCode:0,parts:$parts},
    execution:{leanExecutableSha256:$leanExecutableSha256,lakeExecutableSha256:$lakeExecutableSha256,gates:$gates},
    offlineReconstructions:$offline
  }' > "$out_dir/certification-evidence.json"

sha256sum "$out_dir/certification-evidence.json" > "$out_dir/certification-evidence.json.sha256"
jq '{schemaVersion,generatedAt,source,anchors,transport}' "$out_dir/certification-evidence.json" > "$out_dir/toolchain-manifest.json"
sha256sum "$out_dir/toolchain-manifest.json" > "$out_dir/toolchain-manifest.json.sha256"

{
  echo 'CERTIFICATION COMPLETE'
  echo "lake build exit code: $lake_build_exit"
  echo "lake env lean MathlibSmoke.lean exit code: $smoke_exit"
  echo "archive SHA-256: $archive_sha256"
  echo "workspace tree SHA-256: $workspace_tree_sha256"
  echo "parts: $(wc -l < "$out_dir/parts.ndjson")"
  echo 'offline reconstructions: 2 (Docker --network none)'
} | tee "$out_dir/verification-summary.log"

# Stage the index in a flat directory. GitHub's artifact action otherwise
# preserves the unrelated out/ and scripts/ source paths, which makes a
# connector download disagree with the reconstruction helper's layout.
transport_index_dir="$out_dir/transport-index"
mkdir -p "$transport_index_dir"
cp "$parts_dir/part-sha256sums.txt" \
  "$out_dir/toolchain-manifest.json" \
  "$out_dir/toolchain-manifest.json.sha256" \
  "$repo_root/scripts/download-actions-artifacts.sh" \
  "$repo_root/scripts/verify-and-reconstruct.sh" \
  "$transport_index_dir/"

rm -f "$archive"
