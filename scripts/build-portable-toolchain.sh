#!/usr/bin/env bash
set -euo pipefail

MAX_PART_BYTES=$((450 * 1024 * 1024))
SPLIT_BYTES=$((440 * 1024 * 1024))
MAX_PARTS=497

repo_root="${GITHUB_WORKSPACE:-$(pwd)}"
profiles_file="$repo_root/toolchain-profiles.json"
profile_id="${TOOLCHAIN_PROFILE:-lean-4.32.2}"
[[ -f "$profiles_file" ]] || { echo "missing canonical profile file: $profiles_file" >&2; exit 1; }
profile="$(jq -ce --arg id "$profile_id" '.profiles[$id] // error("unknown toolchain profile: " + $id)' "$profiles_file")"
[[ "$(jq -r '.profileId' <<< "$profile")" == "$profile_id" ]] || { echo 'profile identity mismatch' >&2; exit 1; }

LEAN_VERSION="$(jq -r '.leanVersion' <<< "$profile")"
LEAN_TOOLCHAIN="$(jq -r '.leanToolchain' <<< "$profile")"
MATHLIB_TAG="$(jq -r '.mathlibTag' <<< "$profile")"
MATHLIB_COMMIT="$(jq -r '.mathlibCommit' <<< "$profile")"
MATHLIB_LAKE_MANIFEST_SHA256="$(jq -r '.mathlibLakeManifestSha256' <<< "$profile")"
RELEASE_ARTIFACT="$(jq -r '.releaseArtifact' <<< "$profile")"
RELEASE_SHA256="$(jq -r '.releaseTarballSha256' <<< "$profile")"
RELEASE_BYTES="$(jq -r '.releaseTarballBytes' <<< "$profile")"

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
    --arg id "$id" --arg command "$command" --arg expectedOutcome "$expected" \
    --argjson actualExitCode "$exit_code" --arg logFile "logs/$id.log" \
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
export LEAN_SYSROOT="$lean_home"

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

# Capture the exact Lean search path from the known-good Lake environment before
# canonicalization, then rewrite build-machine roots into portable bundle tokens.
canonical_lean_path="$(lake env bash -c 'printf "%s" "${LEAN_PATH:-}"')"
[[ -n "$canonical_lean_path" ]] || { echo 'lake env produced an empty LEAN_PATH' >&2; exit 1; }
portable_lean_path="${canonical_lean_path//$lean_home/__PORTABLE_ROOT__\/lean}"
portable_lean_path="${portable_lean_path//$mathlib_dir/__PORTABLE_ROOT__\/mathlib}"
if [[ "$portable_lean_path" == *"$work_root"* ]]; then
  echo 'portable LEAN_PATH still contains build-machine work_root' >&2
  exit 1
fi
printf '%s\n' "$portable_lean_path" > "$out_dir/portable-lean-path.txt"

bash "$repo_root/scripts/canonicalize-dependency-git.sh" "$mathlib_dir" | tee "$logs_dir/dependency-git-canonicalization.log"

echo "Packaging Lean, Lake, Mathlib sources, dependencies, compiled cache, and portable runtime wrapper."
portable_root="$package_dir/portable-lean-toolchain"
mkdir -p "$portable_root"
cp -a "$lean_home" "$portable_root/lean"
rsync -a "$mathlib_dir/" "$portable_root/mathlib/"
printf '%s\n' "$MATHLIB_COMMIT" > "$portable_root/MATHLIB_COMMIT"
cp "$repo_root/scripts/verify-and-reconstruct.sh" "$portable_root/verify-and-reconstruct.sh"
chmod +x "$portable_root/verify-and-reconstruct.sh"

cat > "$portable_root/portable-lean-env" <<'PORTABLE_ENV'
#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
LEAN_BIN="$ROOT/lean/bin/lean"
LAKE_BIN="$ROOT/lean/bin/lake"

[[ -x "$LEAN_BIN" ]] || { echo "missing Lean executable: $LEAN_BIN" >&2; exit 69; }
[[ -x "$LAKE_BIN" ]] || { echo "missing Lake executable: $LAKE_BIN" >&2; exit 69; }

export LEAN_SYSROOT="$ROOT/lean"
export PATH="$ROOT/lean/bin:${PATH:-}"
export LD_LIBRARY_PATH="$ROOT/lean/lib/lean:$ROOT/lean/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
PORTABLE_LEAN_PATH='__PORTABLE_LEAN_PATH_VALUE__'
export LEAN_PATH="${PORTABLE_LEAN_PATH//__PORTABLE_ROOT__/$ROOT}"

if [[ $# -eq 0 ]]; then
  cat <<EOF
LEAN_SYSROOT=$LEAN_SYSROOT
LEAN_PATH=$LEAN_PATH
LEAN=$LEAN_BIN
LAKE=$LAKE_BIN
EOF
  exit 0
fi

case "$1" in
  lean)
    shift
    cd "$ROOT/mathlib"
    exec "$LEAN_BIN" "$@"
    ;;
  lake)
    shift
    cd "$ROOT/mathlib"
    exec "$LAKE_BIN" "$@"
    ;;
  env)
    shift
    cd "$ROOT/mathlib"
    exec env "$@"
    ;;
  *)
    cd "$ROOT/mathlib"
    exec "$@"
    ;;
esac
PORTABLE_ENV
python3 - "$portable_root/portable-lean-env" "$portable_lean_path" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
value = sys.argv[2]
text = p.read_text()
needle = "__PORTABLE_LEAN_PATH_VALUE__"
if needle not in text:
    raise SystemExit("portable wrapper placeholder missing")
p.write_text(text.replace(needle, value))
PY
chmod +x "$portable_root/portable-lean-env"

# Prove the bundle can execute without relying on Lean/Lake executable discovery.
# We intentionally strip the inherited PATH down to ordinary system tools and
# invoke the wrapper by absolute path. LEAN_SYSROOT/LEAN_PATH are supplied by it.
portable_smoke="$portable_root/mathlib/MathlibSmoke.lean"
[[ -f "$portable_smoke" ]]
record_gate 'portable-lean-version' 'PASS' "env -u LEAN_SYSROOT -u LEAN_PATH PATH=/usr/bin:/bin '$portable_root/portable-lean-env' lean --version"
record_gate 'portable-mathlib-smoke' 'PASS' "env -u LEAN_SYSROOT -u LEAN_PATH PATH=/usr/bin:/bin '$portable_root/portable-lean-env' lean MathlibSmoke.lean"

# A proof replay gate defaults to the existing smoke theorem, but callers may
# point PORTABLE_PROOF_FILE at any packaged .lean file before the build starts.
portable_proof_file="${PORTABLE_PROOF_FILE:-MathlibSmoke.lean}"
if [[ "$portable_proof_file" = /* || "$portable_proof_file" == *".."* ]]; then
  echo 'PORTABLE_PROOF_FILE must be a relative path inside packaged Mathlib' >&2
  exit 1
fi
[[ -f "$portable_root/mathlib/$portable_proof_file" ]] || {
  echo "portable proof file is not packaged: $portable_proof_file" >&2
  exit 1
}
record_gate 'portable-proof-replay' 'PASS' "env -u LEAN_SYSROOT -u LEAN_PATH PATH=/usr/bin:/bin '$portable_root/portable-lean-env' lean '$portable_proof_file'"

(
  cd "$portable_root"
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
(( ${#generated_parts[@]} > 0 && ${#generated_parts[@]} <= MAX_PARTS )) || {
  echo "connector transport supports 1-$MAX_PARTS archive parts; generated ${#generated_parts[@]}" >&2
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
part_set_sha256="$(sha256sum "$parts_dir/part-sha256sums.txt" | cut -d' ' -f1)"

jq -n \
  --arg profileId "$profile_id" --arg leanVersion "$LEAN_VERSION" --arg leanToolchain "$LEAN_TOOLCHAIN" \
  --arg mathlibCommit "$MATHLIB_COMMIT" --arg archiveSha256 "$archive_sha256" \
  --arg workspaceTreeSha256 "$workspace_tree_sha256" --arg partSetSha256 "$part_set_sha256" \
  --argjson archiveBytes "$archive_bytes" --slurpfile parts "$out_dir/parts.ndjson" \
  '{schemaVersion:"1.2.0",anchors:{profileId:$profileId,leanVersion:$leanVersion,leanToolchain:$leanToolchain,mathlibCommit:$mathlibCommit},portableRuntime:{wrapper:"portable-lean-env",explicitLeanSysroot:true,explicitLeanPath:true},transport:{archiveSha256:$archiveSha256,archiveBytes:$archiveBytes,workspaceTreeSha256:$workspaceTreeSha256,partSetSha256:$partSetSha256,parts:$parts}}' \
  > "$out_dir/reproducibility-fingerprint.json"

generated_at="$(date --utc +'%Y-%m-%dT%H:%M:%SZ')"
repository="${GITHUB_REPOSITORY:-local/Toolchain_factory}"
commit="${GITHUB_SHA:-$(git -C "$repo_root" rev-parse HEAD)}"
run_id="${GITHUB_RUN_ID:-local}"

jq -n \
  --arg generatedAt "$generated_at" --arg repository "$repository" --arg commit "$commit" --arg runId "$run_id" \
  --arg profileId "$profile_id" --arg leanVersion "$LEAN_VERSION" --arg leanToolchain "$LEAN_TOOLCHAIN" \
  --arg mathlibTag "$MATHLIB_TAG" --arg mathlibCommit "$MATHLIB_COMMIT" --arg mathlibLakeManifestSha256 "$MATHLIB_LAKE_MANIFEST_SHA256" \
  --arg releaseArtifact "$RELEASE_ARTIFACT" --arg releaseTarballSha256 "$RELEASE_SHA256" --argjson releaseTarballBytes "$RELEASE_BYTES" \
  --arg archiveFilename "$(basename "$archive")" --arg archiveSha256 "$archive_sha256" --arg workspaceTreeSha256 "$workspace_tree_sha256" --argjson archiveBytes "$archive_bytes" \
  --arg partSetSha256 "$part_set_sha256" --slurpfile parts "$out_dir/parts.ndjson" \
  '{schemaVersion:"3.2.0",generatedAt:$generatedAt,source:{repository:$repository,commit:$commit,workflow:"build-portable-toolchain",runId:$runId,runnerImage:"ubuntu-24.04",builderInstance:(env.BUILDER_INSTANCE // "local")},anchors:{profileId:$profileId,leanVersion:$leanVersion,leanToolchain:$leanToolchain,mathlibTag:$mathlibTag,mathlibCommit:$mathlibCommit,mathlibLakeManifestSha256:$mathlibLakeManifestSha256,releaseArtifact:$releaseArtifact,releaseTarballSha256:$releaseTarballSha256,releaseTarballBytes:$releaseTarballBytes,architecture:"linux-x86_64"},portableRuntime:{wrapper:"portable-lean-env",explicitLeanSysroot:true,explicitLeanPath:true,proofReplayFile:$ENV.PORTABLE_PROOF_FILE},transport:{archiveFilename:$archiveFilename,archiveSha256:$archiveSha256,archiveBytes:$archiveBytes,workspaceTreeSha256:$workspaceTreeSha256,partSetSha256:$partSetSha256,verificationExitCode:0,parts:$parts}}' \
  > "$out_dir/toolchain-manifest.json"
sha256sum "$out_dir/toolchain-manifest.json" > "$out_dir/toolchain-manifest.json.sha256"
cp "$out_dir/toolchain-manifest.json" "$out_dir/toolchain-manifest.json.sha256" "$parts_dir/"

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

  portable="$reconstruction/portable-lean-toolchain/portable-lean-env"
  set +e
  docker run --rm --network none -v "$reconstruction/portable-lean-toolchain:/portable" -w /portable/mathlib lean-toolchain-offline-verifier \
    bash -c 'git config --global --add safe.directory "*"; env -u LEAN_SYSROOT -u LEAN_PATH PATH=/usr/bin:/bin /portable/portable-lean-env lake build' > "$logs_dir/offline-$number-lake-build.log" 2>&1
  offline_build_exit=$?
  docker run --rm --network none -v "$reconstruction/portable-lean-toolchain:/portable" -w /portable/mathlib lean-toolchain-offline-verifier \
    bash -c 'env -u LEAN_SYSROOT -u LEAN_PATH PATH=/usr/bin:/bin /portable/portable-lean-env lean MathlibSmoke.lean' > "$logs_dir/offline-$number-mathlib-smoke.log" 2>&1
  offline_smoke_exit=$?
  set -e
  [[ $offline_build_exit -eq 0 && $offline_smoke_exit -eq 0 ]] || { echo "offline portable replay $number failed" >&2; exit 1; }
  jq -nc --argjson run "$number" --argjson lakeBuildExit "$offline_build_exit" --argjson mathlibSmokeExit "$offline_smoke_exit" \
    '{run:$run,lakeBuildExit:$lakeBuildExit,mathlibSmokeExit:$mathlibSmokeExit,portableRuntime:true}' >> "$out_dir/offline.ndjson"
done

echo "portable toolchain build and replay gates completed successfully"
