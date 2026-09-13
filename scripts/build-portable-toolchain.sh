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
# Prevent consumers of the build-time environment from having to infer the
# installation root from the running executable.
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
cp "$repo_root/HatActivationLedgerV68_SEALED.lean" "$mathlib_dir/HatActivationLedgerV68_SEALED.lean"
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

# Optionally stage one standalone proof candidate from this repository into the
# packaged Mathlib root. This is deliberately opt-in so the canonical factory
# remains profile-driven when no consumer proof is selected.
portable_proof_file="${PORTABLE_PROOF_FILE:-MathlibSmoke.lean}"
if [[ "$portable_proof_file" = /* || "$portable_proof_file" == *".."* ]]; then
  echo 'PORTABLE_PROOF_FILE must be a relative path inside packaged Mathlib' >&2
  exit 1
fi
if [[ -n "${PORTABLE_PROOF_SOURCE:-}" ]]; then
  if [[ "$PORTABLE_PROOF_SOURCE" = /* || "$PORTABLE_PROOF_SOURCE" == *".."* ]]; then
    echo 'PORTABLE_PROOF_SOURCE must be a relative path inside the repository' >&2
    exit 1
  fi
  [[ -f "$repo_root/$PORTABLE_PROOF_SOURCE" ]] || {
    echo "portable proof source does not exist: $PORTABLE_PROOF_SOURCE" >&2
    exit 1
  }
  mkdir -p "$(dirname "$mathlib_dir/$portable_proof_file")"
  cp "$repo_root/$PORTABLE_PROOF_SOURCE" "$mathlib_dir/$portable_proof_file"
fi
[[ -f "$mathlib_dir/$portable_proof_file" ]] || {
  echo "portable proof file is not available in Mathlib: $portable_proof_file" >&2
  exit 1
}

# Capture the exact known-good Lake search path while the build environment is
# working, then replace ephemeral build roots with a stable bundle token.
canonical_lean_path="$(lake env bash -c 'printf "%s" "${LEAN_PATH:-}"')"
[[ -n "$canonical_lean_path" ]] || { echo 'lake env produced an empty LEAN_PATH' >&2; exit 1; }
portable_lean_path="$(python3 - "$canonical_lean_path" "$lean_home" "$mathlib_dir" "$work_root" <<'PY'
import sys
value, lean_home, mathlib_dir, work_root = sys.argv[1:]
value = value.replace(lean_home, "__PORTABLE_ROOT__/lean")
value = value.replace(mathlib_dir, "__PORTABLE_ROOT__/mathlib")
if work_root in value:
    raise SystemExit("portable LEAN_PATH still contains the build work root")
print(value, end="")
PY
)"
[[ "$portable_lean_path" == *"__PORTABLE_ROOT__"* ]] || {
  echo 'portable LEAN_PATH did not contain any relocatable bundle roots' >&2
  exit 1
}
printf '%s\n' "$portable_lean_path" > "$out_dir/portable-lean-path.txt"

bash "$repo_root/scripts/canonicalize-dependency-git.sh" "$mathlib_dir" | tee "$logs_dir/dependency-git-canonicalization.log"

echo "Packaging Lean, Lake, Mathlib sources, dependencies, compiled cache, and explicit portable runtime environment."
portable_root="$package_dir/portable-lean-toolchain"
mkdir -p "$portable_root"
cp -a "$lean_home" "$portable_root/lean"
# Keep the canonicalized top-level Mathlib Git metadata as well as every locked
# dependency's metadata. This lets an offline consumer mount packaged Mathlib as
# a dependency of another exact-pin Lake project without Lake attempting a clone.
rsync -a "$mathlib_dir/" "$portable_root/mathlib/"
printf '%s\n' "$MATHLIB_COMMIT" > "$portable_root/MATHLIB_COMMIT"
printf '%s\n' "$portable_lean_path" > "$portable_root/PORTABLE_LEAN_PATH"
cp "$repo_root/scripts/verify-and-reconstruct.sh" "$portable_root/verify-and-reconstruct.sh"
chmod +x "$portable_root/verify-and-reconstruct.sh"

cat > "$portable_root/portable-lean-env" <<'PORTABLE_ENV'
#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
LEAN_BIN="$ROOT/lean/bin/lean"
LAKE_BIN="$ROOT/lean/bin/lake"
PATH_FILE="$ROOT/PORTABLE_LEAN_PATH"

[[ -x "$LEAN_BIN" ]] || { echo "missing Lean executable: $LEAN_BIN" >&2; exit 69; }
[[ -x "$LAKE_BIN" ]] || { echo "missing Lake executable: $LAKE_BIN" >&2; exit 69; }
[[ -f "$PATH_FILE" ]] || { echo "missing portable Lean path file: $PATH_FILE" >&2; exit 69; }

portable_path="$(cat "$PATH_FILE")"
[[ "$portable_path" == *"__PORTABLE_ROOT__"* ]] || {
  echo 'portable Lean path is missing its relocatable root token' >&2
  exit 65
}

export LEAN_SYSROOT="$ROOT/lean"
export LEAN_PATH="${portable_path//__PORTABLE_ROOT__/$ROOT}"
export LEAN="$LEAN_BIN"
export LAKE="$LAKE_BIN"
export PATH="$ROOT/lean/bin:${PATH:-}"
export LD_LIBRARY_PATH="$ROOT/lean/lib/lean:$ROOT/lean/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

if [[ $# -eq 0 ]]; then
  cat <<EOF
LEAN_SYSROOT=$LEAN_SYSROOT
LEAN_PATH=$LEAN_PATH
LEAN=$LEAN
LAKE=$LAKE
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
chmod +x "$portable_root/portable-lean-env"

# First-class portable runtime gates. Inherited Lean path hints are removed and
# only ordinary system tools remain on PATH before the wrapper initializes its
# explicit sysroot/search-path environment.
record_gate 'portable-lean-version' 'PASS' \
  "env -u LEAN_SYSROOT -u LEAN_PATH -u LEAN -u LAKE PATH=/usr/bin:/bin '$portable_root/portable-lean-env' lean --version"
record_gate 'portable-mathlib-smoke' 'PASS' \
  "env -u LEAN_SYSROOT -u LEAN_PATH -u LEAN -u LAKE PATH=/usr/bin:/bin '$portable_root/portable-lean-env' lean MathlibSmoke.lean"
record_gate 'portable-proof-replay' 'PASS' \
  "env -u LEAN_SYSROOT -u LEAN_PATH -u LEAN -u LAKE PATH=/usr/bin:/bin '$portable_root/portable-lean-env' lean '$portable_proof_file'"

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
  --arg profileId "$profile_id" \
  --arg leanVersion "$LEAN_VERSION" \
  --arg leanToolchain "$LEAN_TOOLCHAIN" \
  --arg mathlibCommit "$MATHLIB_COMMIT" \
  --arg archiveSha256 "$archive_sha256" \
  --arg workspaceTreeSha256 "$workspace_tree_sha256" \
  --arg partSetSha256 "$part_set_sha256" \
  --argjson archiveBytes "$archive_bytes" \
  --slurpfile parts "$out_dir/parts.ndjson" \
  '{schemaVersion:"1.1.0",anchors:{profileId:$profileId,leanVersion:$leanVersion,leanToolchain:$leanToolchain,mathlibCommit:$mathlibCommit},transport:{archiveSha256:$archiveSha256,archiveBytes:$archiveBytes,workspaceTreeSha256:$workspaceTreeSha256,partSetSha256:$partSetSha256,parts:$parts}}' \
  > "$out_dir/reproducibility-fingerprint.json"

generated_at="$(date --utc +'%Y-%m-%dT%H:%M:%SZ')"
repository="${GITHUB_REPOSITORY:-local/Toolchain_factory}"
commit="${GITHUB_SHA:-$(git -C "$repo_root" rev-parse HEAD)}"
run_id="${GITHUB_RUN_ID:-local}"

jq -n \
  --arg generatedAt "$generated_at" --arg repository "$repository" --arg commit "$commit" --arg runId "$run_id" \
  --arg profileId "$profile_id" --arg leanVersion "$LEAN_VERSION" \
  --arg leanToolchain "$LEAN_TOOLCHAIN" --arg mathlibTag "$MATHLIB_TAG" --arg mathlibCommit "$MATHLIB_COMMIT" --arg mathlibLakeManifestSha256 "$MATHLIB_LAKE_MANIFEST_SHA256" \
  --arg releaseArtifact "$RELEASE_ARTIFACT" --arg releaseTarballSha256 "$RELEASE_SHA256" --argjson releaseTarballBytes "$RELEASE_BYTES" \
  --arg archiveFilename "$(basename "$archive")" --arg archiveSha256 "$archive_sha256" --arg workspaceTreeSha256 "$workspace_tree_sha256" --argjson archiveBytes "$archive_bytes" \
  --arg partSetSha256 "$part_set_sha256" --slurpfile parts "$out_dir/parts.ndjson" \
  '{
    schemaVersion:"3.1.0", generatedAt:$generatedAt,
    source:{repository:$repository,commit:$commit,workflow:"build-portable-toolchain",runId:$runId,runnerImage:"ubuntu-24.04",builderInstance:(env.BUILDER_INSTANCE // "local")},
    anchors:{profileId:$profileId,leanVersion:$leanVersion,leanToolchain:$leanToolchain,mathlibTag:$mathlibTag,mathlibCommit:$mathlibCommit,mathlibLakeManifestSha256:$mathlibLakeManifestSha256,releaseArtifact:$releaseArtifact,releaseTarballSha256:$releaseTarballSha256,releaseTarballBytes:$releaseTarballBytes,architecture:"linux-x86_64"},
    transport:{archiveFilename:$archiveFilename,archiveSha256:$archiveSha256,archiveBytes:$archiveBytes,workspaceTreeSha256:$workspaceTreeSha256,partSetSha256:$partSetSha256,verificationExitCode:0,parts:$parts}
  }' > "$out_dir/toolchain-manifest.json"
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

  set +e
  docker run --rm --network none -v "$reconstruction/portable-lean-toolchain:/portable" -w /portable/mathlib lean-toolchain-offline-verifier \
    bash -c 'git config --global --add safe.directory "*"; git -C .lake/packages/plausible remote get-url origin; env -u LEAN_SYSROOT -u LEAN_PATH -u LEAN -u LAKE PATH=/usr/bin:/bin /portable/portable-lean-env lake build' > "$logs_dir/offline-$number-lake-build.log" 2>&1
  offline_build_exit=$?
  docker run --rm --network none -v "$reconstruction/portable-lean-toolchain:/portable" -w /portable/mathlib lean-toolchain-offline-verifier \
    bash -c 'git config --global --add safe.directory "*"; git -C .lake/packages/plausible remote get-url origin; env -u LEAN_SYSROOT -u LEAN_PATH -u LEAN -u LAKE PATH=/usr/bin:/bin /portable/portable-lean-env lake env lean MathlibSmoke.lean' > "$logs_dir/offline-$number-smoke.log" 2>&1
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

jq -n \
  --arg generatedAt "$generated_at" --arg repository "$repository" --arg commit "$commit" --arg runId "$run_id" \
  --arg profileId "$profile_id" \
  --arg leanVersion "$LEAN_VERSION" \
  --arg leanToolchain "$LEAN_TOOLCHAIN" --arg mathlibTag "$MATHLIB_TAG" --arg mathlibCommit "$MATHLIB_COMMIT" --arg mathlibLakeManifestSha256 "$MATHLIB_LAKE_MANIFEST_SHA256" \
  --arg releaseArtifact "$RELEASE_ARTIFACT" --arg releaseTarballSha256 "$RELEASE_SHA256" --argjson releaseTarballBytes "$RELEASE_BYTES" \
  --arg archiveFilename "$(basename "$archive")" --arg archiveSha256 "$archive_sha256" --arg workspaceTreeSha256 "$workspace_tree_sha256" --argjson archiveBytes "$archive_bytes" \
  --arg partSetSha256 "$part_set_sha256" \
  --arg leanExecutableSha256 "$(sha256sum "$portable_root/lean/bin/lean" | cut -d' ' -f1)" \
  --arg lakeExecutableSha256 "$(sha256sum "$portable_root/lean/bin/lake" | cut -d' ' -f1)" \
  --slurpfile parts "$out_dir/parts.ndjson" --slurpfile gates "$gates_file" --slurpfile offline "$out_dir/offline.ndjson" \
  '{
    schemaVersion:"3.1.0", generatedAt:$generatedAt,
    source:{repository:$repository,commit:$commit,workflow:"build-portable-toolchain",runId:$runId,runnerImage:"ubuntu-24.04",builderInstance:(env.BUILDER_INSTANCE // "local")},
    anchors:{profileId:$profileId,leanVersion:$leanVersion,leanToolchain:$leanToolchain,mathlibTag:$mathlibTag,mathlibCommit:$mathlibCommit,mathlibLakeManifestSha256:$mathlibLakeManifestSha256,releaseArtifact:$releaseArtifact,releaseTarballSha256:$releaseTarballSha256,releaseTarballBytes:$releaseTarballBytes,architecture:"linux-x86_64"},
    transport:{archiveFilename:$archiveFilename,archiveSha256:$archiveSha256,archiveBytes:$archiveBytes,workspaceTreeSha256:$workspaceTreeSha256,partSetSha256:$partSetSha256,verificationExitCode:0,parts:$parts},
    execution:{leanExecutableSha256:$leanExecutableSha256,lakeExecutableSha256:$lakeExecutableSha256,gates:$gates},
    offlineReconstructions:$offline
  }' > "$out_dir/certification-evidence.json"

sha256sum "$out_dir/certification-evidence.json" > "$out_dir/certification-evidence.json.sha256"
jq '{schemaVersion,generatedAt,source,anchors,transport}' "$out_dir/certification-evidence.json" > "$out_dir/evidence-manifest.json"
cmp --silent "$out_dir/toolchain-manifest.json" "$out_dir/evidence-manifest.json" || { echo 'final evidence differs from the reconstruction manifest' >&2; exit 1; }
rm -f -- "$out_dir/evidence-manifest.json"

# The public reconstruction helper must reject stale or injected part files,
# even when every checksum-listed part remains valid.
printf -v unlisted_suffix '%03d' "${#generated_parts[@]}"
unlisted_part="$parts_dir/portable-lean-toolchain.tar.zst.part-$unlisted_suffix"
printf 'deliberately unlisted transport bytes\n' > "$unlisted_part"
set +e
bash "$repo_root/scripts/verify-and-reconstruct.sh" \
  "$parts_dir" "$work_root/unlisted-part-negative-control" \
  > "$logs_dir/unlisted-part-negative-control.log" 2>&1
unlisted_part_exit=$?
set -e
rm -f -- "$unlisted_part"
[[ $unlisted_part_exit -ne 0 ]] || { echo 'reconstruction helper accepted an unlisted part' >&2; exit 1; }
grep -F 'discovered part set differs from checksum inventory' "$logs_dir/unlisted-part-negative-control.log"

{
  echo 'BUILDER CERTIFICATION COMPLETE — CROSS-BUILDER COMPARISON PENDING'
  echo "toolchain profile: $profile_id"
  echo "lake build exit code: $lake_build_exit"
  echo "lake env lean MathlibSmoke.lean exit code: $smoke_exit"
  echo "portable proof replay file: $portable_proof_file"
  echo 'portable runtime gates: portable-lean-version, portable-mathlib-smoke, portable-proof-replay'
  echo "archive SHA-256: $archive_sha256"
  echo "workspace tree SHA-256: $workspace_tree_sha256"
  echo "parts: $(wc -l < "$out_dir/parts.ndjson")"
  echo 'offline reconstructions: 2 (Docker --network none, explicit portable runtime wrapper)'
  echo "reproducibility fingerprint SHA-256: $(sha256sum "$out_dir/reproducibility-fingerprint.json" | cut -d' ' -f1)"
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
