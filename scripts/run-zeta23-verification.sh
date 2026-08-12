#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C
export LANG=C

if [[ $# -ne 5 ]]; then
  echo 'usage: run-zeta23-verification.sh PORTABLE_DIR BASE_EVIDENCE ZETA_SOURCE OUTPUT_DIR TOOLS_DIR' >&2
  exit 64
fi

portable_dir="$(cd "$1" && pwd)"
base_evidence="$(realpath "$2")"
source_dir="$(cd "$3" && pwd)"
out_dir="$(mkdir -p "$4" && cd "$4" && pwd)"
tools_dir="$(cd "$5" && pwd)"
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
profile_file="$repo_root/zeta23-profile.json"
logs_dir="$out_dir/logs"
core_root="$out_dir/core-source"
fresh_root="$out_dir/fresh"
records_file="$out_dir/records.ndjson"
axiom_records_file="$out_dir/axiom-records.ndjson"
comparator_records_file="$out_dir/comparator-records.ndjson"
probe_records_file="$out_dir/probe-records.ndjson"

mkdir -p "$logs_dir" "$fresh_root"
: > "$records_file"
: > "$axiom_records_file"
: > "$comparator_records_file"
: > "$probe_records_file"

expected_profile="$(jq -r '.requiredToolchainProfile' "$profile_file")"
expected_commit="$(jq -r '.source.commit' "$profile_file")"
source_repository="$(jq -r '.source.repository' "$profile_file")"
base_profile="$(jq -r '.anchors.profileId' "$base_evidence")"
[[ "$base_profile" == "$expected_profile" ]] || { echo "base evidence profile is $base_profile, expected $expected_profile" >&2; exit 65; }
[[ "$(git -C "$source_dir" rev-parse HEAD)" == "$expected_commit" ]] || { echo 'Zeta23 source commit mismatch' >&2; exit 65; }
[[ -z "$(git -C "$source_dir" status --porcelain --untracked-files=no)" ]] || { echo 'Zeta23 tracked source is not clean' >&2; exit 65; }
[[ -x "$portable_dir/lean/bin/lean" && -x "$portable_dir/lean/bin/lake" ]] || { echo 'portable Lean/Lake binaries are missing' >&2; exit 65; }
[[ -d "$portable_dir/mathlib/.git" ]] || { echo 'portable Mathlib lacks the Git metadata required for offline dependency reuse' >&2; exit 65; }

export PATH="$portable_dir/lean/bin:/usr/local/bin:/usr/bin:/bin:$PATH"
export HOME="$out_dir/home"
mkdir -p "$HOME"
git config --global --add safe.directory '*'

record_command() {
  local destination="$1" id="$2" command="$3" workdir="$4"
  local log_file="$logs_dir/$id.log"
  printf '$ %s\n' "$command" > "$log_file"
  set +e
  (cd "$workdir" && bash -o pipefail -c "$command") >> "$log_file" 2>&1
  local exit_code=$?
  set -e
  cat "$log_file"
  jq -nc \
    --arg id "$id" --arg command "$command" --argjson exitCode "$exit_code" \
    --arg logFile "$id.log" --arg logSha256 "$(sha256sum "$log_file" | cut -d' ' -f1)" \
    '{id:$id,command:$command,exitCode:$exitCode,logFile:$logFile,logSha256:$logSha256}' >> "$destination"
  [[ $exit_code -eq 0 ]] || { echo "command $id failed" >&2; exit "$exit_code"; }
}

record_offline_command() {
  local destination="$1" id="$2" command="$3" workdir="$4"
  local log_file="$logs_dir/$id.log"
  printf '$ %s\n' "$command" > "$log_file"
  set +e
  docker run --rm --network none \
    --user "$(id -u):$(id -g)" \
    -e HOME="$HOME" \
    -e PATH="$portable_dir/lean/bin:/usr/local/bin:/usr/bin:/bin" \
    -v "$portable_dir:$portable_dir:ro" \
    -v "$workdir:$workdir" \
    -v "$HOME:$HOME" \
    -w "$workdir" \
    lean-toolchain-offline-verifier \
    bash -o pipefail -c "$command" >> "$log_file" 2>&1
  local exit_code=$?
  set -e
  cat "$log_file"
  jq -nc \
    --arg id "$id" --arg command "$command" --argjson exitCode "$exit_code" \
    --arg logFile "$id.log" --arg logSha256 "$(sha256sum "$log_file" | cut -d' ' -f1)" \
    '{id:$id,command:$command,exitCode:$exitCode,logFile:$logFile,logSha256:$logSha256}' >> "$destination"
  [[ $exit_code -eq 0 ]] || { echo "offline command $id failed" >&2; exit "$exit_code"; }
}

prepare_source() {
  local destination="$1"
  [[ ! -e "$destination" ]] || { echo "refusing existing source destination: $destination" >&2; exit 66; }
  git clone --no-local --no-hardlinks "$source_dir" "$destination" >/dev/null
  git -C "$destination" checkout --detach "$expected_commit" >/dev/null
  [[ "$(git -C "$destination" rev-parse HEAD)" == "$expected_commit" ]]
  [[ -z "$(git -C "$destination" status --porcelain --untracked-files=no)" ]]
  mkdir -p "$destination/.lake/packages"
  ln -s "$portable_dir/mathlib" "$destination/.lake/packages/mathlib"
  while IFS=$'\t' read -r name revision; do
    [[ "$name" =~ ^[A-Za-z0-9._-]+$ && "$name" != '.' && "$name" != '..' ]] || { echo "unsafe dependency name: $name" >&2; exit 67; }
    package="$portable_dir/mathlib/.lake/packages/$name"
    [[ -d "$package/.git" ]] || { echo "packaged dependency $name has no Git metadata" >&2; exit 67; }
    [[ "$(git -C "$package" rev-parse HEAD)" == "$revision" ]] || { echo "packaged dependency $name revision mismatch" >&2; exit 67; }
    ln -s "$package" "$destination/.lake/packages/$name"
  done < <(jq -r '.packages[] | select(.name != "mathlib") | [.name,.rev] | @tsv' "$destination/lake-manifest.json")
}

prepare_source "$core_root"
source_tree_inventory="$out_dir/source-tree-sha256sums.txt"
while IFS= read -r -d '' tracked_path; do
  [[ ! -L "$core_root/$tracked_path" ]] || { echo "tracked source symlink is not allowed: $tracked_path" >&2; exit 68; }
done < <(git -C "$core_root" ls-files -z)
(
  cd "$core_root"
  git ls-files -z | sort -z | xargs -0 sha256sum
) > "$source_tree_inventory"
source_tree_sha256="$(sha256sum "$source_tree_inventory" | cut -d' ' -f1)"

while IFS=$'\t' read -r path expected_hash expected_bytes; do
  actual_hash="$(sha256sum "$core_root/$path" | cut -d' ' -f1)"
  actual_bytes="$(stat --format='%s' "$core_root/$path")"
  [[ "$actual_hash" == "$expected_hash" && "$actual_bytes" == "$expected_bytes" ]] || { echo "pin file mismatch: $path" >&2; exit 68; }
done < <(jq -r '.pinFiles[] | [.path,.sha256,.bytes] | @tsv' "$profile_file")

record_offline_command "$records_file" 'lean-version' 'lean --version' "$core_root"
record_offline_command "$records_file" 'lake-build' 'lake build' "$core_root"
record_offline_command "$records_file" 'solution-build' 'lake build Solution Solution.Multiplicity Solution.XiPrime' "$core_root"
if grep -Eiq "declaration uses ['\"]sorry|sorryAx" "$logs_dir/lake-build.log" "$logs_dir/solution-build.log"; then
  echo 'forbidden sorry warning in Zeta23 or Solution build' >&2
  exit 69
fi
record_offline_command "$axiom_records_file" 'axioms-base' 'lake env lean comparator/PrintAxioms.lean' "$core_root"
record_offline_command "$axiom_records_file" 'axioms-multiplicity' 'lake env lean comparator/PrintAxioms/Multiplicity.lean' "$core_root"
record_offline_command "$axiom_records_file" 'axioms-xiprime' 'lake env lean comparator/PrintAxioms/XiPrime.lean' "$core_root"
record_offline_command "$axiom_records_file" 'axioms-pair-ceiling' 'lake env lean comparator/PrintAxioms/PairCeiling.lean' "$core_root"

comparator_binary="$tools_dir/comparator/.lake/build/bin/comparator"
lean4export_binary="$tools_dir/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
landrun_binary="$tools_dir/bin/landrun"
nanoda_binary="$tools_dir/nanoda/target/release/nanoda_bin"
for binary in "$comparator_binary" "$lean4export_binary" "$landrun_binary" "$nanoda_binary"; do
  [[ -x "$binary" ]] || { echo "required verifier binary is missing: $binary" >&2; exit 70; }
done

pins_match=true
while IFS=$'\t' read -r name expected_pin; do
  case "$name" in
    comparator) checkout="$tools_dir/comparator" ;;
    lean4export) checkout="$tools_dir/comparator/.lake/packages/lean4export" ;;
    landrun) checkout="$tools_dir/landrun" ;;
    nanoda) checkout="$tools_dir/nanoda" ;;
    *) echo "unknown verifier tool: $name" >&2; exit 70 ;;
  esac
  [[ "$(git -C "$checkout" rev-parse HEAD)" == "$expected_pin" ]] || pins_match=false
  [[ -z "$(git -C "$checkout" status --porcelain --untracked-files=no)" ]] || pins_match=false
done < <(jq -r '.comparator.pins | to_entries[] | [.key,.value] | @tsv' "$profile_file")
[[ "$pins_match" == true ]] || { echo 'verifier source pin mismatch' >&2; exit 70; }

landrun_probe="$fresh_root/landrun-probe"
mkdir -p "$landrun_probe/allowed"
probe_command="set -e; printf allowed > '$landrun_probe/allowed/ok'; if printf denied > '$landrun_probe/denied'; then exit 71; fi; test -f '$landrun_probe/allowed/ok'; test ! -e '$landrun_probe/denied'; echo LANDRUN_PROBE_PASS"
record_command "$probe_records_file" 'landrun-enforcement' "'$landrun_binary' --rox / --rwx '$landrun_probe/allowed' /usr/bin/bash -c \"$probe_command\"" "$fresh_root"
record_command "$probe_records_file" 'systemd-user-scope' "systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pipe --wait --quiet bash -c 'echo SYSTEMD_USER_SCOPE_PASS'" "$fresh_root"

for id in base multiplicity xiprime; do
  config_path="$(jq -r --arg id "$id" '.comparator.configs[] | select(.id == $id) | .path' "$profile_file")"
  workspace="$fresh_root/$id"
  prepare_source "$workspace"
  preexisting=0
  if [[ -d "$workspace/.lake/build" ]]; then
    preexisting="$(find "$workspace/.lake/build" -type f \( -name 'Solution.olean' -o -path '*/Solution/*.olean' \) | wc -l)"
  fi
  [[ "$preexisting" == 0 ]] || { echo "fresh comparator workspace $id already contains Solution artifacts" >&2; exit 72; }
  log_file="$logs_dir/comparator-$id.log"
  comparator_command="lake env '$comparator_binary' '$config_path'"
  printf '$ %s\n' "$comparator_command" > "$log_file"
  set +e
  (
    cd "$workspace"
    export COMPARATOR_LANDRUN="$landrun_binary"
    export COMPARATOR_LEAN4EXPORT="$lean4export_binary"
    export COMPARATOR_NANODA="$nanoda_binary"
    systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pipe --wait --quiet \
      -E PATH="$PATH" \
      -E HOME="$HOME" \
      -E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
      -E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" \
      -E COMPARATOR_NANODA="$COMPARATOR_NANODA" \
      --working-directory "$workspace" -- \
      bash -c "$comparator_command"
  ) >> "$log_file" 2>&1
  exit_code=$?
  set -e
  cat "$log_file"
  jq -nc \
    --arg id "$id" --arg configPath "$config_path" --argjson exitCode "$exit_code" \
    --argjson preexistingSolutionArtifactCount "$preexisting" \
    --arg sourceTreeSha256 "$source_tree_sha256" \
    --arg logFile "comparator-$id.log" --arg logSha256 "$(sha256sum "$log_file" | cut -d' ' -f1)" \
    '{id:$id,configPath:$configPath,exitCode:$exitCode,preexistingSolutionArtifactCount:$preexistingSolutionArtifactCount,sourceTreeSha256:$sourceTreeSha256,landrunMode:"real",systemdUserScope:true,nanodaEnabled:true,logFile:$logFile,logSha256:$logSha256}' \
    >> "$comparator_records_file"
  [[ $exit_code -eq 0 ]] || { echo "comparator $id failed" >&2; exit "$exit_code"; }
  grep -F "$(jq -r '.comparator.successMessage' "$profile_file")" "$log_file"
done

base_evidence_sha256="$(sha256sum "$base_evidence" | cut -d' ' -f1)"
generated_at="$(date --utc +'%Y-%m-%dT%H:%M:%SZ')"
jq -n \
  --arg generatedAt "$generated_at" --arg profileId "$(jq -r '.profileId' "$profile_file")" \
  --arg repository "$source_repository" --arg commit "$expected_commit" --arg treeSha256 "$source_tree_sha256" \
  --arg baseEvidenceSha256 "$base_evidence_sha256" --arg toolchainProfile "$expected_profile" \
  --arg factoryRepository "${GITHUB_REPOSITORY:-}" --arg factoryCommit "${GITHUB_SHA:-}" --arg factoryRunId "${GITHUB_RUN_ID:-}" \
  --arg leanSha256 "$(sha256sum "$portable_dir/lean/bin/lean" | cut -d' ' -f1)" \
  --arg lakeSha256 "$(sha256sum "$portable_dir/lean/bin/lake" | cut -d' ' -f1)" \
  --arg comparatorPin "$(jq -r '.comparator.pins.comparator' "$profile_file")" \
  --arg lean4exportPin "$(jq -r '.comparator.pins.lean4export' "$profile_file")" \
  --arg landrunPin "$(jq -r '.comparator.pins.landrun' "$profile_file")" \
  --arg nanodaPin "$(jq -r '.comparator.pins.nanoda' "$profile_file")" \
  --arg comparatorSha256 "$(sha256sum "$comparator_binary" | cut -d' ' -f1)" \
  --arg lean4exportSha256 "$(sha256sum "$lean4export_binary" | cut -d' ' -f1)" \
  --arg landrunSha256 "$(sha256sum "$landrun_binary" | cut -d' ' -f1)" \
  --arg nanodaSha256 "$(sha256sum "$nanoda_binary" | cut -d' ' -f1)" \
  --slurpfile commands "$records_file" --slurpfile axioms "$axiom_records_file" \
  --slurpfile reconstruction "$out_dir/reconstruction-record.json" \
  --slurpfile probes "$probe_records_file" --slurpfile comparators "$comparator_records_file" \
  '{schemaVersion:"1.0.0",generatedAt:$generatedAt,profileId:$profileId,
    source:{repository:$repository,commit:$commit,treeSha256:$treeSha256},
    toolchain:{profileId:$toolchainProfile,baseEvidenceSha256:$baseEvidenceSha256,factory:{repository:$factoryRepository,commit:$factoryCommit,runId:$factoryRunId},reconstruction:$reconstruction[0],networkMode:"none",binaries:{lean:{sha256:$leanSha256},lake:{sha256:$lakeSha256}},authentication:[]},
    core:{commands:$commands},axioms:{commands:$axioms},sandbox:{probes:$probes},
    comparatorTooling:{pins:{comparator:$comparatorPin,lean4export:$lean4exportPin,landrun:$landrunPin,nanoda:$nanodaPin},binaries:{comparator:{sha256:$comparatorSha256},lean4export:{sha256:$lean4exportSha256},landrun:{sha256:$landrunSha256},nanoda:{sha256:$nanodaSha256}}},
    comparators:$comparators}' > "$out_dir/zeta23-evidence.preliminary.json"

echo 'Zeta23 execution complete; workflow authentication records must be inserted before final evaluation.'
