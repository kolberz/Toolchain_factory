#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 PARTS_DIRECTORY DESTINATION" >&2
  exit 64
fi

parts_dir="$(cd "$1" && pwd)"
destination="$2"
checksums="$parts_dir/part-sha256sums.txt"
manifest="$parts_dir/toolchain-manifest.json"
manifest_checksum="$parts_dir/toolchain-manifest.json.sha256"

[[ -f "$checksums" ]] || { echo "missing $checksums" >&2; exit 65; }
[[ -f "$manifest" ]] || { echo "missing $manifest" >&2; exit 65; }
[[ -f "$manifest_checksum" ]] || { echo "missing $manifest_checksum" >&2; exit 65; }
[[ ! -e "$destination" ]] || { echo "destination already exists: $destination" >&2; exit 66; }
for command_name in jq sha256sum stat tar unzstd; do
  command -v "$command_name" >/dev/null 2>&1 || { echo "required command is missing: $command_name" >&2; exit 69; }
done

read -r expected_manifest_sha256 _ < "$manifest_checksum"
[[ "$expected_manifest_sha256" =~ ^[0-9a-f]{64}$ ]] || { echo 'invalid manifest SHA-256 sidecar' >&2; exit 65; }
actual_manifest_sha256="$(sha256sum "$manifest" | cut -d' ' -f1)"
[[ "$actual_manifest_sha256" == "$expected_manifest_sha256" ]] || { echo 'manifest SHA-256 mismatch' >&2; exit 65; }

mapfile -t checksum_lines < "$checksums"
(( ${#checksum_lines[@]} > 0 && ${#checksum_lines[@]} <= 497 )) || { echo 'checksum inventory must contain 1-497 parts' >&2; exit 67; }

declare -a parts=()
declare -A listed_names=()
for index in "${!checksum_lines[@]}"; do
  line="${checksum_lines[$index]}"
  if [[ ! "$line" =~ ^([0-9a-f]{64})\ \ (portable-lean-toolchain\.tar\.zst\.part-([0-9]{3}))$ ]]; then
    echo "invalid checksum inventory line: $line" >&2
    exit 65
  fi
  filename="${BASH_REMATCH[2]}"
  suffix="${BASH_REMATCH[3]}"
  expected_suffix="$(printf '%03d' "$index")"
  [[ "$suffix" == "$expected_suffix" ]] || { echo "part sequence is not contiguous at $filename" >&2; exit 67; }
  [[ -z "${listed_names[$filename]:-}" ]] || { echo "duplicate part in checksum inventory: $filename" >&2; exit 65; }
  listed_names[$filename]=1
  parts+=("$filename")
done

mapfile -t discovered_parts < <(find "$parts_dir" -maxdepth 1 -type f -name 'portable-lean-toolchain.tar.zst.part-*' -printf '%f\n' | sort)
[[ ${#discovered_parts[@]} -eq ${#parts[@]} ]] || { echo 'discovered part set differs from checksum inventory' >&2; exit 67; }
for index in "${!parts[@]}"; do
  [[ "${discovered_parts[$index]}" == "${parts[$index]}" ]] || { echo "unexpected or missing part: ${discovered_parts[$index]:-<missing>}" >&2; exit 67; }
done

(
  cd "$parts_dir"
  sha256sum --check --strict part-sha256sums.txt
)

manifest_part_count="$(jq -er '.transport.parts | length' "$manifest")"
[[ "$manifest_part_count" == "${#parts[@]}" ]] || { echo 'manifest part count differs from checksum inventory' >&2; exit 65; }

archive_bytes=0
for index in "${!parts[@]}"; do
  part="${parts[$index]}"
  bytes="$(stat --format='%s' "$parts_dir/$part")"
  (( bytes > 0 && bytes < 450 * 1024 * 1024 )) || {
    echo "part violates the <450 MiB transport bound: $part ($bytes bytes)" >&2
    exit 68
  }
  expected_hash="${checksum_lines[$index]%%  *}"
  manifest_name="$(jq -er --argjson index "$index" '.transport.parts[$index].filename' "$manifest")"
  manifest_hash="$(jq -er --argjson index "$index" '.transport.parts[$index].sha256' "$manifest")"
  manifest_bytes="$(jq -er --argjson index "$index" '.transport.parts[$index].bytes' "$manifest")"
  [[ "$manifest_name" == "$part" && "$manifest_hash" == "$expected_hash" && "$manifest_bytes" == "$bytes" ]] || {
    echo "manifest metadata mismatch for $part" >&2
    exit 65
  }
  archive_bytes=$((archive_bytes + bytes))
done

expected_archive_bytes="$(jq -er '.transport.archiveBytes' "$manifest")"
expected_archive_sha256="$(jq -er '.transport.archiveSha256 | select(test("^[0-9a-f]{64}$"))' "$manifest")"
[[ "$archive_bytes" == "$expected_archive_bytes" ]] || { echo 'reassembled archive byte count differs from manifest' >&2; exit 65; }
actual_archive_sha256="$({ for part in "${parts[@]}"; do cat -- "$parts_dir/$part"; done; } | sha256sum | cut -d' ' -f1)"
[[ "$actual_archive_sha256" == "$expected_archive_sha256" ]] || { echo 'reassembled archive SHA-256 differs from manifest' >&2; exit 65; }

mkdir -p "$destination"
for part in "${parts[@]}"; do
  printf '%s\0' "$parts_dir/$part"
done | xargs -0 cat | tar --use-compress-program=unzstd -xf - -C "$destination"

echo "reconstructed ${#parts[@]} manifest-verified parts into $destination"
echo "archive SHA-256: $actual_archive_sha256"
