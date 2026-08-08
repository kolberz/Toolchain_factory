#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 PARTS_DIRECTORY DESTINATION" >&2
  exit 64
fi

parts_dir="$(cd "$1" && pwd)"
destination="$2"
checksums="$parts_dir/part-sha256sums.txt"

[[ -f "$checksums" ]] || { echo "missing $checksums" >&2; exit 65; }
[[ ! -e "$destination" ]] || { echo "destination already exists: $destination" >&2; exit 66; }

mapfile -t parts < <(find "$parts_dir" -maxdepth 1 -type f -name 'portable-lean-toolchain.tar.zst.part-*' -printf '%f\n' | sort)
[[ ${#parts[@]} -gt 0 ]] || { echo "no archive parts found" >&2; exit 67; }

(
  cd "$parts_dir"
  sha256sum --check --strict part-sha256sums.txt
)

for part in "${parts[@]}"; do
  bytes="$(stat --format='%s' "$parts_dir/$part")"
  (( bytes > 0 && bytes < 450 * 1024 * 1024 )) || {
    echo "part violates the <450 MiB transport bound: $part ($bytes bytes)" >&2
    exit 68
  }
done

mkdir -p "$destination"
for part in "${parts[@]}"; do
  printf '%s\0' "$parts_dir/$part"
done | xargs -0 cat | tar --use-compress-program=unzstd -xf - -C "$destination"

echo "reconstructed ${#parts[@]} verified parts into $destination"
