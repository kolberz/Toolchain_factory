#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 RUN_ID DESTINATION" >&2
  exit 64
fi

command -v gh >/dev/null 2>&1 || { echo "GitHub CLI (gh) is required" >&2; exit 69; }

run_id="$1"
destination="$2"
repository="${TOOLCHAIN_FACTORY_REPOSITORY:-kolberz/Toolchain_factory}"

[[ "$run_id" =~ ^[0-9]+$ ]] || { echo "RUN_ID must be numeric" >&2; exit 64; }
[[ ! -e "$destination" ]] || { echo "destination already exists: $destination" >&2; exit 66; }

conclusion="$(gh run view "$run_id" --repo "$repository" --json conclusion --jq .conclusion)"
[[ "$conclusion" == "success" ]] || {
  echo "workflow run $run_id is not successful (conclusion: ${conclusion:-unknown})" >&2
  exit 65
}

mkdir -p "$destination"
gh run download "$run_id" --repo "$repository" \
  --name portable-lean-toolchain-transport-index --dir "$destination"

checksums="$destination/part-sha256sums.txt"
[[ -f "$checksums" ]] || { echo "transport index did not contain part-sha256sums.txt" >&2; exit 65; }

while read -r expected_sha filename; do
  [[ "$expected_sha" =~ ^[0-9a-f]{64}$ ]] || { echo "invalid SHA-256 for $filename" >&2; exit 65; }
  [[ "$filename" =~ ^portable-lean-toolchain\.tar\.zst\.part-([0-9]{3})$ ]] || {
    echo "invalid part filename in checksum index: $filename" >&2
    exit 65
  }
  suffix="${BASH_REMATCH[1]}"
  gh run download "$run_id" --repo "$repository" \
    --name "portable-lean-toolchain-part-$suffix" --dir "$destination"
done < "$checksums"

mkdir -p "$destination/verification"
gh run download "$run_id" --repo "$repository" \
  --name portable-lean-toolchain-verification --dir "$destination/verification"

(
  cd "$destination"
  sha256sum --check --strict part-sha256sums.txt
)

echo "downloaded and hash-verified run $run_id from $repository into $destination"
echo "reconstruct with: bash $destination/verify-and-reconstruct.sh $destination DESTINATION"
