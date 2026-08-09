#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 MATHLIB_DIRECTORY" >&2
  exit 64
fi

mathlib_dir="$(cd "$1" && pwd)"
packages_dir="$mathlib_dir/.lake/packages"
[[ -d "$packages_dir" ]] || { echo "missing dependency directory: $packages_dir" >&2; exit 65; }

canonicalized=0
while IFS= read -r -d '' git_dir; do
  repository="${git_dir%/.git}"
  head="$(git -C "$repository" rev-parse HEAD)"
  origin="$(git -C "$repository" remote get-url origin)"

  # Clone negotiation, reflogs, the working-tree stat cache, and the compressed
  # bytes reused from a server-generated pack vary between otherwise identical
  # builds. Repack and recompress every reachable object deterministically,
  # discard volatile transport state, and rebuild an index from the HEAD tree
  # without host inode/mtime data. `-f` disables delta reuse; `-F` separately
  # disables reuse of the existing compressed object representation.
  git -C "$repository" reflog expire --expire=all --all
  rm -rf -- "$git_dir/logs"
  rm -f -- "$git_dir/FETCH_HEAD" "$git_dir/ORIG_HEAD" "$git_dir/index" \
    "$git_dir/objects/info/commit-graph" "$git_dir/objects/pack/multi-pack-index"
  git -C "$repository" \
    -c pack.threads=1 \
    -c pack.compression=9 \
    -c core.compression=9 \
    -c pack.writeReverseIndex=false \
    -c repack.writeBitmaps=false \
    repack -a -d -f -F --window=0 --depth=0
  rm -f -- "$git_dir/objects/pack/"*.rev
  git -C "$repository" prune-packed

  temporary_index="$(mktemp)"
  rm -f -- "$temporary_index"
  GIT_INDEX_FILE="$temporary_index" git -C "$repository" read-tree HEAD
  mv -- "$temporary_index" "$git_dir/index"

  [[ "$(git -C "$repository" rev-parse HEAD)" == "$head" ]]
  [[ "$(git -C "$repository" remote get-url origin)" == "$origin" ]]
  canonicalized=$((canonicalized + 1))
done < <(find "$packages_dir" -mindepth 2 -maxdepth 2 -type d -name .git -print0 | sort -z)

(( canonicalized > 0 )) || { echo "no dependency Git repositories found" >&2; exit 66; }
echo "canonicalized deterministic Git metadata for $canonicalized locked dependencies"
