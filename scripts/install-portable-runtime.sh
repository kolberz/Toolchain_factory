#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 PORTABLE_ROOT REPOSITORY_ROOT" >&2
  exit 64
fi

portable_root="$(cd "$1" && pwd)"
repo_root="$(cd "$2" && pwd)"

[[ -x "$portable_root/lean/bin/lean" ]] || { echo 'portable Lean binary is missing' >&2; exit 69; }
[[ -x "$portable_root/lean/bin/lake" ]] || { echo 'portable Lake binary is missing' >&2; exit 69; }
[[ -f "$portable_root/PORTABLE_LEAN_PATH" ]] || { echo 'PORTABLE_LEAN_PATH is missing' >&2; exit 69; }

mkdir -p "$portable_root/lib" "$portable_root/runtime-src"
cp "$repo_root/scripts/lean-exepath-shim.c" "$portable_root/runtime-src/lean-exepath-shim.c"
cp "$repo_root/scripts/no-readlink-exec.c" "$portable_root/runtime-src/proc-exe-deny-shim.c"
cp "$repo_root/scripts/install-portable-runtime.sh" "$portable_root/runtime-src/install-portable-runtime.sh"

cc -std=c11 -O2 -Wall -Wextra -Werror -fPIC -shared -Wl,-z,relro,-z,now \
  -o "$portable_root/lib/lean-exepath-shim.so" \
  "$portable_root/runtime-src/lean-exepath-shim.c" -ldl

cc -std=c11 -O2 -Wall -Wextra -Werror -fPIC -shared -Wl,-z,relro,-z,now \
  -o "$portable_root/lib/proc-exe-deny-shim.so" \
  "$portable_root/runtime-src/proc-exe-deny-shim.c" -ldl

cat > "$portable_root/portable-lean-env" <<'PORTABLE_ENV'
#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
LEAN_BIN="$ROOT/lean/bin/lean"
LAKE_BIN="$ROOT/lean/bin/lake"
PATH_FILE="$ROOT/PORTABLE_LEAN_PATH"
EXEPATH_SHIM="$ROOT/lib/lean-exepath-shim.so"

[[ -x "$LEAN_BIN" ]] || { echo "missing Lean executable: $LEAN_BIN" >&2; exit 69; }
[[ -x "$LAKE_BIN" ]] || { echo "missing Lake executable: $LAKE_BIN" >&2; exit 69; }
[[ -f "$PATH_FILE" ]] || { echo "missing portable Lean path file: $PATH_FILE" >&2; exit 69; }
[[ -r "$EXEPATH_SHIM" ]] || { echo "missing executable-path shim: $EXEPATH_SHIM" >&2; exit 69; }

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
# Lean's Linux IO.appPath reads /proc/<pid>/exe during search-path startup.
# Interpose only that self-executable readlink and answer it from AT_EXECFN.
# Any pre-existing preload (including the certification denial adversary) comes
# after this compatibility shim, so only the intended self lookup is repaired.
export LD_PRELOAD="$EXEPATH_SHIM${LD_PRELOAD:+:$LD_PRELOAD}"

if [[ $# -eq 0 ]]; then
  cat <<EOF
LEAN_SYSROOT=$LEAN_SYSROOT
LEAN_PATH=$LEAN_PATH
LEAN=$LEAN
LAKE=$LAKE
LD_PRELOAD=$LD_PRELOAD
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
