#!/bin/sh
# Run a command on a remote Linux GPU machine against this working tree.
#   KEEL_GPU_HOST=user@host tools/gpu-remote.sh 'cargo build --release && ./tests/gpu.sh'
# The tree (tracked and new files, not target/) is copied to ~/keel-gpu.
# Set KEEL_GPU_WSL=1 when SSH lands in Windows and Linux is under WSL2.
set -eu
cd "$(dirname "$0")/.."
host=${KEEL_GPU_HOST:?set KEEL_GPU_HOST=user@host}
# Remote arguments carry no spaces or quotes: ssh joins them into one
# string, which Windows' shell would otherwise reinterpret.
run() { if [ "${KEEL_GPU_WSL:-}" = 1 ]; then ssh -o BatchMode=yes "$host" wsl --cd "~" -e "$@"; else ssh -o BatchMode=yes "$host" "$@"; fi; }
echo 'mkdir -p ~/keel-gpu' | run bash -s
git ls-files -co --exclude-standard | grep -v '^bench/parfor/rayon_bench/target/' | COPYFILE_DISABLE=1 tar --no-xattrs -czf - -T - 2>/dev/null | run tar xzf - -C keel-gpu
printf '[ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"\nexport PATH="$HOME/.local/bin:$PATH"\ncd ~/keel-gpu\n%s\n' "$*" | run bash -s
