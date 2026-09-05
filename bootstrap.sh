#!/usr/bin/env bash
# One-time toolchain + dependency bootstrap.  Log: bootstrap.log
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
echo "[$(date +%T)] elan $(elan --version)"
elan toolchain install "$(cat lean-toolchain)" || true
echo "[$(date +%T)] lake update"; lake update
echo "[$(date +%T)] lake exe cache get"; lake exe cache get
echo "[$(date +%T)] lake build (stubs)"; lake build
echo "[$(date +%T)] BOOTSTRAP OK"
