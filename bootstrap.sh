#!/usr/bin/env bash
# One-time toolchain + dependency bootstrap.
# Dependencies are resolved from the pinned lake-manifest.json;
# do not run `lake update`, which would move Mathlib off its pin.
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v elan >/dev/null 2>&1 && [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
echo "[$(date +%T)] elan $(elan --version)"
elan toolchain install "$(cat lean-toolchain)" || true
echo "[$(date +%T)] lake exe cache get"; lake exe cache get
echo "[$(date +%T)] lake build"; lake build
echo "[$(date +%T)] BOOTSTRAP OK"
