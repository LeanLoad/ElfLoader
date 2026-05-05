#!/usr/bin/env bash
# One-shot setup: system C toolchain, elan (Lean toolchain manager),
# and git submodules. The exact Lean version is pinned in
# `lean-toolchain` and elan installs it on first `lake` invocation.
set -euxo pipefail
cd "$(dirname "$0")"

# C toolchain.
sudo apt-get update
sudo apt-get install -y build-essential curl

# elan — installs to ~/.elan, adds shim at ~/.elan/bin/lean*.
# https://github.com/leanprover/elan
if ! command -v elan >/dev/null 2>&1; then
  curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
# Make this shell session see elan immediately.
. "$HOME/.elan/env" 2>/dev/null || export PATH="$HOME/.elan/bin:$PATH"

# Submodules: gabi, musl, x86-64-ABI, …
git submodule update --init --recursive
