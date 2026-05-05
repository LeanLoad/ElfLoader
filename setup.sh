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
# Persist elan on PATH. elan-init.sh patches ~/.profile, ~/.bashrc,
# ~/.zshenv etc., but not fish — handle it ourselves.
if command -v fish >/dev/null 2>&1; then
  fish -c 'fish_add_path -m ~/.elan/bin/'
else
  export PATH="$HOME/.elan/bin:$PATH"
fi

# Submodules: gabi, musl, x86-64-ABI, …
git submodule update --init --recursive
