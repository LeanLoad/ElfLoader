#!/usr/bin/env bash
# One-shot setup for the C toolchain, elan, and build dependencies.
# Lean is pinned by `lean-toolchain`; elan installs it on first `lake` run.
#
# Large reference/spec submodules are skipped by default. Run
# `git submodule update --init --recursive` if you need them.
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

# Build-dep submodules only (musl libc for the example fixtures).
# Matches what CI inits.
git submodule update --init third_party/musl
