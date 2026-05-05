#!/usr/bin/env bash
# One-shot setup: system C toolchain + git submodules.
# Lean toolchain itself is handled by elan via lean-toolchain.
set -euxo pipefail
cd "$(dirname "$0")"

sudo apt-get update
sudo apt-get install -y build-essential

git submodule update --init --recursive
