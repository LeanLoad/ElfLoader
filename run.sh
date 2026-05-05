#!/usr/bin/env bash
# Build leanload + the example fixtures, then run leanload on a binary.
# Default target: build/main.  Override: ./run.sh <elf> [args...]
set -euxo pipefail
cd "$(dirname "$0")"
lake build leanload
make
exec ./.lake/build/bin/leanload "${@:-build/main}"
