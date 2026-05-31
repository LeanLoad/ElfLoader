#!/usr/bin/env bash
# Build elfloader + the example fixtures, then run elfloader on a binary.
# Default invocation: `elfloader --debug build/main`.
# Override:           `./run.sh <elfloader args>`
# Stdout+stderr is also captured to `run.log` (committed snapshot).
set -euxo pipefail
cd "$(dirname "$0")"
lake build elfloader
make
[ $# -eq 0 ] && set -- --debug build/main
./.lake/build/bin/elfloader "$@" 2>&1 | tee run.log
