#!/usr/bin/env bash
# Build leanload + the example fixtures, then run leanload on a binary.
# Default invocation: `leanload --debug build/main`.
# Override:           `./run.sh <leanload args>`
# Stdout+stderr is also captured to `run.log` (committed snapshot).
set -euxo pipefail
cd "$(dirname "$0")"
lake build leanload
make
[ $# -eq 0 ] && set -- --debug build/main
./.lake/build/bin/leanload "$@" 2>&1 | tee run.log
