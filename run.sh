#!/usr/bin/env bash
# Build leanload + the example fixtures, then run leanload on a binary.
# Default invocation: `leanload --debug build/main`.
# Override:           `./run.sh <leanload args>`
set -euxo pipefail
cd "$(dirname "$0")"
lake build leanload
make
[ $# -eq 0 ] && set -- --debug build/main
exec ./.lake/build/bin/leanload "$@"
