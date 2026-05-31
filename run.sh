#!/usr/bin/env bash
# Build elfloader + the example fixtures, then run elfloader on a binary.
# Default invocation: `elfloader --debug build/main`.
# Override:           `./run.sh <elfloader args>`
# Stdout+stderr is also captured to `run.log` (committed snapshot).
set -euxo pipefail
cd "$(dirname "$0")"
lake build elfloader
: "${THIRD_PARTY_DIR:=../third_party}"
if [ ! -x "$THIRD_PARTY_DIR/musl/configure" ]; then
  echo "missing musl source at $THIRD_PARTY_DIR/musl; run ../setup.sh from the LeanLoad umbrella checkout or set THIRD_PARTY_DIR" >&2
  exit 1
fi
export THIRD_PARTY_DIR
make
[ $# -eq 0 ] && set -- --debug build/main
./.lake/build/bin/elfloader "$@" 2>&1 | tee run.log
