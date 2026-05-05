#!/usr/bin/env bash
# Build the example fixtures (test goldens compare against them) and
# run the Lean test suite.
set -euxo pipefail
cd "$(dirname "$0")"
make
exec lake test
