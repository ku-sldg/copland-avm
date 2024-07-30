#!/bin/bash
set -eu

TOOLS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

for f in *.v; do
  echo "Processing $f"
  $TOOLS_DIR/find_all_deps.sh "$f" | $TOOLS_DIR/validate_all_deps.sh
done