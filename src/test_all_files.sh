#!/bin/bash
set -eu

for f in *.v; do
  echo "Processing $f"
  ./find_all_deps.sh "$f" | ./validate_all_deps.sh
done