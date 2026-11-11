#!/usr/bin/env bash
# Build the TauCeti track, then run Lean's comparator on each of its results.
set -euo pipefail
cd "$(dirname "$0")"
lake build
status=0
for cfg in TauTrack/*/comparator.json; do
  name=$(basename "$(dirname "$cfg")")
  if lake comparator --config="$cfg" 2>&1 | tail -1 | grep -q "Your solution is okay!"; then
    echo "PASS  $name"
  else
    echo "FAIL  $name"; status=1
  fi
done
exit $status
