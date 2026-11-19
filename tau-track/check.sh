#!/usr/bin/env bash
# Build the TauCeti track, then run Lean's comparator on each of its results.
set -euo pipefail
cd "$(dirname "$0")"
lake build
status=0
for cfg in TauTrack/*/comparator.json; do
  name=$(basename "$(dirname "$cfg")")
  # A result whose kernel replay does not fit a standard CI runner carries a CI-SKIP file
  # saying why; check it locally with `lake comparator --config=<its comparator.json>`.
  if [ -f "$(dirname "$cfg")/CI-SKIP" ]; then
    echo "SKIP  $name  ($(head -1 "$(dirname "$cfg")/CI-SKIP"))"
    continue
  fi
  if lake comparator --config="$cfg" 2>&1 | tail -1 | grep -q "Your solution is okay!"; then
    echo "PASS  $name"
  else
    echo "FAIL  $name"; status=1
  fi
done
exit $status
