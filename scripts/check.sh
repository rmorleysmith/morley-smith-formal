#!/usr/bin/env bash
# Build everything, then run Lean's comparator on every result.
# A result passes when its Solution proves exactly the Challenge's statements,
# using only propext, Classical.choice and Quot.sound, and every formalization.yaml
# matches the v0.4 schema.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
status=0
for cfg in MorleySmithFormal/*/comparator.json; do
  name=$(basename "$(dirname "$cfg")")
  if lake comparator --config="$cfg" 2>&1 | tail -1 | grep -q "Your solution is okay!"; then
    echo "PASS  $name"
  else
    echo "FAIL  $name"; status=1
  fi
done
python3 scripts/validate-yaml.py || status=1
exit $status
