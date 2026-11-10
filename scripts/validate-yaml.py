"""Check every MorleySmithFormal/*/formalization.yaml against the formalization.yaml v0.4 schema
and the extra rules Palomar applies to sources.

The schema is vendored from github.com/mathlib-initiative/formalization.yaml (schema/v0.4.schema.json).
Palomar's rules are from github.com/PalomarRegistry/PalomarPolicy (CONTRIBUTING.md, section 3).
Needs PyYAML and jsonschema.
"""
import json
import pathlib
import sys

import jsonschema
import yaml

PALOMAR_SOURCE_TYPES = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
SUBSTANTIVE = {"formalizes", "adapts", "independently-proves"}


def palomar_errors(data):
    """Palomar's source rules: allowed types, and exactly one declared origin."""
    errors = []
    sources = data.get("sources") or []
    for i, s in enumerate(sources):
        if "type" in s and s["type"] not in PALOMAR_SOURCE_TYPES:
            errors.append(f"sources[{i}].type '{s['type']}' is not one of {sorted(PALOMAR_SOURCE_TYPES)}")
    original = [s for s in sources if s.get("type") == "original-proof"]
    if original:
        if any(s.get("relationship") != "other" for s in original) or any(
            s.get("relationship") not in ("background", "other") for s in sources
        ):
            errors.append("an original-proof source needs relationship 'other', and every source 'background' or 'other'")
    elif not any(s.get("relationship") in SUBSTANTIVE for s in sources):
        errors.append("no source formalizes, adapts or independently-proves the result, and none is an original-proof")
    return errors


root = pathlib.Path(__file__).resolve().parent.parent
schema = json.loads((root / "scripts/schema/formalization-v0.4.schema.json").read_text())
validator = jsonschema.Draft7Validator(schema)
status = 0
for f in sorted(root.glob("MorleySmithFormal/*/formalization.yaml")):
    data = yaml.safe_load(f.read_text())
    errors = [f"{list(e.path)}: {e.message}" for e in validator.iter_errors(data)] + palomar_errors(data)
    print(("PASS  " if not errors else "FAIL  ") + f.parent.name + "  formalization.yaml")
    for e in errors:
        print(f"      {e}")
    status |= bool(errors)
sys.exit(status)
