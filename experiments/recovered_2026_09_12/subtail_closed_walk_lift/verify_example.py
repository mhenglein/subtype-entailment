#!/usr/bin/env python3
"""Check one explicit positive certificate, not search for an existential model."""
from pathlib import Path
import json
from closed_walk_lift import (
    evaluate_formula, example, validate_formula, witness_direct, witness_reversed,
)

ROOT = Path(__file__).resolve().parent


def main() -> None:
    with (ROOT / 'formula-example.json').open(encoding='utf-8') as handle:
        formula = json.load(handle)
    with (ROOT / 'witness-model.json').open(encoding='utf-8') as handle:
        certificate = json.load(handle)
    stats = validate_formula(formula)
    model = certificate['assignment']
    word = model['W']
    checks = {
        'serialized_boolean_formula_satisfied': evaluate_formula(formula, model),
        'original_direct_predicate': witness_direct(example(), word),
        'original_reversed_predicate': witness_reversed(example(), word),
    }
    if not all(checks.values()):
        raise SystemExit('Certificate verification failed: ' + json.dumps(checks))
    print(json.dumps({
        'word': word, 'checks': checks, 'formula': stats,
        'method': 'Explicit assignment evaluation; no SAT solver executed',
    }, indent=2))


if __name__ == '__main__':
    main()
