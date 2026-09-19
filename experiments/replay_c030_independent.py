#!/usr/bin/env python3
"""Replay the independent C030 review without rewriting tracked result files.

Standard library only. This is a bounded corpus with exact regular-language
checks, not a Lean proof. The separate finite mutation fixture deliberately
violates terminality; it is not a counterexample to C030.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import tempfile
from pathlib import Path

import check_c030_independent as checker

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RECORD = ROOT / 'results/c030-independent-review.json'
SUITES = (
    ('fixtures', 0, 'fixtures.json'),
    ('k1', 4, 'exhaustive_k1.json'),
    ('k2', 3, 'exhaustive_k2.json'),
    ('random', 5, 'random_k3_k6.json'),
)


def semantic_result(record: dict) -> dict:
    return {key: value for key, value in record.items() if key != 'elapsed_seconds'}


def terminality_countermodel() -> dict:
    """Validate the two-state out-of-scope example using finite sets, not NFAs."""
    instance = checker.Instance(((1, -1), (-1, -1)), frozenset({0}))
    word = '0'
    valuation = ({'', '0'}, {''}, set(), {''}, set())
    expected_clauses = (
        ('denial', 4), ('upper', 0, 1, 4),
        ('upper', 1, 4, 4), ('lower', 4, 4, 3),
    )
    clauses = checker.normalized_constraints(instance)
    if clauses != expected_clauses:
        raise AssertionError(('unexpected mutation constraints', clauses))
    failures = []
    for q, nodes in enumerate(valuation):
        if any(w[:i] not in nodes for w in nodes for i in range(len(w) + 1)):
            failures.append(('not_prefix_closed', q))
    for clause in clauses:
        tag, *args = clause
        if tag == 'denial':
            good = not valuation[args[0]]
        elif tag == 'leq':
            good = valuation[args[0]] <= valuation[args[1]]
        else:
            if tag == 'upper':
                q, left, right = args
            elif tag == 'lower':
                left, right, q = args
            else:
                raise ValueError(clause)
            product = {''} | {'0' + w for w in valuation[left]} | {
                '1' + w for w in valuation[right]}
            good = valuation[q] <= product if tag == 'upper' else product <= valuation[q]
        if not good:
            failures.append(clause)
    witness = checker.direct_witness(instance, word)
    separates = word in valuation[0] and word not in valuation[2]
    if failures or witness or not separates:
        raise AssertionError(('terminality countermodel', failures, witness, separates))
    return {
        'scope': 'Counterexample only after dropping the required terminal-final hypothesis',
        'delta': [[1, -1], [-1, -1]], 'start': 0, 'final': [0],
        'flags': [], 'bad': [], 'word': word, 'witness': witness,
        'separates_in_constructed_system': separates,
        'finite_product_address_sets': dict(zip(
            ('a0', 'a1', 'v0', 'v1', 'b'), (sorted(nodes) for nodes in valuation))),
        'exact_constraint_validation_errors': failures,
    }


def main() -> None:
    if not __debug__:
        raise SystemExit('Run without -O: the preserved checker uses assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', type=Path, default=DEFAULT_RECORD)
    parser.add_argument('--output', type=Path, required=True,
                        help='Scratch output path; the tracked record is never overwritten.')
    parser.add_argument('--timeout', type=float, default=120,
                        help='Maximum seconds for each suite subprocess (default: 120).')
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error('--timeout must be positive')
    if args.output.resolve() in {args.record.resolve(), DEFAULT_RECORD.resolve()}:
        parser.error('--output must not replace the tracked or supplied baseline record')
    baseline = json.loads(args.record.read_text())
    source_path = Path(checker.__file__)
    source_hash = hashlib.sha256(source_path.read_bytes()).hexdigest()
    if source_hash != baseline['checker_sha256']:
        raise AssertionError('Checker bytes differ from the reviewed version')
    archived = baseline['archived_results']
    runs = {}
    environment = dict(os.environ, PYTHONOPTIMIZE='0', PYTHONDONTWRITEBYTECODE='1')
    with tempfile.TemporaryDirectory(prefix='c030-independent-') as scratch:
        for suite, length, filename in SUITES:
            output = Path(scratch) / filename
            command = [sys.executable, str(source_path), '--suite', suite,
                       '--length', str(length), '--output', str(output)]
            subprocess.run(command, check=True, capture_output=True, text=True,
                           timeout=args.timeout, env=environment)
            actual = json.loads(output.read_text())
            if semantic_result(actual) != semantic_result(archived[filename]):
                raise AssertionError(('semantic replay mismatch', suite, actual))
            runs[filename] = actual
    mutation = terminality_countermodel()
    if mutation != archived['terminality_required.json']:
        raise AssertionError('Terminality countermodel differs from archived result')
    totals = {key: sum(run['counts'][key] for run in runs.values())
              for key in next(iter(runs.values()))['counts']}
    summary = archived['summary.json']
    for key, old_key in (
        ('instances', 'total_input_occurrences'), ('words', 'total_query_words'),
        ('positive_words', 'positive_query_words'),
        ('exact_satisfiability_models', 'total_exact_satisfiability_models'),
    ):
        if totals[key] != summary[old_key]:
            raise AssertionError(('aggregate mismatch', key, totals[key], summary[old_key]))
    result = {
        'status': 'PASS', 'checker_sha256': source_hash,
        'inspected_source_revision': checker.REVISION,
        'environment': {'python': platform.python_version(),
                        'system': platform.system(), 'machine': platform.machine(),
                        'suite_timeout_seconds': args.timeout,
                        'explicit_memory_limit': None, 'random_seed': 2026091930},
        'counts': totals,
        'semantic_replay_matches_archived_results': True,
        'terminality_countermodel': mutation,
        'suite_elapsed_seconds': {name: record['elapsed_seconds']
                                  for name, record in runs.items()},
        'not_run': summary['not_run'] + ['Repository-wide navigation/index/CI checks'],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
