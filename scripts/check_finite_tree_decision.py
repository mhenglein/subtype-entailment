#!/usr/bin/env python3
"""Audit the unconditional Lean finite-tree decision and its actual runtime.

The all-input theorem supplies correctness. Native comparisons with an
independent predecessor-saturation oracle check source emission and execution.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import re
import subprocess
import sys

from check_regular_certificate import command
from check_finite_tree_reduction import cli_cases
import regular_countermodel as regular
import subtail

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from experiments.check_finite_trees import threshold_hot

MODULES = ('PopAcyclic', 'FiniteTreeDecision')
DECL = re.compile(r'^(private\s+)?(theorem|def|abbrev|inductive|structure)\s+(\w+)', re.M)
SEED = 5807


def audit(directory):
    expected, private = {}, []
    for module in MODULES:
        source = (ROOT / 'lean/Subtail' / (module + '.lean')).read_text()
        if re.search(r'\b(sorry|sorryAx|native_decide|implemented_by)\b|^\s*(axiom|opaque|noncomputable|unsafe)\s', source, re.M):
            raise RuntimeError('Unexpected trusted or incomplete declaration: ' + module)
        for visibility, kind, name in DECL.findall(source):
            full = 'Subtail.' + module + '.' + name
            expected[full] = kind
            if visibility:
                if kind != 'theorem':
                    raise RuntimeError('Hidden runtime declaration: ' + full)
                private.append(full)
    required = {'Subtail.PopAcyclic.pop_trace',
                'Subtail.PopAcyclic.pop_length_lt_of_no_nonempty_loop'} | {
        'Subtail.FiniteTreeDecision.' + name for name in (
            'growthCheck', 'growthCheck_correct', 'growthCheck_false_bound',
            'growthCheck_true_noFiniteModel', 'run', 'run_growth_noFiniteExprModel',
            'entailsCheck', 'entailsCheck_correct')}
    if not required <= expected.keys():
        raise RuntimeError('Missing critical declarations')
    source = 'import Lean\n' + ''.join('import Subtail.' + m + '\n' for m in MODULES)
    source += ''.join('#print axioms ' + n + '\n' for n in expected if n not in private)
    # Resolve private names in the imported environment, rather than auditing
    # a copied proof or relying on Lean's internal numeric name allocation.
    for name in private:
        source += f'''open Lean Elab Command in
run_cmd do
  let names := (← getEnv).constants.toList.filterMap fun (n, _) =>
    if privateToUserName? n == some `{name} then some n else none
  unless names.length == 1 do throwError "Missing or ambiguous private declaration"
  for n in names do
    let axioms ← collectAxioms n
    logInfo m!"'{name}' depends on axioms: {{axioms}}"
'''
    file = directory / 'Axioms.lean'
    file.write_text(source)
    output = command(['lake', 'env', 'lean', str(file)])
    rows = re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^]]*)\])", output)
    if len(rows) != len(expected) or {n for n, _, _ in rows} != expected.keys():
        raise RuntimeError('Incomplete dependency report: ' + output)
    reports = {}
    for name, _, raw in rows:
        used = {a.strip() for a in raw.split(',') if a.strip()}
        allowed = {'propext', 'Quot.sound'} | ({'Classical.choice'} if expected[name] == 'theorem' else set())
        if not used <= allowed:
            raise RuntimeError('Unexpected dependencies: ' + name + ' ' + repr(used))
        reports[name] = {'kind': expected[name], 'private': name in private, 'axioms': sorted(used)}
    return reports


def systems():
    def make(n, eps=(), push=(), pop=()):
        return regular.System(n, set(eps), set(push), set(pop), set(), set(), 0, 0)
    cases = [
        ('zero-controls', make(0)),
        ('empty', make(1)),
        ('epsilon-cycle', make(2, [(0, 1), (1, 0)])),
        ('one-way-letter', make(2, push=[(0, 0, 1)])),
        ('left-loop', make(1, push=[(0, 0, 0)])),
        ('right-loop', make(1, push=[(0, 1, 0)])),
        ('balanced-excursion-only', make(2, push=[(0, 0, 1)], pop=[(1, 0, 0)])),
        ('balanced-return-cycle', make(3, push=[(1, 0, 2), (0, 1, 1)], pop=[(2, 0, 0)])),
    ]
    rng = random.Random(SEED)
    for i in range(300):
        n = rng.randrange(1, 5)
        eps = {(p, q) for p in range(n) for q in range(n) if rng.random() < .13}
        push = {(p, a, q) for p in range(n) for a in (0, 1) for q in range(n) if rng.random() < .09}
        pop = {(p, a, q) for p in range(n) for a in (0, 1) for q in range(n) if rng.random() < .09}
        cases.append((f'random-{i}', make(n, eps, push, pop)))
    return cases


def native_growth(directory):
    source = 'import Subtail.FiniteTreeDecision\nset_option maxHeartbeats 0\n'
    cases, expected = systems(), []
    for i, (_, system) in enumerate(cases):
        eps = ', '.join(f'({p},{q})' for p, q in sorted(system.epsilon))
        def edges(relation):
            return ', '.join(f'({p},{str(bool(a)).lower()},{q})' for p, a, q in sorted(relation))
        source += f'''def m{i} : Subtail.StackSummary.System {system.size} where
  eps p q := ([{eps}] : List (Nat × Nat)).contains (p.val,q.val)
  push a p q := ([{edges(system.push)}] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
  pop a p q := ([{edges(system.pop)}] : List (Nat × Bool × Nat)).contains (p.val,a,q.val)
'''
        expected.append(bool(threshold_hot(system)))
    evaluations = ','.join(f'Subtail.FiniteTreeDecision.growthCheck m{i}' for i in range(len(cases)))
    source += '#eval IO.println ("GROWTH_CORPUS:" ++ toString [' + evaluations + '])\n'
    file = directory / 'Growth.lean'
    file.write_text(source)
    output = command(['lake', 'env', 'lean', str(file)], timeout=120)
    rows = [line[len('GROWTH_CORPUS:'):] for line in output.splitlines() if line.startswith('GROWTH_CORPUS:')]
    if len(rows) != 1:
        raise RuntimeError('Missing actual native growth corpus')
    actual = json.loads(rows[0])
    if actual != expected:
        raise RuntimeError('Native/oracle mismatch: ' + repr([
            cases[i][0] for i in range(min(len(actual), len(expected))) if actual[i] != expected[i]]))
    return {'status': 'PASS', 'cases': len(cases), 'growth_true': sum(actual), 'seed': SEED,
            'oracle': 'independent predecessor saturation; no cycle classifier',
            'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
            'named_cases': {name: actual[i] for i, (name, _) in enumerate(cases) if not name.startswith('random-')}}


def query_only_cases(directory):
    cases = []
    for name, data, expected in (
        ('zero-variable-reflexivity', {'variables': [], 'constraints': [], 'query': ['bottom', 'bottom']}, 'ENTAILED'),
        ('query-only-products', {'variables': ['x'], 'constraints': [], 'query':
            [{'prod': ['x', {'prod': ['bottom', 'bottom']}]}, 'bottom']}, 'NOT_ENTAILED'),
    ):
        file = directory / (name + '.json')
        file.write_text(json.dumps(data))
        args = ['python3', 'scripts/subtail.py', str(file), '--finite-trees', '--timeout', '40']
        result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True, timeout=50)
        answer = json.loads(result.stdout)
        if result.returncode or answer['status'] != expected or answer.get('growth_analysis', {}).get('finite_model_obstruction') is not False:
            raise RuntimeError(name + ': ' + result.stdout + result.stderr)
        cases.append({'name': name, 'input': data, 'status': 'PASS', 'result': answer})
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'tmp/finite-tree-decision.json')
    args = parser.parse_args()
    target = args.output.resolve()
    target.parent.mkdir(parents=True, exist_ok=True)
    directory = target.parent / (target.stem + '-scratch')
    directory.mkdir(exist_ok=True)
    version = command(['lean', '--version']).strip()
    if 'version 4.33.1,' not in version:
        raise RuntimeError('Use pinned Lean 4.33.1')
    command(['lake', 'build', '+Subtail.FiniteTreeDecision', '+Subtail.RegularTreeCertificate'])
    for module in MODULES:
        command(['lake', 'env', 'leanchecker', 'Subtail.' + module])
    declarations = audit(directory)
    native = native_growth(directory)
    cases = cli_cases() + query_only_cases(directory)
    for case in cases:
        if case['name'] not in ('same-input-arbitrary', 'reject-infinite-model', 'capped-growth'):
            if case['result'].get('basis') != 'Lean FiniteTreeDecision.entailsCheck_correct':
                raise RuntimeError('Finite CLI did not use the proved function: ' + case['name'])
    paths = [ROOT / 'lean/Subtail' / (m + '.lean') for m in MODULES] + [Path(__file__),
        ROOT / 'scripts/subtail.py', ROOT / 'scripts/finite_trees.py',
        ROOT / 'scripts/check_finite_tree_reduction.py', ROOT / 'experiments/check_finite_trees.py',
        ROOT / 'experiments/check_stack_summary.py', ROOT / 'scripts/regular_countermodel.py']
    result = {'status': 'PASS', 'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'host': platform.node(), 'platform': platform.platform(), 'toolchain': version,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'build': 'PASS', 'kernel_replay': 'PASS', 'declarations': declarations,
              'native_growth': native, 'cli_cases': cases,
              'trust': 'Unconditional Lean finite-expression entailment theorem and executable growth classifier. JSON parsing/emission, native execution, extraction and rooted graph finiteness remain external. C084 instance proofs certify arbitrary non-entailment.'}
    target.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'PASS: build/kernel, {len(declarations)} declaration closures, {native["cases"]} native oracle comparisons, {len(cases)} actual CLI cases')


if __name__ == '__main__':
    main()
