#!/usr/bin/env python3
"""Build, replay and audit the Lean finite-graph certificate boundary.

All-word correctness comes from check_not_entails, not these finite examples.
The Python extractor has a separate ordinary proof and independent regressions.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import time

import regular_countermodel as rc
import subtail

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / 'lean/Subtail/RegularTreeCertificate.lean'
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(theorem|def|abbrev|inductive|structure)\s+([A-Za-z_][A-Za-z_0-9.']*)", re.M)


def command(args, timeout=180):
    run = subprocess.run(args, cwd=ROOT / 'lean', text=True, capture_output=True, timeout=timeout)
    if run.returncode:
        raise RuntimeError(run.stdout[-6000:] + run.stderr[-2000:])
    return run.stdout


def audit(directory):
    source = MODULE.read_text()
    if re.search(r'\b(sorry|sorryAx|native_decide|implemented_by)\b|^\s*(axiom|opaque|noncomputable|private|unsafe)\s', source, re.M):
        raise RuntimeError('Unexpected incomplete, hidden or trusted runtime declaration')
    expected = {'Subtail.RegularTreeCertificate.' + name: kind for kind, name in DECL.findall(source)}
    required = {'graphNodes', 'simulationCheck', 'simulation_sound', 'embedCheck', 'embed_eval',
                'check', 'check_sound', 'check_not_entails', 'below_iff_simulation'}
    if not {'Subtail.RegularTreeCertificate.' + name for name in required} <= expected.keys():
        raise RuntimeError('Missing certificate boundary declarations')
    file = directory / 'Axioms.lean'
    file.write_text('import Subtail.RegularTreeCertificate\n' +
                    ''.join('#print axioms ' + name + '\n' for name in expected))
    output = command(['lake', 'env', 'lean', str(file)])
    rows = re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^]]*)\])", output)
    if len(rows) != len(expected) or {name for name, _, _ in rows} != expected.keys():
        raise RuntimeError('Incomplete declaration dependency report: ' + output)
    reports = {}
    for name, _, raw in rows:
        used = {a.strip() for a in raw.split(',') if a.strip()}
        allowed = {'propext', 'Quot.sound'} | ({'Classical.choice'} if expected[name] == 'theorem' else set())
        if not used <= allowed:
            raise RuntimeError('Unexpected dependencies: ' + name + ' ' + repr(used))
        reports[name] = {'kind': expected[name], 'axioms': sorted(used)}
    return reports


def native_cases():
    cases = []
    for filename in ('examples/entailment/reverse.json', 'examples/entailment/zero-spine.json',
                     'examples/countermodels/alternating-spine.json', 'examples/countermodels/no-variables.json'):
        p = subtail.parse_problem(json.loads((ROOT / filename).read_text()))
        result = rc.extract(p, time.monotonic() + 5, max_words=128)
        if result['status'] != 'FOUND' or not subtail.check_countermodel(p, result['model'])['valid']:
            raise RuntimeError('Independent model generation failed: ' + filename)
        cases.append((filename, p, result['model'], True, None))
    _, p, model, _, _ = cases[2]
    for name, expression in (
        ('missing-simulation', '{cert with relation := fun _ _ => false}'),
        ('fabricated-simulation', '{cert with relation := fun _ _ => true}'),
        ('wrong-root-address', '{cert with word := []}'),
        ('bad-expression-embedding', '{cert with embed := fun _ => 0}'),
        ('wrong-variable-roots', '{cert with roots := fun _ => 0}'),
        ('all-bottom-graph', '{cert with graph := ⟨Vector.replicate _ none⟩}'),
    ):
        cases.append((name, p, model, False, expression))
    rng = random.Random(5703)
    for i in range(24):
        nodes = [None] + [[rng.randrange(4), rng.randrange(4)] for _ in range(3)]
        roots = {'x': rng.randrange(4), 'y': rng.randrange(4)}
        model = {'nodes': nodes, 'roots': roots}
        p = subtail.parse_problem({'variables':['x','y'],
            'constraints': [['x','y']] if i % 3 == 0 else [],
            'query': ['y', {'prod':['x','bottom']}] if i % 2 else ['x','y']})
        expected = subtail.check_countermodel(p, model)['valid']
        cases.append((f'cyclic-{i}', p, model, expected, None))
    return cases


def native(directory):
    cases = native_cases()
    sources = ['import Subtail.RegularTreeCertificate\n']
    for i, (_, problem, model, expected, override) in enumerate(cases):
        source = subtail.certificate_source(problem, model)
        source = source.split('\n', 1)[1]
        source = source[:source.index('#eval')]
        term = override or 'cert'
        sources.append(f'namespace Case{i}\n' + source +
            f'#eval IO.println ("CERT_{i}:" ++ toString (check input left right {term}))\nend Case{i}\n')
    path = directory / 'Native.lean'
    path.write_text('\n'.join(sources))
    output = command(['lake', 'env', 'lean', str(path)])
    rows = re.findall(r'^CERT_(\d+):(true|false)$', output, re.M)
    if len(rows) != len(cases) or {int(i) for i, _ in rows} != set(range(len(cases))):
        raise RuntimeError('Missing/duplicate native marker: ' + output)
    reports = []
    for i, value in rows:
        name, _, _, expected, _ = cases[int(i)]
        actual = value == 'true'
        if actual != expected:
            raise RuntimeError(f'{name}: expected {expected}, got {actual}')
        reports.append({'name': name, 'expected': expected, 'actual': actual, 'status': 'PASS'})
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'tmp/regular-certificates.json')
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    directory = args.output.parent / (args.output.stem + '-scratch')
    directory.mkdir(exist_ok=True)
    version = command(['lean', '--version']).strip()
    if 'version 4.33.1,' not in version:
        raise RuntimeError('Use the pinned Lean 4.33.1 toolchain: ' + version)
    command(['lake', 'build', '+Subtail.RegularTreeCertificate'])
    command(['lake', 'env', 'leanchecker', 'Subtail.RegularTreeCertificate'])
    declarations = audit(directory)
    cases = native(directory)
    paths = [MODULE, Path(__file__), ROOT / 'scripts/subtail.py', ROOT / 'scripts/regular_countermodel.py']
    result = {'status': 'PASS', 'build': 'PASS', 'kernel_replay': 'PASS',
              'revision': subprocess.check_output(['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip(),
              'source_sha256': {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'declarations': declarations, 'native_cases': cases,
              'scope': 'Lean certificate soundness boundary and finite native regressions; Python extraction is not Lean-verified'}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f'PASS: build/kernel, {len(declarations)} dependency closures, {len(cases)} native certificate cases')


if __name__ == '__main__':
    main()
