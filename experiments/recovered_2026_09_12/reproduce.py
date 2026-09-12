#!/usr/bin/env python3
"""Recover and replay both original research bundles without modifying tracked files.

This is an integrity/reproduction runner, not a subtype-entailment solver.
It reconstructs the large generated files and verifies every original manifest.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
NAMES = ('subtail_source_visit_bound', 'subtail_closed_walk_lift')


def run(folder: Path, *arguments: str) -> bytes:
    result = subprocess.run([sys.executable, *arguments], cwd=folder,
                            capture_output=True, check=True, timeout=180)
    if result.stderr:
        sys.stderr.buffer.write(result.stderr)
    return result.stdout


def verify_manifest(folder: Path, allow_missing: frozenset[str] = frozenset()) -> int:
    count = 0
    for line in (folder / 'SHA256SUMS').read_text(encoding='utf-8').splitlines():
        digest, name = line.split('  ', 1)
        if Path(name).name != name:
            raise ValueError('Unexpected manifest path: ' + name)
        file = folder / name
        if not file.is_file() and name in allow_missing:
            continue
        actual = hashlib.sha256(file.read_bytes()).hexdigest()
        if actual != digest:
            raise ValueError('SHA256 mismatch: ' + str(file))
        count += 1
    return count


def main() -> int:
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without -O: the archived tests use assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='New or empty directory for the recovered bundles')
    args = parser.parse_args()
    if args.output:
        out = args.output.resolve()
        if out.exists() and (not out.is_dir() or any(out.iterdir())):
            parser.error('--output must be a new or empty directory')
        out.mkdir(parents=True, exist_ok=True)
    else:
        out = Path(tempfile.mkdtemp(prefix='subtail-recovered-2026-09-12-'))
    omitted = {
        NAMES[0]: frozenset({'results.json', 'run.log'}),
        NAMES[1]: frozenset({'formula-example.json', 'witness-model.json'}),
    }
    for name in NAMES:
        verify_manifest(ROOT / name, omitted[name])
        shutil.copytree(ROOT / name, out / name, ignore=shutil.ignore_patterns('__pycache__'))
    lower, lift = (out / name for name in NAMES)
    output = run(lower, 'source_visit_bound.py', '--self-test', '--output', 'results.json')
    (lower / 'run.log').write_bytes(output)
    run(lift, 'closed_walk_lift.py', '--compile-example', 'formula-example.json')
    run(lift, 'check_closed_walk_lift.py', '--output', 'checks.json')
    # Reconstruct the saved explicit assignment from its fixed primary words.
    # This is deterministic certificate construction, not a satisfiability search.
    program = """import json
from closed_walk_lift import compile_scheme, example, Phase
primary = {'C0':'','C1':'110','U0':'1010','A0_0':'10','A0_1':'10'}
bundle = compile_scheme(example(), (Phase(0, (0, 0)),), primary)
certificate = {'primary_assignment': primary, 'assignment': bundle['grounded_model'],
               'solver_executed': False,
               'meaning': 'One explicit satisfying assignment, not an existential search'}
with open('witness-model.json', 'w', encoding='utf-8') as handle:
    json.dump(certificate, handle, indent=2)
    handle.write('\\n')
"""
    run(lift, '-c', program)
    count = sum(verify_manifest(out / name) for name in NAMES)
    certificate = json.loads(run(lift, 'verify_example.py'))
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text(encoding='utf-8'))
    for relative, info in provenance['generated_files'].items():
        data = (out / relative).read_bytes()
        if len(data) != info['size_bytes'] or hashlib.sha256(data).hexdigest() != info['sha256']:
            raise ValueError('Generated artifact differs from the original: ' + relative)
    print(json.dumps({'status': 'PASS', 'output': str(out),
                      'original_manifest_files_verified': count,
                      'generated_files_recovered_exactly': len(provenance['generated_files']),
                      'positive_certificate': certificate,
                      'solver_executed': False, 'lean_checked': False,
                      'independent_mathematical_review': False}, indent=2))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        raise SystemExit('Recovery/reproduction failed: ' + str(error))
