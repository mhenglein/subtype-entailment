#!/usr/bin/env python3
"""Issue #67: resource-bounded calls to unchanged Lean entrypoints.

A completed direct answer is checked against the E061 literal DAG oracle.
Inspections and phase probes are NOT counted as automatic decision coverage.
The ground-expression frontend case has the sole separating address 000;
a frontend shortcut is recorded, never counted as a terminal promotion.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import resource
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
BASE = '9f4b95784a212c322c48a957b80645a1077543ed'
DRIVER = ROOT / 'lean/Issue67NativeProbe.lean'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def execute(command, cwd, wall, cpu, memory_mib):
    """One process group, always reaped, including failed/limited executions.

    wait4 supplies actual user/system time and lifetime max RSS of the waited
    child; this is not sampled total memory of a process tree.
    """
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='32768',
               PYTHONHASHSEED='2026092067')
    def limits():
        if sys.platform.startswith('linux'):
            resource.setrlimit(resource.RLIMIT_AS, (memory_mib * 1024**2,) * 2)
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))
    began = time.monotonic()
    out = {'command': command, 'cwd': str(cwd),
           'limits': {'wall_seconds': wall, 'cpu_seconds': cpu, 'memory_mib': memory_mib}}
    with tempfile.TemporaryFile() as capture:
        try:
            proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=capture,
                                    stderr=subprocess.STDOUT, start_new_session=True,
                                    preexec_fn=limits)
        except OSError as exc:
            return dict(out, status='NOT_RUN', reason='tool_unavailable', detail=str(exc))
        timed_out = False
        try:
            while True:
                pid, status, usage = os.wait4(proc.pid, os.WNOHANG)
                if pid:
                    break
                if time.monotonic() - began >= wall:
                    timed_out = True
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    _, status, usage = os.wait4(proc.pid, 0)
                    break
                time.sleep(0.01)
        except BaseException:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                os.waitpid(proc.pid, 0)
            except ChildProcessError:
                pass
            raise
        proc.returncode = os.waitstatus_to_exitcode(status)
        capture.seek(0)
        raw = capture.read()
    text = raw.decode('utf-8', errors='replace')
    events = []
    for line in text.splitlines():
        if line.startswith('ISSUE67:') and '=' in line:
            key, value = line[len('ISSUE67:'):].split('=', 1)
            events.append([key, value])
    limited = timed_out or proc.returncode in (-signal.SIGXCPU, -signal.SIGKILL)
    limited = limited or any(s in text.lower() for s in ('stack overflow', 'out of memory', 'memory allocation failed'))
    verdict = 'UNKNOWN' if limited else ('PASS' if proc.returncode == 0 else 'FAIL')
    out.update(status=verdict, reason='resource_limit' if limited else 'completed' if proc.returncode == 0 else 'process_error',
               returncode=proc.returncode, events=events,
               stdout=text[-16000:], stdout_sha256=hashlib.sha256(raw).hexdigest(),
               stdout_truncated=len(text) > 16000,
               resources={'wall_seconds': time.monotonic() - began,
                          'user_cpu_seconds': usage.ru_utime, 'system_cpu_seconds': usage.ru_stime,
                          'peak_rss_kib': usage.ru_maxrss // 1024 if sys.platform == 'darwin' else usage.ru_maxrss})
    return out


def parameters(n, variant):
    flags = {'ordered': [(0, 1)], 'reversed': [(1, 0)], 'diagonal': [(1, 1)],
             'empty-suffix': [(0, n)], 'empty-diagonal': [(0, 0)]}.get(variant, [])
    return {'delta': [[q + 1, -1] if q < n else [-1, -1] for q in range(n + 1)],
            'start': 0, 'final': [] if variant == 'no-final' else [n],
            'bad': [0] if variant == 'bad' else [], 'flags': flags}


def expected(n, variant):
    # These functions were independently reviewed and are not the compiler.
    from issue67_independent_fixtures import (instance, complete_words,
        literal_witness, literal_safe, literal_finish, Reference)
    data = parameters(n, variant)
    I = instance(data)
    words, bound = complete_words(I)
    witnesses = [w for w in words if literal_witness(I, w)[0]]
    fields = {'witness': str(literal_witness(I, '0' * n)[0]).lower(),
              'empty_witness': str(literal_witness(I, '')[0]).lower(),
              'inspection_complete': 'true'}
    safe_one = False
    for m in range(1, n + 1):
        B = Reference('0' * m, tuple(n - j for j in range(m + 1)))
        safe = literal_safe(I, B)
        fields[f'safe_at_{m}'] = str(safe).lower()
        if safe:
            fields[f'finish_at_{m}'] = str(bool(literal_finish(I, B))).lower()
        if m == 1:
            safe_one = safe
    fields['safe_one_letter'] = str(safe_one).lower()
    return {'input': data, 'complete_dag_bound': bound, 'all_defined_words': words,
            'witnesses': witnesses, 'expected_boolean': bool(witnesses),
            'expected_inspection': fields}


def selected(mode):
    if mode == 'acceptance':
        return ([['inspect', '3', v] for v in
                 ('plain', 'ordered', 'reversed', 'diagonal', 'empty-suffix', 'bad')]
                + [['direct', '0', v] for v in ('plain', 'empty-diagonal', 'bad')]
                + [['direct', '1', v] for v in ('plain', 'ordered')]
                + [['lazy', '3', 'no-final'], ['frontend', 'negative'], ['frontend', 'positive']])
    return [['direct', str(n), v] for n, v in ((2, 'plain'), (3, 'plain'), (3, 'ordered'))] + [
        ['lazy', '3', 'plain'], ['lazy', '3', 'ordered'], ['phases', '3', 'plain']]


def provenance():
    from issue67_independent_fixtures import source_receipt
    old = source_receipt()
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, head], cwd=ROOT, check=True)
    protected = ['lean/Subtail', 'scripts/subtail.py',
                 'experiments/issue67_independent_fixtures.py',
                 'tests/fixtures/issue67-independent/cases.json']
    changed = subprocess.check_output(['git', 'diff', '--name-only', BASE, '--', *protected], cwd=ROOT, text=True)
    if changed.strip():
        raise ValueError('Protected source differs from pinned base: ' + changed)
    sources = [DRIVER, Path(__file__).resolve(), ROOT / 'lean/lean-toolchain',
               ROOT / 'scripts/subtail.py', *sorted((ROOT / 'lean/Subtail').glob('*.lean'))]
    return {'base_revision': BASE, 'checkout_revision': head,
            'protected_source_diff': changed, 'E061_dependency_pins': old,
            'source_sha256': {str(p.relative_to(ROOT)): sha(p) for p in sources}}


def check_result(row, argv, oracle):
    if row['status'] != 'PASS':
        return
    values = {}
    for k, v in row['events']:
        values.setdefault(k, []).append(v)
    if argv[0] == 'inspect':
        wanted = oracle['expected_inspection']
    else:
        wanted = {'result': str(oracle['expected_boolean']).lower()}
    failures = {k: {'expected': v, 'actual': values.get(k)} for k, v in wanted.items() if values.get(k) != [v]}
    if failures:
        row.update(status='FAIL', reason='missing_ambiguous_or_mismatching_output', failures=failures)
    row['automatic_two_promotion_success'] = (row['status'] == 'PASS' and argv in
        (['direct', '3', 'plain'], ['lazy', '3', 'plain']))
    if argv[0] == 'frontend':
        # This is guard readback, not an instrumented production call.
        row['frontend_guard_readback'] = values.get('frontend_branch', [])
        row['terminal_coverage_credit'] = False
    elif argv[0] in ('inspect', 'phases'):
        row['terminal_coverage_credit'] = False


def selftest():
    cases = [('success', "print('ISSUE67:result=true')", 3, 'PASS'),
             ('nonzero', "print('ISSUE67:result=true'); raise SystemExit(2)", 3, 'FAIL'),
             ('timeout', "import time; print('ISSUE67:begin=x',flush=True); time.sleep(2)", .1, 'UNKNOWN')]
    rows = []
    for label, code, wall, want in cases:
        row = execute([sys.executable, '-c', code], ROOT, wall, 2, 512)
        assert row['status'] == want, row
        row['selftest'] = label
        rows.append(row)
    for events in ([], [['result', 'true'], ['result', 'true']]):
        row = {'status': 'PASS', 'events': events}
        check_result(row, ['direct', '1', 'plain'], {'expected_boolean': True})
        assert row['status'] == 'FAIL'
    # The known two-promotion positive and one shared-generator conflict.
    assert expected(3, 'plain')['witnesses'] == ['000']
    assert expected(3, 'ordered')['witnesses'] == []
    return {'status': 'PASS', 'tests': 7, 'rows': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode', choices=('acceptance', 'stress', 'selftest'), default='acceptance')
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--wall-seconds', type=float, default=20)
    parser.add_argument('--cpu-seconds', type=int, default=18)
    parser.add_argument('--memory-mib', type=int, default=2048)
    parser.add_argument('--only', help='Exact space-separated driver arguments')
    args = parser.parse_args()
    if args.wall_seconds <= 0 or args.cpu_seconds < 1 or args.memory_mib < 64:
        parser.error('Resource limits must be positive; memory at least 64 MiB')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.mode == 'selftest':
        report = selftest()
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
        print(json.dumps({'mode': 'selftest', 'status': report['status'], 'tests': report['tests']}))
        return
    report = {'schema': 1, 'mode': args.mode, 'status': 'INCOMPLETE',
              'provenance': provenance(), 'command': [sys.executable, *sys.argv],
              'environment': {'python': sys.version, 'platform': platform.platform(),
                              'cpu_count': os.cpu_count(), 'LEAN_NUM_THREADS': 1,
                              'rss_basis': 'wait4 child lifetime max RSS; not process-group sum'},
              'native_execution': 'lake env lean --run (Lean runtime; not a standalone C binary)',
              'rows': []}
    jobs = selected(args.mode)
    if args.only:
        jobs = [a for a in jobs if ' '.join(a) == args.only]
        if not jobs:
            parser.error('No matching job')
    for argv in jobs:
        if argv[0] == 'frontend':
            oracle = {'expected_boolean': argv[1] == 'positive',
                      'basis': 'Ground left spines: address sets are {0^j | j < depth}',
                      'sole_separating_address_negative': '000',
                      'input': {'left_depth': 3 if argv[1] == 'positive' else 4,
                                'right_depth': 4 if argv[1] == 'positive' else 3, 'premises': []}}
        else:
            oracle = expected(int(argv[1]), argv[2])
        print('RUN ' + ' '.join(argv), flush=True)
        row = execute(['lake', 'env', 'lean', '--run', str(DRIVER), *argv],
                      ROOT / 'lean', args.wall_seconds, args.cpu_seconds, args.memory_mib)
        row.update(id=' '.join(argv), oracle=oracle,
                   input_sha256=hashlib.sha256(json.dumps(oracle['input'], sort_keys=True).encode()).hexdigest())
        check_result(row, argv, oracle)
        report['rows'].append(row)
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
        print('RECEIPT ' + json.dumps({k: v for k, v in row.items() if k not in ('stdout', 'oracle')}, sort_keys=True), flush=True)
        if row['status'] == 'FAIL':
            print(row.get('stdout', ''), flush=True)
    counts = {s: sum(r['status'] == s for r in report['rows']) for s in ('PASS','FAIL','UNKNOWN','NOT_RUN')}
    report['counts'] = counts
    report['automatic_two_promotion_success'] = any(r.get('automatic_two_promotion_success') for r in report['rows'])
    good = all(r['status'] == 'PASS' for r in report['rows']) if args.mode == 'acceptance' else not counts['FAIL']
    report['status'] = ('PASS' if good else 'FAIL') if args.mode == 'acceptance' else ('DIAGNOSTIC' if good else 'FAIL')
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print('SUMMARY ' + json.dumps({'status': report['status'], 'counts': counts,
          'automatic_two_promotion_success': report['automatic_two_promotion_success']}, sort_keys=True), flush=True)
    if not good:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
