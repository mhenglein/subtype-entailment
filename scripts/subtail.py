#!/usr/bin/env python3
"""Capped JSON interface to the checked C081 entailment procedure.

The input parser, launcher and finite-graph certificate checker are ordinary
Python, not Lean proofs. Positive decisions only come from the Lean procedure.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / 'lean/Subtail/EntailmentFast.lean'
MARKER = 'SUBTAIL_RESULT:'


@dataclass(frozen=True)
class Problem:
    variables: tuple[str, ...]
    constraints: tuple[tuple[tuple, tuple], ...]
    query: tuple[tuple, tuple]


def parse_problem(data) -> Problem:
    if not isinstance(data, dict) or set(data) != {'variables', 'constraints', 'query'}:
        raise ValueError('Input needs exactly variables, constraints and query.')
    names = data['variables']
    if not isinstance(names, list) or any(type(x) is not str or not x or x == 'bottom' for x in names):
        raise ValueError('variables must be nonempty names; bottom is reserved.')
    if len(names) != len(set(names)):
        raise ValueError('Variable names must be unique.')
    indices = {name: i for i, name in enumerate(names)}

    def expr(x):
        if x == 'bottom':
            return ('bot',)
        if isinstance(x, str):
            if x not in indices:
                raise ValueError('Unknown variable: ' + x)
            return ('var', indices[x])
        if isinstance(x, dict) and set(x) == {'prod'}:
            p = x['prod']
            if isinstance(p, list) and len(p) == 2:
                return ('prod', expr(p[0]), expr(p[1]))
        raise ValueError('Expression must be a variable, bottom, or {"prod": [left, right]}.')

    def pair(x):
        if not isinstance(x, list) or len(x) != 2:
            raise ValueError('Each inequality is a [left, right] pair.')
        return (expr(x[0]), expr(x[1]))

    if not isinstance(data['constraints'], list):
        raise ValueError('constraints must be a list of inequalities.')
    return Problem(tuple(names), tuple(pair(x) for x in data['constraints']), pair(data['query']))


def lean_expr(e):
    if e[0] == 'bot':
        return '.bot'
    if e[0] == 'var':
        return f'(.var {e[1]})'
    return f'(.prod {lean_expr(e[1])} {lean_expr(e[2])})'


def lean_source(p: Problem) -> str:
    # Only parsed integer indices and fixed syntax enter Lean source. Names do not.
    premises = ', '.join(f'({lean_expr(l)}, {lean_expr(r)})' for l, r in p.constraints)
    return f'''import Subtail.EntailmentFast
open Subtail.ExpressionNormalization
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def input : Input {len(p.variables)} := [{premises}]
def left : Expr {len(p.variables)} := {lean_expr(p.query[0])}
def right : Expr {len(p.variables)} := {lean_expr(p.query[1])}
#eval IO.println ("{MARKER}" ++ toString
  (Subtail.EntailmentFast.entailsCheck input left right))
'''


def run_process(command, cwd, timeout, memory_gib=16.0):
    """Run one process group; a limit or nonzero exit can never yield a decision."""
    if timeout <= 0:
        return {'status': 'UNKNOWN', 'reason': 'time_limit', 'seconds': 0.0}
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    env['LEAN_STACK_SIZE_KB'] = '32768'

    def limits():
        import resource
        # macOS RLIMIT_AS does not consistently bound committed physical memory.
        if sys.platform.startswith('linux'):
            cap = int(memory_gib * 1024**3)
            resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
        cpu = max(1, math.ceil(timeout))
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))

    start = time.monotonic()
    with tempfile.TemporaryFile() as out:
        try:
            process = subprocess.Popen(command, cwd=cwd, env=env,
                                       stdout=out, stderr=subprocess.STDOUT,
                                       start_new_session=True,
                                       preexec_fn=limits if os.name == 'posix' else None)
        except OSError as exc:
            return {'status': 'UNKNOWN', 'reason': 'tool_unavailable', 'detail': str(exc)}
        try:
            process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            return {'status': 'UNKNOWN', 'reason': 'time_limit',
                    'seconds': round(time.monotonic() - start, 3)}
        # Keep output bounded even on compiler errors. A marker outside this tail
        # would yield UNKNOWN rather than a guessed answer.
        out.seek(0, os.SEEK_END)
        out.seek(max(0, out.tell() - 8000))
        output = out.read().decode('utf-8', errors='replace')
    result = {'seconds': round(time.monotonic() - start, 3),
              'returncode': process.returncode, 'output': output}
    if process.returncode:
        result.update(status='UNKNOWN', reason='process_failed_or_resource_limit')
    else:
        result['status'] = 'PASS'
    return result


def run_native(p: Problem, deadline, memory_gib=16.0):
    build = run_process(['lake', 'build', '+Subtail.EntailmentFast'], ROOT / 'lean',
                        deadline - time.monotonic(), memory_gib)
    if build['status'] != 'PASS':
        return {**build, 'stage': 'build'}
    with tempfile.TemporaryDirectory(prefix='subtail-input-') as directory:
        source = Path(directory) / 'Input.lean'
        source.write_text(lean_source(p))
        result = run_process(['lake', 'env', 'lean', str(source)], ROOT / 'lean',
                             deadline - time.monotonic(), memory_gib)
    if result['status'] != 'PASS':
        return {**result, 'stage': 'decision'}
    markers = [x.strip() for x in result['output'].splitlines() if x.startswith(MARKER)]
    if len(markers) != 1 or markers[0] not in (MARKER + 'true', MARKER + 'false'):
        return {'status': 'UNKNOWN', 'reason': 'missing_or_ambiguous_result', 'stage': 'decision'}
    return {'status': 'ENTAILED' if markers[0].endswith('true') else 'NOT_ENTAILED',
            'stage': 'decision', 'native_seconds': result['seconds'],
            'build_seconds': build['seconds'],
            'basis': 'Lean EntailmentFast.entailsCheck_correct',
            'wrapper_sha256': hashlib.sha256(MODULE.read_bytes()).hexdigest()}


def separating_path(nodes, left, right, deadline=None):
    """Exact regular-tree inclusion by reachability in the finite pair graph.

    None means inclusion; [] is a real counterexample at the root. Visited pairs
    make this terminate even for cyclic graphs. This does not call Lean.
    """
    pending = deque([(left, right, ())])
    seen = set()
    while pending:
        if deadline is not None and time.monotonic() >= deadline:
            raise TimeoutError("certificate time limit")
        a, b, word = pending.popleft()
        if (a, b) in seen:
            continue
        seen.add((a, b))
        if nodes[a] is None:
            continue
        if nodes[b] is None:
            return list(word)
        for bit in (0, 1):
            pending.append((nodes[a][bit], nodes[b][bit], word + (bit,)))
    return None


def validate_model(p: Problem, model):
    if not isinstance(model, dict) or not {'nodes', 'roots'} <= set(model):
        raise ValueError('Countermodel needs nodes and roots.')
    nodes, roots = model['nodes'], model['roots']
    if not isinstance(nodes, list) or not nodes:
        raise ValueError('nodes must be a nonempty list.')
    size = len(nodes)
    if any(x is not None and not (isinstance(x, (list, tuple)) and len(x) == 2
           and all(type(y) is int and 0 <= y < size for y in x)) for x in nodes):
        raise ValueError('A node is null (bottom) or two in-range child indices.')
    if not isinstance(roots, dict) or set(roots) != set(p.variables):
        raise ValueError('roots must name exactly the input variables.')
    if any(type(x) is not int or not 0 <= x < size for x in roots.values()):
        raise ValueError('Every root must index nodes.')
    return [None if x is None else tuple(x) for x in nodes], roots


def check_countermodel(p: Problem, model, deadline=None):
    nodes, roots = validate_model(p, model)
    intern = {node: i for i, node in enumerate(nodes)}

    def node_id(node):
        if node not in intern:
            intern[node] = len(nodes)
            nodes.append(node)
        return intern[node]

    def evaluate(e):
        if e[0] == 'bot':
            return node_id(None)
        if e[0] == 'var':
            return roots[p.variables[e[1]]]
        return node_id((evaluate(e[1]), evaluate(e[2])))

    for i, (left, right) in enumerate(p.constraints):
        path = separating_path(nodes, evaluate(left), evaluate(right), deadline)
        if path is not None:
            return {'valid': False, 'reason': 'premise_fails', 'premise': i, 'path': path}
    path = separating_path(nodes, evaluate(p.query[0]), evaluate(p.query[1]), deadline)
    if path is None:
        return {'valid': False, 'reason': 'query_holds'}
    # Return only the supplied graph. Temporary expression nodes are reconstructed
    # by every checker call and do not change the valuation of any variable.
    return {'valid': True, 'separating_path': path,
            'nodes': model['nodes'], 'roots': model['roots'],
            'checked_premises': len(p.constraints),
            'semantics': 'arbitrary bottom/product trees; finite graph denotes regular trees'}


def problem_json(p: Problem):
    def expression(e):
        if e[0] == 'bot':
            return 'bottom'
        if e[0] == 'var':
            return p.variables[e[1]]
        return {'prod': [expression(e[1]), expression(e[2])]}
    return {'variables': list(p.variables),
            'constraints': [[expression(l), expression(r)] for l, r in p.constraints],
            'query': [expression(e) for e in p.query]}


def find_countermodel(p: Problem, deadline, memory_gib=16.0):
    """Complete conditional extraction, with explicit operational limits.

    The worker's unbounded version terminates on non-entailed inputs. Resource
    exhaustion is UNKNOWN here; it never changes a previously proved decision.
    """
    with tempfile.TemporaryDirectory(prefix='subtail-model-') as directory:
        source, target = Path(directory) / 'input.json', Path(directory) / 'model.json'
        source.write_text(json.dumps(problem_json(p)))
        remaining = deadline - time.monotonic()
        result = run_process([sys.executable, str(ROOT / 'scripts/regular_countermodel.py'),
                              str(source), str(target), str(max(0, remaining))],
                             ROOT, remaining, memory_gib)
        if result['status'] != 'PASS':
            return {k: v for k, v in result.items() if k != 'output'}
        if not target.exists():
            return {'status': 'UNKNOWN', 'reason': 'missing_extraction_result'}
        if target.stat().st_size > 8 * 1024**2:
            return {'status': 'UNKNOWN', 'reason': 'certificate_size_limit'}
        found = json.loads(target.read_text())
    if found['status'] != 'FOUND':
        return found
    try:
        checked = check_countermodel(p, found.pop('model'), deadline)
    except (TimeoutError, RecursionError, MemoryError):
        return {'status': 'UNKNOWN', 'reason': 'certificate_resource_limit'}
    if not checked['valid']:
        return {'status': 'UNKNOWN', 'reason': 'extracted_model_rejected', 'check': checked}
    if checked['separating_path'] != found['separating_path']:
        # Different valid paths are harmless: the independent checker returns
        # the shortest path of the final graph, not necessarily the seed word.
        found['seed_path'] = found['separating_path']
    found['separating_path'] = checked['separating_path']
    return {**found, 'countermodel': checked}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='JSON problem file')
    parser.add_argument('--timeout', type=float, default=20.0, help='Total build/decision/explanation seconds')
    parser.add_argument('--memory-gib', type=float, default=16.0, help='Process address-space cap on Linux')
    parser.add_argument('--no-explain', action='store_true')
    parser.add_argument('--check-model', type=Path, help='Check a supplied finite-graph model instead of running Lean')
    args = parser.parse_args(argv)
    if not math.isfinite(args.timeout) or args.timeout <= 0 or not math.isfinite(args.memory_gib) or args.memory_gib <= 0:
        parser.error('timeout and memory-gib must be finite positive numbers')
    start = time.monotonic()
    deadline = start + args.timeout
    try:
        p = parse_problem(json.loads(args.input.read_text()))
        if args.check_model:
            model = json.loads(args.check_model.read_text())
            if 'countermodel' in model:
                model = model['countermodel']
            checked = check_countermodel(p, model, deadline)
            result = {'status': 'NOT_ENTAILED' if checked['valid'] else 'INVALID_MODEL',
                      'basis': 'independent Python regular-tree certificate check',
                      'countermodel': checked}
        else:
            result = run_native(p, deadline, args.memory_gib)
            if result['status'] == 'NOT_ENTAILED' and not args.no_explain:
                explanation = find_countermodel(p, deadline, args.memory_gib)
                result['explanation_search'] = {k: v for k, v in explanation.items() if k != 'countermodel'}
                if 'countermodel' in explanation:
                    result['countermodel'] = explanation['countermodel']
    except TimeoutError:
        result = {"status": "UNKNOWN", "reason": "certificate_time_limit"}
    except (ValueError, OSError, TypeError) as exc:
        result = {'status': 'INPUT_ERROR', 'reason': str(exc)}
    except (RecursionError, MemoryError):
        result = {'status': 'UNKNOWN', 'reason': 'parser_or_certificate_resource_limit'}
    result['seconds'] = round(time.monotonic() - start, 3)
    result['trust_boundary'] = (
        'Python certificate check only; Lean was not run. Parser and graph checker are not Lean-verified.'
        if args.check_model else
        'Lean algorithm checked; Python parsing, launch and certificate checker are not Lean-verified.')
    print(json.dumps(result, indent=2))
    return 0 if result['status'] in ('ENTAILED', 'NOT_ENTAILED') else 2 if result['status'] == 'UNKNOWN' else 1


if __name__ == '__main__':
    raise SystemExit(main())
