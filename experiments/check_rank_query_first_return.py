#!/usr/bin/env python3
"""Finite regressions for the stage-3/4 query-graph interface (#26, #28).

All-word results rely on the Lean theorems, not these finite searches. Uses
literal suffix comparisons and a separate explicit-interval partition. The
optional --lean mode executes the actual pinned Lean interval-count definition.
It never substitutes Python computations for a claimed native Lean result.
Python 3.10+, standard library only.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import tempfile


def literal_edges(w: str) -> list[list[tuple[str, int]]]:
    rows = []
    for j in range(len(w) + 1):
        borders = [h for h in range(j) if w[:j].endswith(w[:h])]
        row = [('F', max(borders, default=0))]
        if j < len(w):
            row.append(('S', j + 1))
        for a in '01':
            h = max(h for h in range(len(w) + 1) if (w[:j] + a).endswith(w[:h]))
            row.append(('K' + a, h))
        rows.append(row)
    return rows


def first_return(w: str, m: int) -> bool:
    return (0 < m < len(w) and w.endswith(w[:m])
            and not any(w[:j].endswith(w[:m]) for j in range(m + 1, len(w))))


def count_intervals(m: int, path: list[int]) -> int:
    if not path:
        return 0
    answer = int(path[0] > m)
    for a, b in zip(path, path[1:]):
        answer += int(b > m and not (a > m and b == a + 1))
    return answer


def explicit_partition(m: int, path: list[int]) -> list[list[int]]:
    """Partition NODE INDICES, keeping separate repeated physical vertices."""
    result = []
    i = 0
    while i < len(path):
        if path[i] <= m:
            i += 1
            continue
        part = [i]
        i += 1
        while i < len(path) and path[i] > m and path[i] == path[i - 1] + 1:
            part.append(i)
            i += 1
        result.append(part)
    assert [i for part in result for i in part] == [i for i, p in enumerate(path) if p > m]
    assert all(all(path[j] == path[i] + 1 for i, j in zip(part, part[1:])) for part in result)
    return result


def simple_observer_paths(rows, states, moves, start, limit):
    """All product-simple paths to the stated EDGE bound; not an existence oracle."""
    stack = [([start], [])]
    while stack:
        nodes, letters = stack.pop()
        yield nodes, letters
        if len(letters) == limit:
            continue
        u, q = nodes[-1]
        for a, v in rows[u]:
            for p in moves[q, a]:
                node = (v, p)
                if node not in nodes:
                    stack.append((nodes + [node], letters + [a]))


def native_counts(cases: list[tuple[int, list[int]]]) -> dict:
    repo = Path(__file__).resolve().parents[1]
    lean_dir = repo / 'lean'
    source = ('import Subtail.RankQueryFirstReturn\nset_option maxRecDepth 20000\n'
              'set_option maxHeartbeats 0\nopen Subtail.RankQueryFirstReturn\n')
    source += 'def inputCases : List (Nat × List Nat) := [\n'
    source += ',\n'.join(f'({m}, [{",".join(map(str, p))}])' for m, p in cases) + '\n]\n'
    source += ('def main : IO Unit := inputCases.forM fun c =>\n'
               '  IO.println (toString (freshIntervals (fun n : Nat => n) c.1 c.2))\n')
    version = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=lean_dir,
                             check=True, text=True, capture_output=True, timeout=60).stdout
    if 'version 4.33.1,' not in version:
        raise RuntimeError('Unexpected Lean toolchain: ' + version)
    with tempfile.TemporaryDirectory(prefix='query-first-return-') as td:
        src = Path(td) / 'Counts.lean'
        src.write_text(source, encoding='utf-8')
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(src)], cwd=lean_dir,
                                check=False, text=True, capture_output=True, timeout=120)
        if result.returncode:
            raise RuntimeError('Lean evaluation failed:\n' + result.stdout + '\n' + result.stderr)
    lines = result.stdout.splitlines()
    if len(lines) != len(cases) or any(not line.isdecimal() for line in lines):
        raise RuntimeError('Unexpected native output: ' + result.stdout[:2000])
    actual = list(map(int, lines))
    expected = [len(explicit_partition(m, p)) for m, p in cases]
    if actual != expected:
        raise AssertionError('Native interval-count mismatch')
    return {'status': 'PASS', 'cases': len(cases), 'toolchain': 'leanprover/lean4:v4.33.1'}


def check(use_lean: bool = False) -> dict:
    rng = random.Random(2026091828)
    counts = Counter()
    native = []
    fixtures = []
    for n in range(2, 10):
        for bits in product('01', repeat=n):
            w = ''.join(bits)
            rows = literal_edges(w)
            for m in range(1, n):
                if not first_return(w, m):
                    continue
                counts['literal_first_returns'] += 1
                for u, row in enumerate(rows):
                    for label, v in row:
                        counts['directed_edges_checked'] += 1
                        if label == 'F':
                            assert v <= m
                        if v > m:
                            assert v == u + 1 or (u == n and v == m + 1)
                            if u <= m:
                                assert u == m and v == m + 1
                            if not (u > m and v == u + 1):
                                assert v == m + 1
                if len(fixtures) < 50 or rng.randrange(90) == 0:
                    fixtures.append((w, m, rows))
    # Generic list semantics, including lists which are not graph paths.
    for _ in range(2000):
        m = rng.randrange(1, 8)
        path = [rng.randrange(m + 6) for _ in range(rng.randrange(25))]
        assert count_intervals(m, path) == len(explicit_partition(m, path))
        native.append((m, path))
        counts['independent_partition_comparisons'] += 1
    # Short product-simple paths: the bound applies to each, not just a chosen BFS path.
    for w, m, rows in fixtures[:100]:
        s = rng.randrange(1, 4)
        moves = {(q, a): tuple(p for p in range(s) if rng.random() < 0.42)
                 for q in range(s) for a in ('F', 'S', 'K0', 'K1')}
        for _ in range(3):
            start = (rng.randrange(len(rows)), rng.randrange(s))
            for nodes, labels in simple_observer_paths(rows, s, moves, start, 5):
                vertices = [u for u, q in nodes]
                assert len(nodes) == len(set(nodes))
                assert all((label, v) in rows[u] and p in moves[q, label]
                           for (u, q), label, (v, p) in zip(nodes, labels, nodes[1:]))
                amount = count_intervals(m, vertices)
                assert amount == len(explicit_partition(m, vertices))
                visits = sum(u == m + 1 for u, q in nodes)
                assert amount <= visits + 1 <= s + 1
                counts['product_simple_path_checks'] += 1
    # The +1 cannot in general be dropped: start inside the new portion, then wrap.
    rows = literal_edges('010')
    # A finite colour guard can select precisely vertices 2 and 3:
    # End OR (not Root AND next_bit == '0').
    allowed = [j for j in range(4) if j == 3 or (j != 0 and '010'[j:j+1] == '0')]
    assert allowed == [2, 3]
    tight = []
    for s in range(1, 9):
        nodes = [(v, q) for q in range(s) for v in (3, 2)]
        labels = ['K1' if i % 2 == 0 else 'S' for i in range(len(nodes) - 1)]
        assert len(nodes) == len(set(nodes))
        assert all((a, v) in rows[u] for (u, _), a, (v, _) in zip(nodes, labels, nodes[1:]))
        assert all((p == q if a == 'K1' else p == q + 1)
                   for (_, q), a, (_, p) in zip(nodes, labels, nodes[1:]))
        # Exhaust every enabled successor: this guarded observer forces exactly
        # the displayed path; at the final node its remaining K1 exits the guard.
        for i, (u, q) in enumerate(nodes):
            successors = []
            for a, v in rows[u]:
                p = q if a == 'K1' else q + 1 if a == 'S' else s
                if v in allowed and p < s:
                    successors.append((v, p))
            assert successors == ([nodes[i+1]] if i+1 < len(nodes) else [])
        path = [v for v, _ in nodes]
        assert count_intervals(1, path) == len(explicit_partition(1, path)) == s + 1
        native.append((1, path))
        tight.append({'observer_controls': s, 'intervals': s + 1,
                      'word': '010', 'old_length': 1, 'nodes': nodes, 'labels': labels,
                      'allowed_vertices': allowed, 'entire_guarded_run_exhausted': True})
    # No-first-return negative regression: not a counterexample to the theorem.
    badpath = [4, 3, 2]
    badrows = literal_edges('0000')
    assert not first_return('0000', 1)
    assert all(('F', b) in badrows[a] for a, b in zip(badpath, badpath[1:]))
    assert count_intervals(1, badpath) == 3 > 1 + 1
    native.append((1, badpath))
    counts['tight_bound_examples'] = len(tight)
    counts['missing_first_return_counterexamples'] = 1
    return {'status': 'PASS', 'seed': 2026091828, 'counts': dict(sorted(counts.items())),
            'word_length_max': 9, 'observer_path_edge_limit': 5,
            'native_lean': native_counts(native) if use_lean else {'status': 'NOT_RUN'},
            'tight_examples': tight,
            'hypothesis_regression': {'word': '0000', 'old_length': 1, 'path': badpath,
                                     'observer_controls': 1, 'intervals': 3,
                                     'is_first_return': False},
            'limits': ['Finite tests are not the all-word or all-observer proof.',
                       'This checks the s+1 interface, not preimage compilation.',
                       'Structural toy fixtures need not be safe terminal references.']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--full-output', type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must be enabled; do not use -O')
    result = check(args.lean)
    if args.full_output:
        args.full_output.parent.mkdir(parents=True, exist_ok=True)
        args.full_output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    result['tight_examples'] = [{k: v for k, v in row.items() if k not in ('nodes', 'labels')}
                                for row in result['tight_examples']]
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text)


if __name__ == '__main__':
    main()
