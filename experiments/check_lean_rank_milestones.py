#!/usr/bin/env python3
"""Finite semantic regressions for the Lean rank/milestone formalization.

The Lean theorem proofs, NOT these word bounds, justify all-word statements.
With --lean, compare native executable Lean definitions against literal slicing.
No network, solver, hash-based word equality, or third-party dependencies.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BASE = '2fe18864e39a26f6dd256bf05bea166c8c6b3d20'

def literal_borders(word: str) -> list[int]:
    return [b for b in range(len(word) + 1) if word[:b] == word[len(word)-b:]]

def prefix_function(word: str) -> tuple[list[int], list[int]]:
    """Separate KMP recurrence, with a zero entry for the empty prefix."""
    pi, depth = [0], [0]
    for i, a in enumerate(word):
        p = pi[i]
        while p and word[p] != a:
            p = pi[p]
        if i and word[p] == a:
            p += 1
        pi.append(p)
        depth.append(depth[p] + 1)
    return pi, depth

def all_words(bound: int):
    for n in range(bound + 1):
        for bits in product('01', repeat=n):
            yield ''.join(bits)

def check_words(bound: int) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for word in all_words(bound):
        bs = [literal_borders(word[:n]) for n in range(len(word) + 1)]
        ranks = [len(b) - 1 for b in bs]
        pi, depth = prefix_function(word)
        assert ranks == depth
        assert literal_borders(word[::-1]) == bs[-1]
        first: dict[int, int] = {}
        for n in range(len(word) + 1):
            assert pi[n] == max((b for b in bs[n] if b < n), default=0)
            if n:
                assert bs[n] == bs[pi[n]] + [n]
                assert ranks[n] == ranks[pi[n]] + 1
            for h in range(1, ranks[n] + 1):
                first.setdefault(h, n)
            counts['prefixes_checked'] += 1
        for h, m in first.items():
            assert ranks[m] == h
            assert all(r < h for r in ranks[:m])
            if h + 1 in first:
                n = first[h + 1]
                assert pi[n] == m
                assert all(m not in bs[j] for j in range(m + 1, n))
                counts['successive_milestones'] += 1
                counts['overlapping_milestones'] += n < 2 * m
                counts['milestones_at_final_position'] += n == len(word)
            else:
                assert all(m not in bs[j] for j in range(m + 1, len(word) + 1))
                counts['maximal_rank_tails'] += 1
        # Every possible old reference, not only first rank milestones.
        for m in range(1, len(word)):
            n = next((j for j in range(m + 1, len(word) + 1) if m in bs[j]), None)
            if n is None:
                continue
            assert pi[n] == m
            assert all(pi[j] < m for j in range(m + 1, n))
            counts['arbitrary_first_returns'] += 1
            counts['overlapping_first_returns'] += n < 2 * m
            counts['singleton_extensions'] += n == m + 1
        counts['binary_words'] += 1
    return dict(sorted(counts.items()))

def native_lean(bound: int) -> int:
    lean_dir = ROOT / 'lean'
    version = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=lean_dir,
                             text=True, capture_output=True, check=True).stdout
    if 'version 4.33.1,' not in version:
        raise RuntimeError('Expected the repository-pinned Lean 4.33.1: ' + version)
    lines = ['import Subtail.RankMilestones', 'open Subtail Subtail.TerminalRank Subtail.RankMilestones',
             'set_option maxRecDepth 4096', 'set_option maxHeartbeats 10000000',
             'def checkRows (rows : List (Word × List Nat × Nat × Nat)) : IO Unit := do',
             '  for (w, bs, r, p) in rows do',
             '    unless borderLengths w == bs do',
             '      throw (IO.userError s!"border mismatch: {w}")',
             '    unless rank w == r do',
             '      throw (IO.userError s!"rank mismatch: {w}")',
             '    unless failureParent w == p do',
             '      throw (IO.userError s!"failure-parent mismatch: {w}")']
    rows = []
    for word in all_words(bound):
        bs = literal_borders(word)
        p = max((b for b in bs if b < len(word)), default=0)
        lean_word = '[' + ','.join('true' if a == '1' else 'false' for a in word) + ']'
        rows.append(f'({lean_word}, {bs}, {len(bs)-1}, {p})')
    for i in range(0, len(rows), 64):
        lines.append('#eval checkRows [' + ','.join(rows[i:i+64]) + ']')
    scratch = ROOT / 'tmp' / 'lean-rank-milestones-regressions.lean'
    scratch.parent.mkdir(parents=True, exist_ok=True)
    scratch.write_text('\n'.join(lines) + '\n', encoding='utf-8')
    done = subprocess.run(['lake', 'env', 'lean', str(scratch)], cwd=lean_dir,
                          text=True, capture_output=True)
    if done.returncode:
        raise RuntimeError(done.stdout + done.stderr)
    return len(rows)

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error('Assertions must be enabled; do not use python -O')
    result = dict(status='PASS', base_foundation=BASE, python_max_word_length=12,
                  counts=check_words(12), native_lean='NOT_RUN')
    if args.lean:
        result['native_lean'] = dict(status='PASS', toolchain='leanprover/lean4:v4.33.1',
                                    max_word_length=10, words=native_lean(10))
    result['limits'] = ['Finite regressions are separate from the kernel-checked all-word proofs.',
                        'No uniform preimage compiler or unrestricted subtype decision is verified here.']
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')

if __name__ == '__main__':
    main()
