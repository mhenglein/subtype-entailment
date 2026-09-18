#!/usr/bin/env python3
"""Independent P-automaton oracle for the finite-propagation Lean layer.

Saturation constructs Pre* of an exact target word, or all stacks at one target
control. It does not use the new minimum-stack normal form or a stack cutoff.
Complete monotone-stack BFS cases independently check the reference algorithm.
--lean compares the actual compiled Boolean functions, not a Python translation.
"""
from __future__ import annotations
import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess
import tempfile

Word = tuple[int, ...]
SEED = 2026091831

@dataclass(frozen=True)
class System:
    n: int
    eps: frozenset[tuple[int, int]]
    push: frozenset[tuple[int, int, int]]
    pop: frozenset[tuple[int, int, int]]


def words(bound: int) -> list[Word]:
    return [w for k in range(bound + 1) for w in itertools.product((0, 1), repeat=k)]


def predecessor(M: System, target: int, word: Word | None):
    """Finite epsilon saturation; None means the entire target stack language."""
    extra = max(1, len(word)) if word is not None else 1
    N = M.n + extra
    sink = N - 1
    E = [{q} for q in range(N)]
    A = [[set() for _ in range(N)] for _ in range(2)]
    for p, q in M.eps:
        E[p].add(q)
    for a, p, q in M.pop:
        A[a][p].add(q)
    if word is None:
        E[target].add(sink)
        for a in (0, 1):
            A[a][sink].add(sink)
    elif not word:
        E[target].add(sink)
    else:
        p = target
        for j, a in enumerate(word):
            q = M.n + j
            A[a][p].add(q)
            p = q
    while True:
        before = tuple(frozenset(row) for row in E)
        for k in range(N):
            for p in range(N):
                if k in E[p]:
                    E[p].update(E[k])
        for a, p, q in M.push:
            targets = {r for t in E[q] for r in A[a][t]}
            for r in targets:
                E[p].update(E[r])
        if before == tuple(frozenset(row) for row in E):
            break
    def accepts(p: int, u: Word) -> bool:
        states = set(E[p])
        for a in u:
            states = {s for t in states for r in A[a][t] for s in E[r]}
        return sink in states
    return accepts


def bounded_reachable(M: System, p: int, u: Word, bound: int):
    """Used as complete only for monotone-stack systems with a proved bound."""
    todo = deque([(p, u)])
    seen = {(p, u)}
    while todo:
        p, u = todo.popleft()
        nxt = [(q, u) for x, q in M.eps if x == p]
        nxt += [(q, (a,) + u) for a, x, q in M.push if x == p and len(u) < bound]
        nxt += [(q, u[1:]) for a, x, q in M.pop if x == p and u and u[0] == a]
        for c in nxt:
            if c not in seen:
                seen.add(c)
                todo.append(c)
    return seen


def system_of(C: list[tuple], n: int) -> System:
    eps, push, pop = set(), set(), set()
    for c in C:
        if c[0] == 'leq':
            eps.add((c[1], c[2]))
        elif c[0] == 'lower':
            _, l, r, q = c
            push.update(((0, l, q), (1, r, q)))
        elif c[0] == 'upper':
            _, p, l, r = c
            pop.update(((0, p, l), (1, p, r)))
        elif c[0] != 'denial':
            raise ValueError(c)
    return System(n, frozenset(eps), frozenset(push), frozenset(pop))


def forced(C):
    return {(c[3], ()) for c in C if c[0] == 'lower'}


def semantic_case(C, n, ws):
    M = system_of(C, n)
    bad = [predecessor(M, c[1], None) for c in C if c[0] == 'denial']
    roots = forced(C)
    def safe(seeds):
        return not any(oracle(p, u) for oracle in bad for p, u in seeds)
    values = [safe(roots)]
    for a in range(n):
        for b in range(n):
            for w in ws:
                seeds = roots | {(a, w[:i]) for i in range(len(w) + 1)}
                accepts = predecessor(M, b, w)
                values.append(safe(seeds) and not any(accepts(p, u) for p, u in seeds))
    return values


def lean_word(w):
    return '[' + ','.join('true' if a else 'false' for a in w) + ']'


def lean_system(M):
    eps = '[' + ','.join(f'({p},{q})' for p, q in sorted(M.eps)) + ']'
    def triples(edges):
        return '[' + ','.join(f'({"true" if a else "false"},{p},{q})' for a, p, q in sorted(edges)) + ']'
    return ('{ eps := fun p q => decide ((p.val,q.val) \u2208 ' + eps + '), '
            'push := fun a p q => decide ((a,p.val,q.val) \u2208 ' + triples(M.push) + '), '
            'pop := fun a p q => decide ((a,p.val,q.val) \u2208 ' + triples(M.pop) + ') }')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lean', action='store_true')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    rng = random.Random(SEED)
    systems = []
    for mask in range(32):
        bits = [(mask >> i) & 1 for i in range(5)]
        systems.append(System(1, frozenset({(0, 0)} if bits[0] else ()),
            frozenset((a, 0, 0) for a in (0, 1) if bits[1 + a]),
            frozenset((a, 0, 0) for a in (0, 1) if bits[3 + a])))
    for mode in ('mixed', 'no_push', 'no_pop'):
        for _ in range(12):
            eps = frozenset((p, q) for p in range(2) for q in range(2) if rng.random() < .25)
            push = frozenset((a, p, q) for a in (0, 1) for p in range(2) for q in range(2)
                             if mode != 'no_push' and rng.random() < .25)
            pop = frozenset((a, p, q) for a in (0, 1) for p in range(2) for q in range(2)
                            if mode != 'no_pop' and rng.random() < .25)
            systems.append(System(2, eps, push, pop))
    expected = {}
    sources = ['import Subtail.CanonicalReachability',
        'open Subtail Subtail.StackSummary Subtail.StackReachability Subtail.TreeSemantics Subtail.CanonicalReachability',
        'def emit (tag : String) (xs : List Bool) : IO Unit := IO.println (tag ++ " " ++ xs.foldl (fun s b => s ++ (if b then "1" else "0")) "")']
    counts = {'systems': len(systems), 'reachability_comparisons': 0,
        'control_reachability_comparisons': 0, 'balanced_comparisons': 0,
        'complete_monotone_bfs_checks': 0, 'constraint_systems': 0,
        'satisfiability_comparisons': 0, 'supplied_address_comparisons': 0}
    for j, M in enumerate(systems):
        ws = words(3 if M.n == 1 else 2)
        targets = {(q, v): predecessor(M, q, v) for q in range(M.n) for v in ws}
        controls = [predecessor(M, q, None) for q in range(M.n)]
        vals = [targets[q, ()](p, ()) for p in range(M.n) for q in range(M.n)]
        counts['balanced_comparisons'] += len(vals)
        for p in range(M.n):
            for u in ws:
                seen = None
                if not M.push:
                    seen = bounded_reachable(M, p, u, len(u))
                elif not M.pop:
                    seen = bounded_reachable(M, p, u, max(len(u), max(map(len, ws))))
                for q in range(M.n):
                    for v in ws:
                        value = targets[q, v](p, u)
                        if seen is not None:
                            assert value == ((q, v) in seen), (M, p, u, q, v)
                            counts['complete_monotone_bfs_checks'] += 1
                        vals.append(value)
                        counts['reachability_comparisons'] += 1
        vals += [controls[q](p, u) for p in range(M.n) for u in ws for q in range(M.n)]
        counts['control_reachability_comparisons'] += M.n * len(ws) * M.n
        tag = 'S' + str(j)
        expected[tag] = ''.join('1' if b else '0' for b in vals)
        ws_text = '[' + ','.join(map(lean_word, ws)) + ']'
        sources.append(f'''#eval emit "{tag}" (let M : System {M.n} := {lean_system(M)}
  let ws : List Word := {ws_text}
  let qs := List.finRange {M.n}
  (qs.flatMap fun p => qs.map fun q => balancedCheck M p q) ++
  (qs.flatMap fun p => ws.flatMap fun u => qs.flatMap fun q => ws.map fun v => reachesCheck M p u q v) ++
  (qs.flatMap fun p => ws.flatMap fun u => qs.map fun q => controlReachCheck M p u q))''')
    C_cases = [[], [('lower', 0, 1, 0), ('denial', 1)],
               [('lower', 0, 0, 1), ('denial', 1)], [('upper', 0, 1, 1), ('denial', 1)],
               [('leq', 0, 1)], [('lower', 0, 1, 1)], [('denial', 0), ('denial', 1)]]
    universe = ([('leq', a, b) for a in range(2) for b in range(2)] +
        [(typ, a, b, c) for typ in ('upper', 'lower') for a in range(2) for b in range(2) for c in range(2)] +
        [('denial', a) for a in range(2)])
    C_cases += [sorted(rng.sample(universe, rng.randrange(1, 7))) for _ in range(25)]
    ws = words(2)
    for j, C in enumerate(C_cases):
        vals = semantic_case(C, 2, ws)
        tag = 'C' + str(j)
        expected[tag] = ''.join('1' if b else '0' for b in vals)
        counts['constraint_systems'] += 1
        counts['satisfiability_comparisons'] += 1
        counts['supplied_address_comparisons'] += len(vals) - 1
        ctext = '[' + ','.join('.' + c[0] + ' ' + ' '.join(map(str, c[1:])) for c in C) + ']'
        wtext = '[' + ','.join(map(lean_word, ws)) + ']'
        sources.append(f'''#eval emit "{tag}" (let C : List (Constraint 2) := {ctext}
  let ws : List Word := {wtext}
  [satCheck C] ++ (List.finRange 2).flatMap (fun a => (List.finRange 2).flatMap (fun b => ws.map (fun w => separationCheck C a b w))))''')
    if args.lean:
        root = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory(prefix='stack-oracle-') as tmp:
            path = Path(tmp) / 'Cases.lean'
            path.write_text('\n\n'.join(sources) + '\n')
            proc = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=root / 'lean',
                text=True, capture_output=True, timeout=600)
            if proc.returncode:
                raise RuntimeError(proc.stdout + '\n' + proc.stderr)
            actual = dict(line.split(' ', 1) for line in proc.stdout.splitlines()
                          if line and line[0] in ('S', 'C') and ' ' in line)
            assert set(actual) == set(expected), (set(actual), set(expected), proc.stdout)
            for tag, values in expected.items():
                assert actual[tag] == values, (tag, actual[tag], values)
    encoded = json.dumps(expected, sort_keys=True, separators=(',', ':')).encode()
    result = {'status': 'PASS', 'seed': SEED, 'counts': counts, 'lean_native': args.lean,
        'oracle_sha256': hashlib.sha256(encoded).hexdigest(),
        'scope': 'Finite corpus differential evidence; all-length claims require the separate Lean correctness proofs, not extrapolation from this corpus',
        'oracle': 'Independent epsilon/letter P-automaton predecessor saturation; no stack cutoff',
        'bounded_bfs_scope': 'Only no-push or no-pop systems, where stack monotonicity proves completeness for tested endpoints'}
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')

if __name__ == '__main__':
    main()
