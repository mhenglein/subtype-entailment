#!/usr/bin/env python3
"""Native summary bridge differential against independent P-automata.

All reference predecessor languages are exact and use no stack cutoff. The
finite corpus is regression evidence; all-word results are Lean theorems.
"""
from __future__ import annotations
import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import subprocess

from check_stack_summary import system_of, predecessor, semantic_case, words, lean_word
from check_finishing_trace import Instance, literal_witness

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026091931


def subsets(xs):
    if not xs:
        return [()]
    tail = subsets(xs[1:])
    return tail + [(xs[0],) + ys for ys in tail]


def reference(n, C, a, b):
    """Full physical table, using independently saturated predecessor languages."""
    M = system_of(C, n)
    R = type(M)(n, frozenset((q, p) for p, q in M.eps),
                frozenset((x, q, p) for x, p, q in M.pop),
                frozenset((x, q, p) for x, p, q in M.push))
    def balanced(N):
        oracles = [predecessor(N, q, ()) for q in range(n)]
        return [{q for q in range(n) if oracles[q](p, ())} for p in range(n)]
    E, F = balanced(M), balanced(R)
    forced = {c[3] for c in C if c[0] == 'lower'}
    denials = [predecessor(M, c[1], None) for c in C if c[0] == 'denial']
    danger = {p for p in range(n) if any(f(p, ()) for f in denials)}
    sat = not bool(forced & danger)
    ss = list(product(subsets(tuple(range(n))), repeat=2))
    ids = {pair: j for j, pair in enumerate(ss)}
    def nxt(N, G, S, x):
        return tuple(q for q in range(n)
                     if any(letter == x and p in S and q in G[r]
                            for letter, p, r in N.pop))
    delta = tuple(tuple(ids[(nxt(M, E, B, x), nxt(R, F, A, x))]
                        for x in (0, 1)) for B, A in ss)
    initial = ids[(tuple(sorted(E[a])), tuple(sorted(F[b])))]
    finals = frozenset(j for j, (_, A) in enumerate(ss) if not set(A) & forced)
    bad = frozenset(j for j, (B, _) in enumerate(ss) if not sat or set(B) & danger)
    flags = frozenset((i, j) for i, (B, _) in enumerate(ss)
                      for j, (_, A) in enumerate(ss) if set(B) & set(A))
    I = Instance(delta, initial, finals, bad, flags)
    for q in finals:
        for r in delta[q]:
            assert r in finals and all((p, r) not in flags for p in range(len(ss)))
    return I, sat


def corpus():
    one = [('leq', 0, 0), ('upper', 0, 0, 0), ('lower', 0, 0, 0), ('denial', 0)]
    out = [(1, [c for j, c in enumerate(one) if mask >> j & 1], 3, 'one-state-exhaustive')
           for mask in range(16)]
    fixtures = [
        ('empty-and-diagonal', []),
        ('infinite-left-spine', [('lower', 0, 1, 0), ('denial', 1)]),
        ('forced-root-unsat', [('lower', 0, 0, 1), ('denial', 1)]),
        ('nonempty-denial', [('upper', 0, 1, 1), ('denial', 1)]),
        ('ordered-epsilon', [('leq', 0, 1)]),
        ('lower-propagation', [('lower', 0, 1, 1)]),
        ('all-denied', [('denial', 0), ('denial', 1)]),
    ]
    out += [(2, C, 3, name) for name, C in fixtures]
    rng = random.Random(SEED)
    universe = ([('leq', a, b) for a, b in product(range(2), repeat=2)] +
                [(op, a, b, c) for op in ('upper', 'lower')
                 for a, b, c in product(range(2), repeat=3)] +
                [('denial', q) for q in range(2)])
    out += [(2, sorted(rng.sample(universe, rng.randrange(1, 8))), 3, 'seeded')
            for _ in range(18)]
    out += [(3, [('lower', 0, 2, 1), ('denial', 2)], 2, 'proper-prefix-seed')]
    return out


PREAMBLE = '''import Subtail.SummaryAutomaton
open Subtail Subtail.TreeSemantics Subtail.CanonicalReachability Subtail.SummaryAutomaton
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000
def emit (tag : String) (xs : List Bool) : IO Unit :=
  IO.println (tag ++ " " ++ xs.foldl (fun s b => s ++ (if b then "1" else "0")) "")
def emitNat (tag : String) (xs : List Nat) : IO Unit :=
  IO.println (tag ++ " " ++ String.intercalate "," (xs.map toString))
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'tmp/subtype-summary-bridge.json')
    args = parser.parse_args()
    sources = [PREAMBLE]
    expected = {}
    counts = {'constraint_systems': 0, 'query_words': 0, 'native_booleans': 0,
              'table_states': 0, 'ordered_flags': 0, 'all_state_absorption_edges': 0}
    cases = corpus()
    for j, (n, C, bound, name) in enumerate(cases):
        ws = words(bound)
        vals = semantic_case(C, n, ws)
        I, sat = reference(n, C, 0, 0)
        assert sat == vals[0]
        k = len(I.delta)
        ctext = '[' + ','.join('.' + c[0] + ' ' + ' '.join(map(str, c[1:])) for c in C) + ']'
        wtext = '[' + ','.join(map(lean_word, ws)) + ']'
        sources.append(f'def C{j} : List (Constraint {n}) := {ctext}')
        sources.append(f'''#eval emit "M{j}" (let I := summaryInstance C{j} 0 0
  let qs := List.finRange (states {n}).length
  [satCheck C{j}] ++ qs.map (fun q => I.bad.get q) ++ qs.map (fun q => I.final.get q) ++
  qs.flatMap (fun p => qs.map (fun q => (I.flags.get p).get q)))''')
        expected['M' + str(j)] = ''.join('1' if x else '0' for x in
            [sat] + [q in I.bad for q in range(k)] + [q in I.finals for q in range(k)] +
            [(p, q) in I.flags for p in range(k) for q in range(k)])
        sources.append(f'''#eval emitNat "T{j}" (let I := summaryInstance C{j} 0 0
  (List.finRange (states {n}).length).flatMap fun q =>
    [false,true].map fun x => ((step I q x).map fun r => r.val+1).getD 0)''')
        expected['T' + str(j)] = ','.join(str(r+1) for row in I.delta for r in row)
        wanted = []
        offset = 1
        for a in range(n):
            for b in range(n):
                inst, _ = reference(n, C, a, b)
                literal = [literal_witness(inst, ''.join(map(str, w))) for w in ws]
                oracle = vals[offset:offset+len(ws)]
                assert literal == oracle, (j, name, a, b, literal, oracle)
                wanted += [v for v in oracle for _ in range(2)]
                offset += len(ws)
        sources.append(f'''#eval emit "W{j}" ((List.finRange {n}).flatMap fun a =>
  (List.finRange {n}).flatMap fun b =>
    let I := summaryInstance C{j} a b
    ({wtext} : List Word).flatMap fun w => [witnessCheck I w, separationCheck C{j} a b w])''')
        expected['W' + str(j)] = ''.join('1' if v else '0' for v in wanted)
        counts['constraint_systems'] += 1
        counts['query_words'] += n*n*len(ws)
        counts['native_booleans'] += len(expected['M'+str(j)]) + len(wanted)
        counts['table_states'] += k
        counts['ordered_flags'] += k*k
        counts['all_state_absorption_edges'] += 2*len(I.finals)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    scratch = (ROOT / 'tmp/subtype-summary-checks' / (args.output.stem + '.lean')).resolve()
    scratch.parent.mkdir(parents=True, exist_ok=True)
    scratch.write_text('\n\n'.join(sources) + '\n')
    proc = subprocess.run(['lake', 'env', 'lean', str(scratch)], cwd=ROOT/'lean',
                          text=True, capture_output=True, timeout=600)
    if proc.returncode:
        raise RuntimeError(proc.stdout + proc.stderr)
    actual = dict(line.split(' ', 1) for line in proc.stdout.splitlines()
                  if line.startswith(('M', 'T', 'W')) and ' ' in line)
    assert actual.keys() == expected.keys(), (actual.keys(), expected.keys(), proc.stdout)
    for tag, value in expected.items():
        assert actual[tag] == value, (tag, actual[tag], value)
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in [ROOT/'lean/Subtail/SummaryBridge.lean', ROOT/'lean/Subtail/SummaryAutomaton.lean',
                        Path(__file__), ROOT/'experiments/check_stack_summary.py',
                        ROOT/'experiments/check_finishing_trace.py']}
    result = {'status': 'PASS', 'seed': SEED, 'counts': counts,
              'scope': 'Finite differential corpus; no claim that sampled words decide arbitrary entailment',
              'oracle': 'Independent exact P-automaton predecessor saturation plus literal original word predicate',
              'native': 'summaryInstance transitions, Bad/final/ordered flag tables, witnessCheck and separationCheck',
              'fixtures': [name for _, _, _, name in cases if name not in ('seeded', 'one-state-exhaustive')],
              'corpus_sha256': hashlib.sha256(json.dumps(cases, separators=(',', ':')).encode()).hexdigest(),
              'source_sha256': hashes, 'failures': 0}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
