#!/usr/bin/env python3
"""Exhaustive absorbing one/two-state terminal-restriction differential.

Existence uses the existing complete length <= 1 two-state theorem, both for
the original instance and for finals restricted to safe-cycle-reachable states.
This is not a bounded-search claim for larger instances or for C029 in general.
"""
from __future__ import annotations
import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import subprocess

from check_finishing_trace import Instance, literal_witness
from check_terminal_decision import PREAMBLE as DECODER

ROOT = Path(__file__).resolve().parents[1]


def decoded(k, start, trans, finals, bad, flags):
    def digit(j):
        d = trans // (k+1)**j % (k+1)
        return d if d < k else -1
    return Instance(tuple((digit(2*q), digit(2*q+1)) for q in range(k)), start,
                    frozenset(q for q in range(k) if finals >> q & 1),
                    frozenset(q for q in range(k) if bad >> q & 1),
                    frozenset((q, r) for q in range(k) for r in range(k)
                              if flags >> (q*k+r) & 1))


def absorbing(I):
    return all(r in I.finals and all((p, r) not in I.flags for p in range(len(I.delta)))
               for q in I.finals for r in I.delta[q] if r >= 0)


def terminalize(I):
    safe = {q for q in range(len(I.delta)) if q not in I.bad and (q, q) not in I.flags}
    delta = tuple(tuple(r if q in safe and r in safe else -1 for r in row)
                  for q, row in enumerate(I.delta))
    return Instance(delta, I.initial,
                    frozenset(q for q in I.finals & safe if delta[q] == (-1, -1)),
                    I.bad, I.flags)


def infinite_endpoints(I):
    """Positive-length graph closure, independently of witness comparisons."""
    k = len(I.delta)
    safe = {q for q in range(k) if q not in I.bad and (q, q) not in I.flags}
    R = {(p, q) for p in safe for q in I.delta[p] if q in safe}
    for r in range(k):
        R |= {(p, q) for p in range(k) for q in range(k) if (p, r) in R and (r, q) in R}
    return {p for p in safe if any((r, r) in R and (p == r or (p, r) in R) for r in safe)}


def has_witness(I):
    assert len(I.delta) <= 2
    return any(literal_witness(I, w) for w in ('', '0', '1'))


def cases():
    for k in (1, 2):
        for data in product(range(k), range((k+1)**(2*k)), range(2**k),
                            range(2**k), range(2**(k*k))):
            I = decoded(k, *data)
            if not absorbing(I):
                continue
            J = terminalize(I)
            good = infinite_endpoints(I)
            K = Instance(I.delta, I.initial, I.finals & good, I.bad, I.flags)
            original, terminal, inf = has_witness(I), has_witness(J), has_witness(K)
            assert original == (terminal or inf), (k, data)
            tfinal = sum(1 << q for q in J.finals)
            ttrans = sum((r if r >= 0 else k) * (k+1)**(2*q+x)
                         for q, row in enumerate(J.delta) for x, r in enumerate(row))
            yield k, (*data, ttrans, tfinal, original, terminal, inf)


CHECKER = '''
open Subtail.AbsorbingTerminal

def checkAbsRows (k : Nat) (hk : 0 < k)
    (rows : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool × Bool × Bool)) : IO Unit := do
  for (start, trans, finals, bad, flags, ttrans, tfinal, original, terminal, inf) in rows do
    let I := decoded k hk start trans finals bad flags
    let J := terminalize I
    let expected := decoded k hk start ttrans tfinal bad flags
    unless J.initial == expected.initial do
      throw (IO.userError "initial state mismatch")
    for q in List.finRange k do
      unless J.final.get q == expected.final.get q && J.bad.get q == expected.bad.get q do
        throw (IO.userError "annotation mismatch")
      for x in [false, true] do
        unless step J q x == step expected q x do
          throw (IO.userError "unsafe-edge pruning mismatch")
      for p in List.finRange k do
        unless (J.flags.get p).get q == (expected.flags.get p).get q do
          throw (IO.userError "ordered-flag mismatch")
    unless twoStateWitnessCheck I == original do
      throw (IO.userError "original decision mismatch")
    unless terminalWitnessCheck J == terminal do
      throw (IO.userError "terminal decision mismatch")
    unless original == (terminal || inf) do
      throw (IO.userError "C031 split mismatch")
'''


def fixtures():
    weak = Instance(((1, -1), (-1, -1)), 0, frozenset({0, 1}),
                    frozenset(), frozenset({(0, 1)}))
    assert not absorbing(weak) and has_witness(weak)
    assert not has_witness(terminalize(weak)) and not infinite_endpoints(weak)
    prune = Instance(((1, -1), (-1, -1)), 0, frozenset({0}), frozenset({1}))
    assert terminalize(prune).finals == frozenset({0})
    nonfinal = Instance(((-1, -1),), 0, frozenset())
    assert not terminalize(nonfinal).finals
    bad_start = Instance(((-1, -1),), 0, frozenset({0}), frozenset({0}))
    assert not has_witness(terminalize(bad_start))
    return ['weak-final-closure-is-insufficient', 'prune-before-sink-test',
            'nonfinal-sink-stays-nonfinal', 'unsafe-empty-start']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'tmp/absorbing-terminal.json')
    args = parser.parse_args()
    rows = list(cases())
    named = fixtures()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    scratch = (ROOT/'tmp/absorbing-terminal-checks'/(args.output.stem + '.lean')).resolve()
    scratch.parent.mkdir(parents=True, exist_ok=True)
    lines = ['import Subtail.AbsorbingTerminal', DECODER, CHECKER]
    for k in (1, 2):
        selected = [data for n, data in rows if n == k]
        for offset in range(0, len(selected), 64):
            terms = ['(' + ','.join(str(x).lower() for x in row) + ')'
                     for row in selected[offset:offset+64]]
            lines.append(f'#eval checkAbsRows {k} (by decide) [' + ','.join(terms) + ']')
    scratch.write_text('\n\n'.join(lines) + '\n')
    proc = subprocess.run(['lake', 'env', 'lean', str(scratch)], cwd=ROOT/'lean',
                          capture_output=True, text=True, timeout=600)
    if proc.returncode:
        raise RuntimeError(proc.stdout + proc.stderr)
    result = {'status': 'PASS', 'scope': 'All encoded absorbing binary one/two-state instances, including every initial state, partial transition, Bad/final set and ordered flag set',
              'cases': len(rows), 'counts_by_states': {str(k): sum(n == k for n, _ in rows) for k in (1, 2)},
              'original_yes': sum(data[-3] for _, data in rows),
              'terminal_yes': sum(data[-2] for _, data in rows),
              'infinite_branch_yes': sum(data[-1] for _, data in rows),
              'oracle': 'Literal original word predicate; complete small-state existence via TwoState theorem; independent finite safe-cycle closure',
              'native': 'terminalize full tables and existing exact original/terminal small-state decisions',
              'fixtures': named,
              'corpus_sha256': hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest(),
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in [Path(__file__), ROOT/'lean/Subtail/AbsorbingTerminal.lean']},
              'larger_state_C029_existence': 'NOT TESTED; still an open formal obligation',
              'failures': 0}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
