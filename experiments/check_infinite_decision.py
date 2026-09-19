#!/usr/bin/env python3
"""Native C029 decision versus independent exact small-state and graph oracles.

One/two-state witness existence is complete by the existing TwoState theorem.
Infinite continuation is computed independently by positive safe-graph closure.
Larger examples are named guards, not a completeness or performance claim.
"""
from __future__ import annotations
import argparse
from itertools import product
import hashlib
import json
from pathlib import Path
import random
import subprocess

from check_absorbing_terminal import cases as absorbing_cases, absorbing
from check_finishing_trace import Instance, literal_witness
from check_absorbing_terminal import infinite_endpoints
from check_terminal_decision import PREAMBLE as DECODER
from check_infinite_cycle_monitor import suffix_oracle, plain

ROOT = Path(__file__).resolve().parents[1]


def graph_cases():
    """All simple paths in three vertices; no saturation recurrence reused."""
    for graph in range(512):
        edges = {(p, q) for p in range(3) for q in range(3) if graph >> (3*p+q) & 1}
        for start in range(3):
            reached = {start}
            for length in (1, 2):
                for tail in product(range(3), repeat=length):
                    path = (start,) + tail
                    if len(set(path)) == len(path) and all(e in edges for e in zip(path, path[1:])):
                        reached.add(path[-1])
            yield graph, start, sum(1 << q for q in reached)


CHECKER = '''
open Subtail.InfiniteDecision Subtail.FiniteSearch

def graphNext (mask : Nat) (p : Fin 3) : List (Fin 3) :=
  (List.finRange 3).filter (fun q => bit mask (3*p.val+q.val))

def checkGraphRows (rows : List (Nat × Nat × Nat)) : IO Unit := do
  for (graph, start, expected) in rows do
    let p : Fin 3 := ⟨start % 3, Nat.mod_lt _ (by decide)⟩
    for q in List.finRange 3 do
      let actual := reachesAny (graphNext graph) (List.finRange 3) p (fun r => r == q)
      unless actual == bit expected q.val do
        throw (IO.userError s!"finite graph mismatch {graph} {start} {q.val}")
      for fuel in [3, 4] do
        unless reachesAnyWithFuel (graphNext graph) fuel p (fun r => r == q) == actual do
          throw (IO.userError "numeric-fuel graph mismatch")

def checkInfiniteRows (k : Nat) (hk : 0 < k)
    (rows : List (Nat × Nat × Nat × Nat × Nat × Bool)) : IO Unit := do
  for (start, trans, finals, bad, flags, expected) in rows do
    let I := decoded k hk start trans finals bad flags
    let actual := infiniteWitnessCheck I
    unless actual == expected do
      throw (IO.userError s!"C029 mismatch {k} {start} {trans} {finals} {bad} {flags}: {actual} expected {expected}")

def wordCode (length code : Nat) : Word :=
  (List.range length).map (fun i => bit code i)

def checkPrefixRows (k : Nat) (hk : 0 < k)
    (rows : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool)) : IO Unit := do
  for (start, trans, finals, bad, flags, n, w, d, c, expected) in rows do
    let I := decoded k hk start trans finals bad flags
    let actual := Subtail.PeriodicMonitor.monitorWord I (wordCode n w) (wordCode d c)
    unless actual == expected do
      throw (IO.userError s!"prefix mismatch {k} {start} {trans} {bad} {flags} {n} {w} {d} {c}")

def checkHugeFuel : IO Unit := do
  let next : Fin 1 → List (Fin 1) := fun _ => []
  unless reachesAnyWithFuel next (2^256) 0 (fun _ => true) do
    throw (IO.userError "huge-fuel positive fixed-point mismatch")
  if reachesAnyWithFuel next (2^256) 0 (fun _ => false) then
    throw (IO.userError "huge-fuel negative fixed-point mismatch")
'''


def lean_rows(name, rows):
    lines = []
    for offset in range(0, len(rows), 64):
        terms = ['(' + ','.join(str(x).lower() for x in row) + ')' for row in rows[offset:offset+64]]
        lines.append('#eval ' + name + ' [' + ','.join(terms) + ']')
    return lines


def encode(I):
    k = len(I.delta)
    return (k, (I.initial,
        sum((q if q >= 0 else k)*(k+1)**(2*p+a) for p,row in enumerate(I.delta) for a,q in enumerate(row)),
        sum(1<<q for q in I.finals), sum(1<<q for q in I.bad),
        sum(1<<(p*k+q) for p,q in I.flags)))


def prefix_cases():
    """Direct all-offset oracle for each word; no phase or bucket logic reused."""
    rng = random.Random(2026091929)
    words = [''.join(w) for n in range(5) for w in product('01', repeat=n)]
    periods = words[1:]
    def code(w):
        return sum(int(a) << i for i, a in enumerate(w))
    for case in range(32):
        k = rng.randrange(2, 7)
        partial = case % 3 == 0
        delta = tuple(tuple(-1 if partial and rng.random() < .12 else rng.randrange(k)
                            for _ in range(2)) for _ in range(k))
        I = Instance(delta, rng.randrange(k),
                     frozenset(q for q in range(k) if rng.random() < .4),
                     frozenset(q for q in range(k) if partial and rng.random() < .1),
                     frozenset((p,q) for p in range(k) for q in range(k)
                               if (p != q or partial) and rng.random() < .18))
        _, data = encode(I)
        J = plain(I)
        for w in words:
            for c in periods:
                yield k, (*data, len(w), code(w), len(c), code(c), suffix_oracle(J, w, c))


def fixtures():
    specs = [
        ('forced-periodic-conflict', ((1,-1),(2,-1),(2,-1)), {2}, {(0,1)}, False, None),
        ('ordered-flags', ((1,-1),(2,-1),(2,-1)), {2}, {(1,0)}, True, '00'),
        ('necessary-prefinal-loop', ((1,-1),(2,1),(2,-1)), {2}, {(0,1)}, True, '0100'),
        ('terminal-only', ((1,-1),(-1,-1)), {1}, set(), False, None),
        ('terminal-only-exit-from-cycle', ((1,-1),(2,-1),(2,3),(-1,-1)), {2,3}, {(0,1)}, False, None),
        ('left-mismatch-cannot-repair', ((-1,1),(2,-1),(3,-1),(3,-1)), {3}, {(1,2)}, False, None),
        ('extend-prefix-before-cycle', ((1,-1),(2,-1),(3,-1),(-1,3)), {2,3}, {(0,1)}, True, '0001'),
    ]
    out = []
    for name,delta,finals,flags,expected,certificate in specs:
        I=Instance(delta,0,frozenset(finals),frozenset(),frozenset(flags))
        assert absorbing(I), name
        if expected:
            assert literal_witness(I, certificate), (name, certificate)
            q=I.initial
            for a in certificate:
                q=I.delta[q][int(a)]
            assert q in infinite_endpoints(I)
        k,data=encode(I)
        out.append((name,k,(*data,expected)))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'tmp/infinite-decision.json')
    args = parser.parse_args()
    corpus = list(absorbing_cases())
    rows = [(k, (*data[:5], data[-1])) for k, data in corpus]
    assert len(rows) == 15914
    graphs = list(graph_cases())
    guards = fixtures()
    prefixes = list(prefix_cases())
    assert len(prefixes) == 29760
    lines = ['import Subtail.InfiniteDecision', DECODER, CHECKER]
    lines.append('#eval checkHugeFuel')
    lines += lean_rows('checkGraphRows', graphs)
    for k in (1, 2):
        lines += lean_rows(f'checkInfiniteRows {k} (by decide)', [data for n, data in rows if n == k])
    for _, k, data in guards:
        lines += lean_rows(f'checkInfiniteRows {k} (by decide)', [data])
    for k in range(2, 7):
        lines += lean_rows(f'checkPrefixRows {k} (by decide)', [data for n, data in prefixes if n == k])
    scratch = (ROOT/'tmp/infinite-decision-checks'/(args.output.stem+'.lean')).resolve()
    scratch.parent.mkdir(parents=True, exist_ok=True)
    scratch.write_text('\n\n'.join(lines)+'\n')
    proc = subprocess.run(['lake', 'env', 'lean', str(scratch)], cwd=ROOT/'lean',
                          capture_output=True, text=True, timeout=600)
    if proc.returncode:
        raise RuntimeError(proc.stdout+proc.stderr)
    sources = ['lean/Subtail/FiniteSearch.lean', 'lean/Subtail/InfiniteDecision.lean',
               'lean/Subtail/PeriodicRun.lean', 'lean/Subtail/PeriodicMonitor.lean',
               'lean/Subtail/PeriodicRotation.lean', 'lean/Subtail/PeriodicGood.lean',
               'experiments/check_infinite_decision.py',
               'experiments/check_absorbing_terminal.py', 'experiments/check_finishing_trace.py',
               'experiments/check_infinite_cycle_monitor.py', 'experiments/check_terminal_decision.py']
    result = {
        'status': 'PASS', 'failures': 0,
        'scope': 'Actual total Lean infiniteWitnessCheck on every encoded absorbing one/two-state binary instance; complete independent small-state oracle',
        'cases': len(rows), 'yes': sum(data[-1] for _, data in rows),
        'counts_by_states': {str(k): sum(n == k for n, _ in rows) for k in (1, 2)},
        'graph_oracle': {'graphs': 512, 'seeds': 1536, 'reachability_comparisons_per_variant': 4608, 'variants': ['enumerated-state fuel', 'exact numeric fuel3', 'larger numeric fuel4'],
                         'method': 'Enumerate all simple paths of length at most two on three vertices'},
        'infinite_oracle': 'Literal Witness on empty/one-letter words complete by TwoState; independent positive safe-graph closure determines infinite endpoints',
        'huge_fuel_fixed_point': 'PASS: empty-edge one-vertex search with fuel 2^256, both acceptance values',
        'supplied_prefix_oracle': {
            'cases': len(prefixes), 'accepted': sum(data[-1] for _, data in prefixes),
            'seed': 2026091929, 'instances': 32, 'states': '2 through 6',
            'prefixes': 'Every binary word of length 0 through 4',
            'periods': 'Every binary word of length 1 through 4, including all nonprimitive periods',
            'method': 'Actual native monitorWord versus direct suffix equality over prefix length plus period length, which is exact for each supplied ultimately periodic stream',
            'assumptions': 'Arbitrary partial transition, final, Bad and directed-flag tables; absorption and cycle validity are not assumed for supplied-prefix semantics',
            'corpus_sha256': hashlib.sha256(json.dumps(prefixes, separators=(',', ':')).encode()).hexdigest(),
        },
        'corpus_sha256': hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest(),
        'source_sha256': {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
        'guards': [name for name,_,_ in guards],
        'guard_oracle': 'Positive cases have independently checked literal witnesses and safe cycles. Negative guards use forced periodic tails with a persistent flagged pair, or only terminal accepting runs.',
        'larger_state_existence': 'Seven named guards; no general larger-state census or performance claim',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS', 'cases':len(rows), 'yes':result['yes'], 'output':str(args.output)}))


if __name__ == '__main__':
    main()
