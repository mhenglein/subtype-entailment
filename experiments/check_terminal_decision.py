#!/usr/bin/env python3
"""Exhaustive one/two-state terminal decision differential.

The Python oracle checks the original word predicate on "", "0", and "1".
This is complete here by the existing TwoState.exists_short_witness_two_states
theorem; no bounded search failure is treated as a general NO.
Larger-state promotion enumeration is deliberately not benchmarked.
"""
from __future__ import annotations
import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import subprocess

from check_finishing_trace import Instance, literal_witness

ROOT = Path(__file__).resolve().parents[1]


def cases():
    for k in (1, 2):
        for start, trans, finals, bad, flags in product(
                range(k), range((k + 1) ** (2 * k)), range(2 ** k),
                range(2 ** k), range(2 ** (k * k))):
            def digit(j):
                n = trans // (k + 1) ** j % (k + 1)
                return n if n < k else -1
            delta = tuple((digit(2*q), digit(2*q+1)) for q in range(k))
            final_set = frozenset(q for q in range(k) if finals >> q & 1)
            if any(delta[q] != (-1, -1) for q in final_set):
                continue
            I = Instance(delta, start, final_set,
                         frozenset(q for q in range(k) if bad >> q & 1),
                         frozenset((q, r) for q in range(k) for r in range(k)
                                   if flags >> (q*k+r) & 1))
            expected = any(literal_witness(I, w) for w in ("", "0", "1"))
            yield k, (start, trans, finals, bad, flags), expected


PREAMBLE = """
import Subtail.RankQueryDecision
import Subtail.TwoState
open Subtail Subtail.RankQueryDecision
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

def bit (n j : Nat) : Bool := n / 2^j % 2 == 1

def decoded (k : Nat) (hk : 0 < k)
    (start trans finals bad flags : Nat) : Instance k :=
  { initial := ⟨start % k, Nat.mod_lt _ hk⟩
    transitions := Vector.ofFn fun q =>
      let digit := fun j =>
        let n := trans / (k+1)^j % (k+1)
        if h : n < k then some (⟨n, h⟩ : Fin k) else none
      (digit (2*q.val), digit (2*q.val+1))
    final := Vector.ofFn fun q => bit finals q.val
    bad := Vector.ofFn fun q => bit bad q.val
    flags := Vector.ofFn fun q => Vector.ofFn fun r => bit flags (q.val*k+r.val) }

def checkRows (k : Nat) (hk : 0 < k)
    (rows : List (Nat × Nat × Nat × Nat × Nat × Bool)) : IO Unit := do
  for (start, trans, finals, bad, flags, expected) in rows do
    let I := decoded k hk start trans finals bad flags
    unless terminalWitnessCheck I == expected do
      throw (IO.userError s!"terminal decision mismatch: {k}, {start}, {trans}, {finals}, {bad}, {flags}")
    unless twoStateWitnessCheck I == expected do
      throw (IO.userError "previous small-state decision mismatch")
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "tmp/terminal-decision-regressions.json")
    args = parser.parse_args()
    rows = list(cases())
    counts = {str(k): sum(n == k for n, _, _ in rows) for k in (1, 2)}
    assert counts == {"1": 20, "2": 12800}, counts
    args.output.parent.mkdir(parents=True, exist_ok=True)
    source = (ROOT / "tmp/terminal-decision-checks" / (args.output.stem + ".lean")).resolve()
    source.parent.mkdir(parents=True, exist_ok=True)
    lines = [PREAMBLE]
    for k in (1, 2):
        selected = [(data, expected) for n, data, expected in rows if n == k]
        for offset in range(0, len(selected), 64):
            terms = ["(" + ", ".join(map(str, data)) + ", " +
                     str(expected).lower() + ")" for data, expected in selected[offset:offset+64]]
            lines.append(f"#eval checkRows {k} (by decide) [" + ", ".join(terms) + "]")
    source.write_text("\n".join(lines) + "\n")
    proc = subprocess.run(["lake", "env", "lean", str(source)],
                          cwd=ROOT / "lean", capture_output=True, text=True)
    if proc.returncode:
        raise RuntimeError(proc.stdout + proc.stderr)
    result = {
        "scope": "all encoded binary terminal instances with one or two states, including all initial states, partial transitions, Bad sets, ordered flags and final sets",
        "counts_by_states": counts,
        "cases": len(rows), "yes": sum(yes for _, _, yes in rows),
        "no": sum(not yes for _, _, yes in rows),
        "oracle": "independent literal original predicate on empty and one-letter words; complete by existing TwoState theorem",
        "native": "terminalWitnessCheck and twoStateWitnessCheck both match",
        "corpus_sha256": hashlib.sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest(),
        "larger_state_promotion_evaluation": "NOT RUN; proof covers it, exhaustive compiler may be impractical",
        "failures": 0,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
