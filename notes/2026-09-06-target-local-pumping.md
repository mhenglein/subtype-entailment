# Integrated target-local pending-context pumping

Date: 2026-09-08 integration of PR #11. Canonical claim: C059. Canonical experiment: E036.

**Status: written proof + executed finite checks; independent review pending; not Lean-checked. This is a certified subclass, not unrestricted Problem 1.7.**

The complete branch proof is preserved verbatim at [the archived PR #11 proof](archive/2026-09-06-target-local-pumping-branch.txt). Its provisional `C056` label was branch-local and is superseded by C059.

## C059 — bounded target tails admit a finite pending-context pump

Work in one verified paired/unary marker format. If no productive marker cycle is reachable from any effective flag target, the maximum number `h` of markers from a target to the selected terminal final is finite and computable.

Protect the final `h` blocks of a witness. Earlier blocks contain no relevant target. Relative to the fixed protected suffix, summarize each earlier source block by whole-block equality bits and equal-tail flag-hit bits. A finite pending set records which suffix contexts would complete a violation. Deleting an interval between two boundaries with the same `(macro state, pending set)` preserves the run and every relevant flag obligation.

This yields an existence-preserving marker bound

    h + K * 2^(h-1)

for the certified slice, where `K` is the productive macro-state count. Enumerating the finitely many resulting schemas and applying the exact bounded-delimited solver gives an exact decision for this class. Missing formats, target-reachable marker cycles, or resource caps remain `UNKNOWN`.

The concrete regression also records why equal original-state repetition alone is insufficient: deleting a block can complete a previously pending comparison even when the automaton splice is valid.

## E036 — reproduction

Run:

    python3 experiments/check_target_tail.py

The checker includes complete acyclic-language oracles, a cyclic-prefix family with an independent existence oracle, known-witness pumping tests, the pending-context counterexample, the five-state NO fixture, canonical subtype checks, and explicit unsupported/cap guards.

[Implementation](../experiments/target_tail.py), [checker](../experiments/check_target_tail.py).
