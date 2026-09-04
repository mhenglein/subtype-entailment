# Lean core

This project checks local lemmas for **binary BorderAvoid** and decides
witness existence for at most two states. The general problem and subtype
entailment remain open.

## Build and check

Use Lean **4.33.1**, pinned in [lean-toolchain](lean-toolchain), with its bundled
Lake. Follow the [official installation guide](https://lean-lang.org/install/)
if Lean is not installed. There are no third-party Lean dependencies.

From the repository root:

```sh
python3 scripts/check_lean.py
```

This builds the project, replays the compiled declarations with `leanchecker`,
audits the named algorithms and theorems, and compares native Lean evaluations
with the independent Python predicates. Results go to
[lean-checks.json](../results/lean-checks.json).

To build or inspect the axioms directly, run these commands from `lean/`:

```sh
lake build
lake env leanchecker --verbose Subtail
lake env lean Subtail/Audit.lean
```

## Checked statements

| File | Result |
|---|---|
| [Basic.lean](Subtail/Basic.lean) | Finite partial DFA, witness definition, executable checker, and `witnessCheck_correct` |
| [Truncation.lean](Subtail/Truncation.lean) | Maximum repeated-suffix specification; C008, C009, and the visited-state relaxation C013 |
| [SandwichPredicates.lean](Subtail/SandwichPredicates.lean) | Direct necessary/sufficient checks, soundness, individual lrs coverage, and reversal of the occurrence condition |
| [Boundary.lean](Subtail/Boundary.lean) | Exact separation of empty/full borders from proper borders and final-state slices |
| [TwoState.lean](Subtail/TwoState.lean) | Executable exact witness-existence test under `k<=2` |
| [Conditional.lean](Subtail/Conditional.lean) | Finite budget enumeration, correct under explicit test-soundness and bounded-coverage assumptions |
| [Examples.lean](Subtail/Examples.lean) | Empty word, undefined transitions, bad initial state, diagonal flags, and strict shortening examples |
| [Audit.lean](Subtail/Audit.lean) | Dependency-axiom reports for the runtime definitions and main theorems |

Words are `List Bool`. State sets have type `Fin k`; tables are finite vectors.
The flag condition includes both diagonal pairs and the empty suffix. A
missing transition rejects the word. Flags mean forbidden pairs.

The visited-state rule shortens `0010` to `00` in a two-state instance where
C009's all-state condition fails. This example and its distinction from C009
are checked in Lean. The finer exact-occurrence rule has a written proof and
Python checks, but is not yet formalized.

## What remains assumed or missing

`finiteBudgetDecision_correct` accepts executable parameters `size`, `F`, and
`success`. Its statement assumes:

1. Every successful fixed-budget test yields a witness.
2. Every instance with a witness has a successful budget within `F(size I)`.

The direct sufficient predicate is now implemented and proved sound for an
individual word. The finite automaton that decides whether any such word
exists, and the definition of `F`, remain missing. The conditional theorem
checks the enumeration argument; it does not settle these assumptions.
Arbitrary-tree semantics, normalization, and the subtype reduction also
remain outside this Lean core.

The current binary formalization does not claim results for every finite
alphabet. The general statements in the research notes retain their separate
written-proof status.

## Proof and computation boundaries

The named proof dependencies use only Lean's standard `propext`, `Quot.sound`,
and, for some list/truncation proofs, `Classical.choice`. The checked runtime
definitions do not depend on classical choice. Several use `propext` in
erased library proofs. No custom axiom or `sorryAx` discharges a research gap.
The audit covers the named declarations and their transitive dependencies;
new independent theorems must be added to that audit.

The native evaluation comparisons are regression tests, separate from the
kernel-checked theorem proofs. `leanchecker` replays declarations through
Lean's own kernel; it is not an independent external proof checker. Read the
[formalization note](../notes/2026-09-04-lean-core.md) and the
[A018 obligations](../research/approaches/A018.md) before extending the core.
