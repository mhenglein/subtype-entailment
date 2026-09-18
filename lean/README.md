# Lean core

This project checks local lemmas for **binary BorderAvoid**, decides witness
existence for at most two states, and formalizes structural dependencies of the
[proposed rank-query solution](../research/RANK_QUERY_COMPILER.md). There is no
complete Lean-verified general BorderAvoid or subtype-entailment decision yet.

## Role in the research process

This core remains maintained. Under
[the current plan](../research/PLAN.md), a new formalization task must name the
specific semantic uncertainty, disputed implication, or stable critical
dependency it resolves. Early formalization is welcome when it answers that
question; otherwise prioritize a conceptual route, falsification and ordinary
mathematical review. Existing checks are still required for Lean changes.
Conditional theorem hypotheses below remain open mathematics, not progress
obtained merely by extending the formal framework. The September 18
user-requested continuation checks the rank/first-return dependency of the
concrete candidate; its central shared-word compiler remains unformalized.

## Build and check

Use Lean **4.33.1**, pinned in [lean-toolchain](lean-toolchain), with its bundled
Lake. Follow the [official installation guide](https://lean-lang.org/install/)
if Lean is not installed. There are no third-party Lean dependencies.

From the repository root:

```sh
python3 scripts/check_lean.py
python3 experiments/check_lean_rank_milestones.py --lean --output /tmp/lean-rank-milestones.json
cmp results/lean-rank-milestones.json /tmp/lean-rank-milestones.json
```

The first command builds the project, replays the compiled declarations with
`leanchecker`, audits the earlier named algorithms and theorems, and compares
native Lean evaluations with the independent Python predicates. Its results go
to [lean-checks.json](../results/lean-checks.json). The second checks the new
executable border/rank definitions; these finite native comparisons are not the
proof of the all-word statements.

To build or inspect the earlier axioms directly, run these commands from `lean/`:

```sh
lake build
lake env leanchecker --verbose Subtail
lake env lean Subtail/Audit.lean
```

The new modules are included by `Subtail.lean`. Their complete public dependency
audits are separately enforced by
[the foundation workflow](../.github/workflows/lean-rank-foundation.yml) and
[the milestone workflow](../.github/workflows/lean-rank-milestones.yml); the
latter audits every public definition/theorem in `RankMilestones.lean`.

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
| [Audit.lean](Subtail/Audit.lean) | Dependency-axiom reports for the earlier runtime definitions and main theorems |
| [TerminalRank.lean](Subtail/TerminalRank.lean) | Terminal prefix-freeness, border-state injection and at most k-1 positive borders of accepted suffixes |
| [RankMilestones.lean](Subtail/RankMilestones.lean) | Literal rank recurrence, reversal and actual reversed-prefix bound; exact first milestones/first returns; interior failure-target confinement |

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

The direct sufficient predicate is implemented and proved sound for an
individual word. The earlier finite-budget interface is still conditional:
its exact language nonemptiness test and concrete covering bound have not been
instantiated in Lean. The new rank-route formalization does not silently
discharge those parameters.

For the current candidate, first-return successor/KMP graph identities and
colours, finite observer/diagram syntax, both uniform preimage directions,
quantitative repeated closure and the executable global witness bound remain
unformalized. Arbitrary-tree semantics, normalization, and the subtype reduction
also remain outside this Lean core. See the
[precise milestone readback and handoff](../notes/2026-09-18-lean-rank-milestones.md).
The proved rank bound is not a word-length or source-visit bound.

The current binary formalization does not claim results for every finite
alphabet. The general statements in the research notes retain their separate
written-proof status.

## Proof and computation boundaries

The named proof dependencies use only Lean's standard `propext`, `Quot.sound`,
and, for some list/truncation proofs, `Classical.choice`. The checked runtime
definitions do not depend on classical choice. Several use `propext` in
erased library proofs. No custom axiom or `sorryAx` discharges a research gap.
The audits cover the named declarations and their transitive dependencies;
new independent theorems must be included in the relevant audit. In the new
milestone module, `rank`, `failureParent`, `maxNat`, `FirstMilestone` and
`FirstReturn` have no axiom dependencies in the recorded execution.

The native evaluation comparisons are regression tests, separate from the
kernel-checked theorem proofs. `leanchecker` replays declarations through
Lean's own kernel; it is not an independent external proof checker. Read the
[formalization note](../notes/2026-09-04-lean-core.md),
[terminal foundation note](../notes/2026-09-18-lean-rank-foundation.md), and the
[A018 obligations and current history](../research/approaches/A018.md) before
extending the core. The new statements were read back by their author; no
independent human semantic review is claimed.
