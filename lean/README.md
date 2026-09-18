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
python3 experiments/check_lean_first_return_graph.py --repository --lean --output /tmp/first-return-graph.json
python3 experiments/check_rank_query_first_return.py --lean --output /tmp/query-first-return.json
```

The first command builds the project, replays the compiled declarations with
`leanchecker`, audits the earlier named algorithms and theorems, and compares
native Lean evaluations with the independent Python predicates. Its results go
to [lean-checks.json](../results/lean-checks.json). The remaining checks exercise
the executable border/rank, graph and interval definitions; these finite native
comparisons are not the proof of the all-word statements.

To build or inspect the earlier axioms directly, run these commands from `lean/`:

```sh
lake build
lake env leanchecker --verbose Subtail
lake env lean Subtail/Audit.lean
```

The new modules are included by `Subtail.lean`. Their complete public dependency
audits are separately enforced by
[the foundation workflow](../.github/workflows/lean-rank-foundation.yml),
[the milestone workflow](../.github/workflows/lean-rank-milestones.yml),
[the query workflow](../.github/workflows/lean-rank-query.yml), and
[the graph/interface workflow](../.github/workflows/lean-first-return-graph.yml).
The latter audits all 65 public declarations of the four graph modules and
`RankQueryFirstReturn.lean` at the checked revision.

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
| [RankQuery.lean](Subtail/RankQuery.lean) | Stage 4a: query grammar, literal prefix graphs, executable `satCheck` with `satCheck_correct`, and the UNPROVED `ClosureStatement`/`RankDecisionStatement` pinned as `Prop`s |
| [RankQueryPaths.lean](Subtail/RankQueryPaths.lean) | Stage 4b ingredient: runs are chains of nodes, every accepted run has a repetition-free chain, and such a chain visits any vertex at most `O.size` times (`accepts_bounded_visits`) |
| [PrefixMatching.lean](Subtail/PrefixMatching.lean), [FirstReturnGraph.lean](Subtail/FirstReturnGraph.lean) | Literal KMP maximum/fallback and the exact first-return cursor and K-edge identities |
| [FirstReturnGenerator.lean](Subtail/FirstReturnGenerator.lean), [FirstReturnColours.lean](Subtail/FirstReturnColours.lean) | First-hit iff literal first return; complete colour/mask and F/S/K0/K1 graph equality |
| [RankQueryFirstReturn.lean](Subtail/RankQueryFirstReturn.lean) | Graph construction transferred to the actual query graph; single entrance, fresh-edge shape, and at most `O.size+1` maximal forward fresh intervals of a product-simple accepted path |
| [TreeSemantics.lean](Subtail/TreeSemantics.lean), [CanonicalModel.lean](Subtail/CanonicalModel.lean), [CanonicalModelAudit.lean](Subtail/CanonicalModelAudit.lean) | Stage 6 foundation: arbitrary prefix-closed path-set trees, the four normalized constraint forms, inductive propagation closure, `satisfiable_iff_forced_safe`, `not_entails_iff_canonical`, and all-length semantic regression proofs |
| [StackSummary.lean](Subtail/StackSummary.lean), [StackReachability.lean](Subtail/StackReachability.lean), [CanonicalReachability.lean](Subtail/CanonicalReachability.lean), [StackSummaryAudit.lean](Subtail/StackSummaryAudit.lean) | Stage 6 second layer: balanced excursions, minimum-stack normal form (`reaches_iff_normal`), executable exact reachability, `derived_iff_reaches`, total `satCheck_correct`, supplied-address `separationCheck_iff_countermodel`; entailment NOT decided |

Words are `List Bool`. State sets have type `Fin k`; tables are finite vectors.
The flag condition includes both diagonal pairs and the empty suffix. A
missing transition rejects the word. Flags mean forbidden pairs.

The visited-state rule shortens `0010` to `00` in a two-state instance where
C009's all-state condition fails. This example and its distinction from C009
are checked in Lean. The finer exact-occurrence rule has a written proof and
Python checks, but is not yet formalized.

## What remains assumed or missing

`RankQuery.lean` pins `ClosureFor`, `ClosureStatement` and `RankDecisionStatement`
as statements only. No theorem in the repository proves them. Its literal graph
and observer semantics are now default-imported through the checked
first-return query interface. See
[the statement readback](../notes/2026-09-18-lean-rank-query-statement.md) and
[the exact graph/interval handoff](../notes/2026-09-18-lean-first-return-graph.md).

`finiteBudgetDecision_correct` accepts executable parameters `size`, `F`, and
`success`. Its statement assumes:

1. Every successful fixed-budget test yields a witness.
2. Every instance with a witness has a successful budget within `F(size I)`.

The direct sufficient predicate is implemented and proved sound for an
individual word. The earlier finite-budget interface is still conditional:
its exact language nonemptiness test and concrete covering bound have not been
instantiated in Lean. The new rank-route formalization does not silently
discharge those parameters.

For the current candidate, the first-return graph and bounded fresh-interval
interface are checked. What remains is the executable marked-diagram enumerator
and coverage proof, the shared-interval product and both uniform preimage
directions, quantitative repeated closure, and the executable global witness
bound. Arbitrary-tree semantics, normalization, and the subtype reduction also
remain outside this integrated Lean core. Other agents' reserved semantic
work is tracked separately; no unintegrated work is claimed here.
The proved rank and interval bounds are not word-length or source-visit bounds.

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
`FirstReturn` have no axiom dependencies in the recorded execution. The new
`breaksAfter` and `freshIntervals` also have no axiom dependencies.

The native evaluation comparisons are regression tests, separate from the
kernel-checked theorem proofs. `leanchecker` replays declarations through
Lean's own kernel; it is not an independent external proof checker. Read the
[formalization note](../notes/2026-09-04-lean-core.md),
[terminal foundation note](../notes/2026-09-18-lean-rank-foundation.md), and the
[A018 obligations and current history](../research/approaches/A018.md) before
extending the core. The new statements were read back by their author; no
independent human semantic review is claimed.
