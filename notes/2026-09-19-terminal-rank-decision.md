# Terminal rank-query decision: proof and readback

Date: 2026-09-19. A018/C080, issue #30; integration coordinated in #37.
Actor: Codex Astra `terminal-decision-20260919`.
Base: `a7c29093fcbdfc9c2a3dc58aeefc4547770542c2`.
Proof checkpoint: `9b359f7d7f23e051b7d81fd1a0b8a7b6e572e8d0`.

## Result and exact scope

`RankQueryDecision.terminalWitnessCheck_correct` proves, for every finite binary
instance `I : Instance k`,

```lean
TerminalFinals I →
  (terminalWitnessCheck I = true ↔ ∃ w : Word, Witness I w)
```

`TerminalFinals` means that each accepting state has no outgoing transition on
either letter. `Witness` is the original predicate in `Basic.lean`: a defined
accepting run, no Bad cut state, and no ordered flagged pair at any agreement
of suffixes. Empty suffixes, diagonals, and the initial cut remain included.

This is a total executable decision for terminal BorderAvoid for arbitrary k.
The same module proves the previously pinned `RankDecisionStatement` with
`preimage I RankQueryCoverage.budget`. Neither theorem assumes a witness
length bound, the clause-weight contract in `ClosureFor`, or the formula F(k).
The theorem is not a subtype-entailment result. The effective construction
and correctness of the arbitrary-tree C029/C031 reduction remain #31.

The initial route outline was written before implementation, working both
backwards from the decision schema and forwards from the existing semantic
closure. Its six obligations—witness lifting, rank-chain coverage, finishing,
semantic unwind, converse witness reconstruction and executable finite
enumeration—are all discharged for the terminal theorem. No word is shortened
and no preservation of newly created borders is assumed.

## Ordinary proof

1. A nonempty original witness w defines a reversed reference C:
   `C.word = w.reverse` and `C.label j = cutState I I.initial w (|w|-j)`.
   Its zero label is accepting, its last label is initial, its adjacent labels
   follow the original transitions backwards, and its mask exclusions are
   exactly the original ordered agreement checks. Positive prefixes inherit
   safety. `RankWitnessReference` proves these implications without terminality.
2. Terminality bounds the literal positive-border rank of every prefix of C by
   k-1. Choose the maximum attained rank H over **all** prefixes. Nonemptiness
   gives H ≥ 1. Choosing the rank of the complete word instead would be wrong:
   for example rank can fall from `000` to `0001`.
3. The first rank-one milestone is position 1. Consecutive first milestones
   are literal first returns. Restricting C at these positions gives safe
   labelled `FirstReturnExt` steps, including overlapping returns. A chain to
   the first rank-H milestone has exactly H-1 ≤ k-2 steps.
4. The remaining completion cannot return to that maximal milestone, including
   at the ultimate cut. `maximal_rank_completion_finishes` therefore supplies
   the finishing query there. Empty completion is allowed. This uses the
   original endpoint condition `C.label |C| = I.initial`.
5. The concrete semantic promotion-unwind theorem moves that query down the
   finite chain. The one-letter prefix and `oneLetter` need not agree on labels
   beyond their endpoints. Bounded label equality, through position 1, suffices
   for safe-reference and prefix-graph congruence.
6. Conversely, satisfaction of the promoted query gives a safe finite chain
   and a final finishing query. `finish_implies_witness` reconstructs a word
   satisfying the original predicate. This soundness direction does not need
   terminality. The empty witness is checked separately.

H=1 gives zero promotions. The inequalities rule out a nonempty terminal
witness for k<2; no fabricated one-letter witness is used in that case.
`Instance 0` itself has no value because its initial state would lie in Fin 0.

## Executability and limits

`terminalWitnessCheck` tests the empty word, enumerates the two letters and
the k² initial/final label pairs, checks safety at the finite physical
positions, and evaluates the promoted finishing query. The compiler iterates
exactly k-2 times. Each preimage is a finite `flatMap` over the explicit
diagram enumeration at the computed coverage budget; query satisfaction is
finite graph reachability. All runtime dependencies pass the axiom audit
without `Classical.choice`. The proof uses ordinary classical reasoning only
in erased propositions; it does not manufacture a noncomputable decision.

This is a mathematical termination and correctness result, not a practical
complexity result. Native whole-decision regressions cover k≤2, where no
promotion is needed. Larger-state whole-preimage evaluation was NOT RUN;
the exhaustive compiler may be impractical. Existing native compiler and
query differentials remain separate evidence for their components.
The explicit U/F estimates remain open.

## Review and provenance

The five finishing source/evidence files are unchanged from released commit
`098a0bdc60c393ee10737ae42aec6dce2cc4186b`; its standalone workflow is not restored.
The witness-reference module is unchanged from worker commit
`9f453dec00d59d7f3a856114f99233a8151d2dad`.

A separate read-only Astra context, `finishing_review`, checked the released
finishing modules, independently checked the ordinary milestone assembly
plan, and then read the complete Decision and WitnessReference declarations
at proof checkpoint `9b359f7`. It reported no mathematical or semantic defect.
It checked empty and small-state cases, maximum-prefix selection, exact chain
length, graph transport restricted to physical labels, directed flags, the
original witness equivalence and the finite runtime path. It inherited the
parent context and was not a blind derivation or human referee. It did not
re-audit the large imported coverage proof. The parent independently checked
the worker's reversed-run construction and ordered flag mapping.

The worker had a separate worktree and released its only owned path in
[the handoff](https://github.com/mhenglein/subtail/issues/30#issuecomment-5739062358).
The parent is the single integrator; no worker wrote main.

## Reproduction and workbench evidence

Run on wb-marcus using Lean 4.33.1 and Python 3.13.14:

```sh
cd lean
lake build
lake env leanchecker Subtail
lake env leanchecker Subtail.RankQueryDecision
cd ..
python3 scripts/check_lean.py
python3 scripts/check_rank_decision.py
python3 experiments/check_terminal_decision.py
python3 experiments/check_finishing_trace.py --lean
python3 experiments/run_experiments.py
python3 scripts/research_index.py --check
```

The new default imports compile together (37 build jobs). Decision kernel replay
passes. The audit covers 88 named declarations, including finishing constructors
and runtime definitions. The full earlier Lean core passes with its saved
result unchanged. Its combined-tree check took 100.272 seconds.

The independent literal Python oracle and two native Lean checks agree on all
12,820 one/two-state terminal inputs: 341 YES, 12,479 NO, all partial transitions,
final sets, Bad sets, ordered flags and initial states. The short oracle is
complete in this scope by the existing `TwoState` theorem; bounded failure is
not promoted to NO outside this scope. The native run took 66.656 seconds.
[Compact result](../results/terminal-decision-regressions.json).

The finishing differential agrees on 180 cases, with 92 YES witness
reconstructions and 88 fixed-reference no-return NO results. Compact and full
outputs replay byte-for-byte with a different Python hash seed. A required-return
fixture distinguishes arbitrary completion from no-return finishing.
[Preserved finishing evidence](../results/finishing-trace-semantics.json).

The real remote lean-lsp-mcp was used for current-file diagnostics, goals,
declaration lookup and isolated tactic trials. The final assembly goal read took
1.627 seconds; two tactic trials took 2.434 seconds. One failed simplification
trial exposed the residual `n ≤ n` goal; an explicit reflexivity proof succeeded.
The fresh final target build took 1.169 seconds and kernel replay 1.249 seconds.
These are observed times, not a controlled comparison with the old setup.
No native remote Codex task activation was tested; this route uses SSH plus the
configured remote MCP process.

Exact source hashes and compact check outcomes are in
[terminal-decision-proof.json](../results/terminal-decision-proof.json).
Consolidated Lean CI runs the new audits and regressions without a new workflow.

## Next question

Construct an effective family of terminal instances from a normalized subtype
input, and prove both directions of the original entailment/non-entailment
correspondence over arbitrary, possibly infinite trees. Preserve the
ordered-cut and absorption cases and state any remaining finite-summary
obligations explicitly. Do not replace that bridge with a regular-tree-only
theorem. The terminal result supplies its decision backend; it does not prove
the bridge or settle Problem 1.7.

No opposing-route encoding is refuted for a different fragment. Within the
exact terminal BorderAvoid definition, an undecidability claim would conflict
with the checked theorem and must identify a semantic mismatch.
