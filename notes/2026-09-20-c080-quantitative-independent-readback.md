# Independent C080 quantitative Lean readback

**Later September 20 result.** [C086](../research/claims.md#c086) proves the original terminal
F and the original U contract for a different, filtered compiler. The old
unfiltered compiler counterexample remains valid, and C082 remains a valid
larger bound. The dated argument and earlier open status below are preserved
as history, not the current C086 status.

Date: 2026-09-20
Reviewer: independent non-author successor reviewer for issue #53
Scope: PR #48's released quantitative proof source and its terminal witness
bound

## Evidence and review boundary

I read the proof-source checkpoint
[`0b5d9de`](https://github.com/mhenglein/subtail/commit/0b5d9de57a36591f3fd7cb38940afde3c7f9500b),
the publication head
[`881d4be`](https://github.com/mhenglein/subtail/commit/881d4beeb903d679d7d36a8a9abc2aa0efa60a52),
the ordinary author note
[`rank-weight-native.md`](https://github.com/mhenglein/subtail/blob/881d4beeb903d679d7d36a8a9abc2aa0efa60a52/notes/2026-09-19-rank-weight-native.md),
and the current main source checkpoint `c946d86`. The three imported source
modules used by the new files are byte-identical between the proof checkpoint
and current main; the three new quantitative modules are only on PR #48.
The new-module SHA-256 values at `0b5d9de` are:

```text
RankQueryWeightCounterexample.lean d3e2ebbe27bdc277f8080e5e75f8d8939784d670e396e52e69aac631681a68ce
RankQueryWeightBound.lean         d92069dfe5de891ba9bcfe3c5599a6a5e726fd57e2995f87a3b569fa0daabe50
RankQueryLengthBound.lean         daec0fabc8c8e8b5c9ff5b1078a110f2fddf48ef60d3cbfec04557261a794399
```

The recorded native workflow run `35452368681` reports a pinned Lean 4.33.1
build, separate `leanchecker` replay, and the transitive axiom audit at the
proof-source checkpoint. This review did not rerun that build, the full
enumerator, or the large searches. PR #48 has no human review entries; its
automated review attempt reported a usage limit. The conclusions below are a
source and statement readback, not a fresh kernel certificate.

The exact C080 record remains the proposed old claim in
[`research/claims.md#c080`](../research/claims.md#c080): its original
`U_k(T)=64*k*T^(2*T+2)` and its original `F(k)` are still open. This review
checks the separate replacement result in PR #48 and does not promote C080.

## The old-U counterexample

`RankQueryWeightCounterexample.terminal_counterexample` proves

```lean
∃ I : Instance 5, TerminalRank.TerminalFinals I ∧
  ¬ ClosureFor I (preimage I RankQueryCoverage.budget)
```

The instance has five states, initial state 4, only the chain
`4 -1-> 3 -0-> 2 -1-> 1 -0-> 0`, final state 0, and no bad states or flags.
The accepting state is terminal, and `original_witness` checks `1010` against
the unchanged `Basic.Witness` predicate.

The clause has one variable and five repeated occurrences of one two-control
observer. The diagram has two groups and repeats a valid forward/wrap pair 35
times for every occurrence. The module proves `Bounded`, `validDiagram = true`,
exact active-coordinate count 175, and exact output membership through
`mem_preimageClause`; it never evaluates the astronomical diagram list or
interval product. It then proves

```text
clauseWeight output = 12 + 30*2^175
closureBound 5 (weight [input]) < clauseWeight output
```

The contradiction uses only the second, universal weight conjunct of
`ClosureFor`. It therefore refutes the old bound for the current concrete
enumerator. It does not refute `ClosureStatement`, which existentially chooses
a preimage map; it does not refute the old numerical `F(k)` statement; and it
does not affect the qualitative terminal decision.

## Corrected weight theorem for the unchanged compiler

`RankQueryWeightBound.improvedBound` defines

```text
Uhat_k(T) = 64*k*T^(6*T^2+2).
```

The central endpoint is:

```lean
compileValid_weight_le (I : Instance k) (c : Clause k) (D : Diagram k)
  (hb : Bounded c (RankQueryCoverage.budget c) D) :
  clauseWeight (compileValid I c D) ≤ improvedBound k (clauseWeight c)
```

and the actual-enumerator endpoint is:

```lean
preimage_clause_weight_le (I : Instance k) (phi : Query k) (out : Clause k)
  (hout : out ∈ preimage I RankQueryCoverage.budget phi) :
  clauseWeight out ≤ improvedBound k (weight phi)
```

The first theorem needs only the structural `Bounded` premise. The second gets
that premise and a successful `compileDiagram` from exact preimage membership.
Neither theorem assumes satisfaction, a safe reference, terminality,
product-simplicity, `ClosureFor`, or a hidden normalization. The proof counts
repeated piece occurrences in the actual oversized diagram envelope. It uses
the exact interval cardinality

```text
6*k*product(observer sizes of the active occurrences)
```

and the budget facts `groups <= 2*T`, `coreVars <= T + 6*T^2`, and total piece
occurrences `<= 6*T^2`, where `T = clauseWeight c`. This is the right universal
quantifier for the concrete `preimage`: an existentially small product-simple
diagram would not have been enough.

The module also proves the executable recurrence for the actual concrete map:

```lean
weightBudget k 0       = k + 10
weightBudget k (h + 1)  = improvedBound k (weightBudget k h)

weight_promote_finish_le (I : Instance k) :
  ∀ h, weight (promote (preimage I RankQueryCoverage.budget)
    (finishQuery I) h) ≤ weightBudget k h
```

This recurrence is not obtained by falsely reusing the old conditional
`RankQueryUnwind.weight_promote_finish_le`, whose `ClosureFor` premise contains
the invalid old `closureBound`. It is proved directly from the pointwise bound,
query maximum, monotonicity, and the finishing-query base weight.

## Bounded reconstruction and the terminal endpoint

`RankQueryLengthBound.compile_bounded` is the key size-preserving theorem:

```lean
compile_bounded (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k)
  (hB : SafeReference I B) {P : Clause k}
  (hP : compileDiagram I c D = some P)
  (hsat : SatClause (prefixGraph I B) P) :
  ∃ C, FirstReturnExt I B C ∧ SatClause (prefixGraph I C) c ∧
    C.word.length + 1 ≤ (B.word.length + 1) * (clauseWeight P + 2)
```

The construction keeps the model's common vertex assignment and all boundary
controls. For each physical interval it replaces the accepting product path by
a repetition-free path with the same endpoints. `RankQueryPaths` supplies the
finite product bound: an observer of size `s` over a graph with `N` vertices
has a path with at most `N*s-1` edges. `interval_trace_bounded` translates that
path back to the existing `Gen` relation, including state, next-marker, seen,
and every observer control. `exists_bounded_recon` replaces only interval
traces, and the existing `Recon` lemmas reassemble the same tests, equalities,
disequalities, all path atoms, safety, and first-return condition.

`preimage_bounded` lifts the theorem through exact membership in the concrete
preimage and `preimage_clause_weight_le`. `finish_bounded` applies the same
product-path argument to the existing finishing observer and then uses
`RankQueryFinishTrace.safe_reference_witness` to return to the original
`Basic.Witness` predicate. It proves

```text
w.length + 1 <= (B.word.length + 1)*(k+1).
```

`promoted_finish_bounded` iterates this bound over the actual finite preimage.
It has no `ClosureFor` or numerical-bound premise:

```lean
∀ h B, SafeReference I B →
  Sat (prefixGraph I B)
    (promote (preimage I RankQueryCoverage.budget) (finishQuery I) h) →
  ∃ w, Witness I w ∧
    w.length + 1 <= (B.word.length + 1)*(k+1)*growth k h
```

where

```text
growth k 0       = 1
growth k (h + 1) = (weightBudget k (h + 1) + 2)*growth k h.
```

The final endpoint is:

```lean
terminal_witness_bound_iff (I : Instance k)
  (ht : TerminalRank.TerminalFinals I) :
  (∃ w, Witness I w) ↔
    ∃ w, Witness I w ∧ w.length ≤ witnessBound k
```

with

```text
witnessBound(1) = 0
witnessBound(k) = 2*(k+1)*growth k (k-2), k >= 2.
```

The only extra hypothesis at this final endpoint is the explicit
`TerminalFinals I` assumption. The proof uses the already checked
`RankQueryDecision.rankDecisionStatement`, which reduces a nonempty witness to
a safe one-letter reference satisfying the concrete promoted finishing query
after at most `k-2` promotions. The rank bound comes from terminality. The
empty witness and the one-state case are handled separately. The intermediate
semantic equivalence is `RankQueryCoverage.closure_iff`, proved for the actual
enumerator by the checked finite coverage theorem; the new length proof does
not assume the old quantitative `ClosureFor` contract.

Thus, at the exact proof checkpoint, this is a genuine unconditional
**terminal-instance existence bound** under the repository's classical Lean
logic. It is not an assumption that still needs to be supplied. It is also not
the original C080 bound: it uses `Uhat` and `Fhat`, not `U` and `F`.

## Classical logic and executability

The recorded audit allows only `propext`, `Quot.sound`, and `Classical.choice`.
It reports that all new runtime definitions are choice-free. In particular,
`improvedBound`, `weightBudget`, `growth`, `witnessBound`, and the finite
counterexample/compiler data are executable structural definitions.

Some proof declarations depend on `Classical.choice`. The relevant uses are in
the existing coverage/reconstruction proofs that choose one accepting path per
finite interval and assemble existential `Recon` data. They live in `Prop` and
are used to prove existence; they are not definitions used by the runtime
checker. This is acceptable for the stated theorem, but a constructive proof
or proof-extraction claim would need a separate review.

The PR does not add a bounded terminal enumerator whose fuel is `witnessBound`,
nor a theorem connecting such a new executable to `terminalWitnessCheck`. The
length theorem would support deriving that finite search in a later module
using `witnessCheck_correct`, but that integration and its resource accounting
remain open. The existing qualitative `terminalWitnessCheck` is already total
and correct without this bound.

## Verdict, accepted claims, and limits

**Accepted at statement/readback confidence:**

* The five-state fixture refutes the old universal weight conjunct for the
  current concrete preimage.
* `preimage_clause_weight_le` is a universal corrected bound for every emitted
  clause of that unchanged compiler.
* `terminal_witness_bound_iff` proves a corrected explicit `Fhat` for every
  terminal `Instance k`, with no unproved `ClosureFor`, witness-bound, or
  satisfaction premise beyond the theorem's stated existence and terminality
  hypotheses.
* The source proof depends one-way on the existing qualitative terminal
  decision; the qualitative decider does not depend on this quantitative PR.

**Still open or outside scope:**

* The original C080 `U` and `F` remain unproved and the old `ClosureFor`
  declaration remains unchanged.
* PR #48 is not merged into current main, so the corrected theorem is not part
  of the integrated C081 source checkpoint.
* No complete C081 input-size or complexity theorem follows: `k` is the state
  count of a supplied terminal instance, and normalization, summary
  construction, the infinite branch, and subtype composition are separate.
* No practical runtime or storage bound follows from `clauseWeight`; the
  grammar contains finite function/table fields that this metric does not
  charge.
* No bounded-terminal executable or performance claim is supplied by these
  declarations.

Status: `READY_FOR_INTEGRATION` after this independent readback. All Lean
modules, workflows, ledgers, paper files, and main remain read-only for this
session.
