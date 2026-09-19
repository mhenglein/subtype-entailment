# Corrected quantitative bound: reviewed integration

Date: 2026-09-20. Integrator: post-c081-20260919. A017/A018, C080/C082,
Q004; coordination #53/#37/#30 and source PR #48.

## Result and exact scope

The concrete compiler's old universal weight contract is false. A separate,
larger weight bound and terminal small-witness theorem are now kernel checked
and independently read back. They do not alter the qualitative C081 decision.
The original numerical F and an existentially chosen smaller compiler remain
separate questions. [C080 correction](../research/claims.md#c080),
[C082 exact statement](../research/claims.md#c082).

For k>=1 put T_0=k+10, T_(j+1)=64*k*T_j^(6*T_j^2+2). The corrected bound is

```text
Fhat(1)=0;
Fhat(k)=2*(k+1)*product_(j=1..k-2)(T_j+2), k>=2.
```

Every positive binary terminal k-state instance has some original Witness
of length at most Fhat(k). There is no caller weight-contract, SAT or bound
hypothesis. The runtime `witnessBound 0` is 2; `Instance 0` has no initial state,
so the zero-state instance theorem is vacuous. This is a bound on words, not
a bound on running the current query enumerator.

## Why the replacement works

The old calculation did not charge enough simultaneous observer coordinates
across the whole conjunction. Repeated occurrences still contribute to the
concrete output. The checked five-state chain has input clause weight 17 and
an emitted clause of weight `12+30*2^175 > 320*17^36`: five observer occurrences,
35 selected forward/wrap pairs and 175 coordinates. Membership, the actual
budget, terminality and the inequality are proved without evaluating the huge
observer or the full enumerator. This refutes the universal old size conjunct
for that concrete compiler even if a smaller equivalent query might exist.

`RankQueryWeightBound` bounds all active coordinates and observer products in
every structurally bounded emitted diagram. Its `compileValid_weight_le`
needs only structural boundedness. The new bound is `64*k*T^(6*T^2+2)`;
`preimage_clause_weight_le` and `weight_promote_finish_le` give the recurrence.
The construction and source enumeration are unchanged.

`RankQueryLengthBound.compile_bounded` chooses repetition-free paths in the
joint interval observer. It retains the common assignment, every boundary
control and every observation, so the reconstructed extension is still safe
and satisfies the entire query. Its length plus one is bounded by
`(B.len+1)*(clauseWeight P+2)`. Iterating this estimate through at most k-2
promotions, starting from a one-letter reference, gives the product above;
finishing contributes the factor k+1. The one-state case has only the empty
witness. `terminal_witness_bound_iff` combines this construction with the
already checked terminal decision. No new global shortening assumption occurs.

The [author's detailed proof note](2026-09-19-rank-weight-native.md) and
[independent ordinary source readback](2026-09-20-c080-quantitative-independent-readback.md)
record the exact declarations and proof obligations. The latter is a separate
session's source review, not a blind derivation or human peer review.

## Provenance and integration choices

- Original proof source: `0b5d9de57a36591f3fd7cb38940afde3c7f9500b`.
- Released PR #48 publication: `881d4beeb903d679d7d36a8a9abc2aa0efa60a52`.
- Independent readback: `01bd5ae89d9020d97dd7e539b87df49c3c2e3133`.
- Combined checked revision: `7525724b3c86b6a9dbe0a7f62b062a9b8697a97c`.

The three new Lean modules, driver, author note and historical JSON are copied
byte-for-byte from the released publication. The original separate workflow
is preserved at that immutable source. Its build, kernel and dependency check
is instead a bounded step in the existing Lean workflow, sharing its build
cache. The new modules are optional imports and are built explicitly by the
driver; `Subtail.lean`, all existing definitions, toolchain and paper source
pins remain unchanged. This avoids a duplicate full CI job.

## Fresh combined validation

Execution host: wb-marcus. Isolated checkout:
`/home/marcus/workspaces/subtail-worktrees/post-c081-quantitative-20260920`.
Lean 4.33.1, one Lean thread, stack 32768 KiB. Each command has a separate
process group, 16 GiB address-space cap and 1200-second CPU cap; wall caps
are recorded below. A limit would yield UNKNOWN, never a negative theorem.

The build cache was copied from a clean C081 checkout only after comparing
all 53 baseline source hashes with `c946d86`. No shared active build was used.

| Command from repository root | Result | Seconds | Wall cap |
|---|---|---:|---:|
| `python3 scripts/check_rank_weight_native.py` | PASS | 18.816 | 1000 |
| `python3 scripts/check_lean.py` | PASS | 141.563 | 1000 |
| `python3 scripts/check_entailment_decision.py --output tmp/entailment-axioms.json` | PASS | 0.768 | 600 |
| `git diff --exit-code` | PASS | 0.117 | 60 |

The quantitative driver builds all three modules with code generation, replays
each through `leanchecker`, and audits 87 declarations. Proof dependencies use
only the standard axioms; no new runtime def/abbrev depends on classical
choice. The default core build/kernel/regression check and final entailment
audit pass on the same combined checkout. The retained driver report's
`independent_mathematical_review: false` correctly describes that automated
run; the separate linked source review supplies the human-readable audit.

[Fresh complete audit](../results/rank-weight-integration.json),
[historical source audit](../results/rank-weight-native.json). No full diagram
enumeration, large observer materialization or new performance benchmark ran.
Documentation-only changes after the checked revision retain these source
hashes; publication and CI readback are separately recorded in #53/#37.

## Dependency correction and implications

The original `RankQueryUnwind` results are still valid under their explicit
`ClosureFor` hypothesis. The concrete old weight conjunct cannot instantiate
that hypothesis. `RankQuerySemanticUnwind`, `RankQueryCoverage.closure_iff`,
`RankQueryDecision` and C081 use semantic closure without that size conjunct;
the fresh default build and entailment audit preserve this distinction.
The old ordinary proofs and favourable reviews receive correction banners;
their unqualified size conclusions are withdrawn, not their valid semantic
lemmas. This audit covers those known entry points and the checked default
C081 dependency graph; it is not a line-by-line review of every old note.

For Q004, take `R(0)=0` and `R(k)=Fhat(k)+1` for k>=1: a word of length l has
l+1 run positions, so source visits cannot exceed that number. This ordinary
corollary now has an explicit formula, but no new Lean source-visit declaration.
The former finite-classification proof remains useful independent history.

The best next quantitative question is original-input resource accounting for
a specified algorithm, then a smaller effective bound or better representation.
C082 supplies neither the old F nor an efficient solver by itself. Other
constructors, finite-tree entailment and exact lower-bound transfers remain
separate obligations.
