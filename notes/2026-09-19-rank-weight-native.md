# Native quantitative follow-up: counterexample, corrected closure size, and witness bound

Date: 2026-09-19. A017/A018, C080; issues #30, #34, #37.
Author/session: ChatGPT `rank-weight-native-20260919`, continuing its own
advisory investigation. This is not a non-author mathematical review.

**Result: all three requested quantitative stages are proved and kernel-checked
on the unchanged concrete compiler.** The original concrete U contract is
refuted natively; a separate larger bound is proved; bounded shared-interval
reconstruction and the resulting explicit terminal witness bound are proved.
No existing compiler, definition, theorem signature, production import,
qualitative decider, toolchain, shared ledger or existing workflow was changed.

Proof-source checkpoint: **`0b5d9de57a36591f3fd7cb38940afde3c7f9500b`**.
Base: `3ce7cf18899ad24a5562d4b614f738bec8bc8427`.
Branch: `lean/rank-weight-native-20260919`.
Contribution: [PR #48](https://github.com/mhenglein/subtail/pull/48), not merged
by this session. The final documentation/result commit preserves the checked
proof, driver and workflow blobs unchanged.

Prior ordinary counterexample and route: [PR #47](https://github.com/mhenglein/subtail/pull/47),
[full report at its immutable checkpoint](https://github.com/mhenglein/subtail/blob/42be43f35a98d4d23a4ba26439833730bbcd6510/notes/2026-09-19-rank-query-weight-counterexample.md).
That record and its failed-bound history remain preserved, not overwritten.

## 1. Exact results and their limits

### Native counterexample

Module: [RankQueryWeightCounterexample.lean](../lean/Subtail/RankQueryWeightCounterexample.lean).
Namespace: `Subtail.RankQueryWeightCounterexample`.

The principal theorem is:

```lean
terminal_counterexample :
  ∃ I : Instance 5, TerminalRank.TerminalFinals I ∧
    ¬ ClosureFor I (preimage I RankQueryCoverage.budget)
```

The concrete fixture is the terminal chain accepting 1010, with initial state 4,
final state 0, no Bad states or flags, and only these transitions:

```text
4 --1--> 3 --0--> 2 --1--> 1 --0--> 0
```

The input clause declares one vertex variable and five occurrences of a path
atom whose observer has two controls, initial/final control 0, allows every
colour, and permits both target controls on every label. Its weight is 17.
The diagram has two fresh groups, no core variables, states [3,4], next markers
[1,END], first bit 0, the old endpoint colour of state 2, and an empty seam list.
Each atom's path diagram repeats the forward 0-to-1 / wrap 1-to-0 pair 35 times.
The wrap label is K0; all piece boundary controls are 0.

The native module proves terminality, an original Witness 1010, exact input
weight, exact syntax budget (groups 33, core 351, perAtom 70, seamEntries 1155,
scalar 470), original Bounded, original validDiagram, 175 active coordinates,
interval size 30*2^175, four output variables, three output atoms, and

```text
clauseWeight output = 12 + 30*2^175
closureBound 5 (weight [input]) < clauseWeight output
```

`output_mem` proves membership in the ACTUAL preimage using
`mem_preimageClause`; it does not evaluate the astronomical diagram list.
`not_closureFor` contradicts the second conjunct of the unchanged ClosureFor.
All finite reductions use `decide +kernel`, never native_decide or a compiled
proof oracle. Only structural size projections are reduced; neither the full
enumerator nor the large interval control lists are materialized.

The native refutation needs no satisfaction premise because the original weight
conjunct quantifies over every emitted clause. The satisfying shared-reference
model from PR #47 remains an ordinary proof; this module does not additionally
prove satisfaction of that enormous compiled clause in Lean. It does prove the
original length-four witness of the terminal instance.

This refutes the concrete map's original weight contract. It does NOT refute
semantic closure, the existentially chosen map in ClosureStatement, or the old
F(k) witness statement itself. The counterexample instance has a short witness.

### Corrected universal clause-weight bound

Module: [RankQueryWeightBound.lean](../lean/Subtail/RankQueryWeightBound.lean).
Namespace: `Subtail.RankQueryWeightBound`.

```lean
def improvedBound (k T : Nat) : Nat := 64 * k * T ^ (6 * T ^ 2 + 2)

compileValid_weight_le (I : Instance k) (c : Clause k) (D : Diagram k)
  (hb : Bounded c (RankQueryCoverage.budget c) D) :
  clauseWeight (compileValid I c D) ≤ improvedBound k (clauseWeight c)

preimage_clause_weight_le (I : Instance k) (phi : Query k) (out : Clause k)
  (hout : out ∈ preimage I RankQueryCoverage.budget phi) :
  clauseWeight out ≤ improvedBound k (weight phi)
```

The first theorem is stronger than required: it needs Bounded but no validity,
satisfaction, safe-reference, terminality or product-simplicity assumption.
The second theorem is the pointwise contract for the actual emitted union.
`weight_preimage_le` bounds its maximum clause weight. These are separate
declarations; closureBound and ClosureFor keep their original meanings.

The module also proves monotonicity, domination on k>0 and T>=2, and the
unconditional promoted-query recurrence for this concrete compiler:

```text
weightBudget k 0       = k+10
weightBudget k (h+1)   = improvedBound k (weightBudget k h)
weight_promote_finish_le:
  weight (promote (preimage I RankQueryCoverage.budget) (finishQuery I) h)
  <= weightBudget k h
```

No old ClosureFor premise is assumed or supplied falsely.

### Bounded reconstruction and explicit terminal witness bound

Module: [RankQueryLengthBound.lean](../lean/Subtail/RankQueryLengthBound.lean).
Namespace: `Subtail.RankQueryLengthBound`.

The central strengthening of the existing semantic compiler theorem is:

```lean
compile_bounded (I : Instance k) (c : Clause k) (D : Diagram k)
  (B : Reference k) (hB : SafeReference I B)
  {P : Clause k} (hP : compileDiagram I c D = some P)
  (hsat : SatClause (prefixGraph I B) P) :
  ∃ C : Reference k, FirstReturnExt I B C ∧
    SatClause (prefixGraph I C) c ∧
    C.word.length + 1 ≤
      (B.word.length + 1) * (clauseWeight P + 2)
```

`preimage_bounded` lifts this to the actual union using the new size theorem.
`finish_bounded` produces an ORIGINAL Witness with
`w.length + 1 <= (B.word.length + 1)*(k+1)`.
`promoted_finish_bounded` composes the length factors without an assumed
ClosureFor or numerical witness bound.

For T_0=k+10 and T_(j+1)=64*k*T_j^(6*T_j^2+2), the definitions are:

```text
growth k 0       = 1
growth k (h+1)   = (T_(h+1)+2) * growth k h
witnessBound k   = if k=1 then 0 else 2*(k+1)*growth k (k-2)
```

Equivalently, for k>=2,

```text
Fhat(k) = 2*(k+1)*product_{j=1,...,k-2}(T_j+2),   Fhat(1)=0.
```

The final theorem is against the unchanged direct Witness predicate:

```lean
terminal_witness_bound_iff (I : Instance k)
  (ht : TerminalRank.TerminalFinals I) :
  (∃ w : Word, Witness I w) ↔
    ∃ w : Word, Witness I w ∧ w.length ≤ witnessBound k
```

There are no unresolved quantitative premises in this theorem. It uses the
already checked qualitative `RankQueryDecision.rankDecisionStatement` for the
bounded promotion plan; the dependency is from this NEW theorem to the existing
decider, never the reverse. The production import graph is unchanged.

This is a bound on SOME original witness of every positive terminal instance,
not every witness. Here k is the number of states of the supplied terminal
machine. It is not the number of subtype variables, constraints or expression
nodes. No remaining subtype reduction or original-input complexity bound is
assumed. This is not a practical runtime or storage guarantee.

## 2. Counting and semantic readback

Write v for declared variables, a for atom occurrences, S for the sum of their
observer sizes, and T=max(2,1+v+a+S). Instance.initial implies k>0.
The existing coverage budget gives per-atom pieces P=2*(3a+2S)<=6T, total piece
occurrences M=aP<=6T^2, groups<=2T, and core variables<=v+M.

The Estimate invariant follows the actual compiler cases and additive folds.
Each piece emits at most one non-interval atom, of size at most T, and at most
one observer coordinate for any FIXED physical interval. The interval-index
map is injective, even if a forward piece crosses many global marks. This is
where the proof distinguishes total observations across all intervals from
coordinates in one interval. Repeated traversals and repeated atom objects are
counted separately; no deduplication or normal-form assumption is inserted.

One interval has exactly 6*k*product(active sizes) controls: original state,
three next markers, positive-length bit, and all observer coordinates. The
single physical generator contributes 6k ONCE, not once per observation.
Consequently its size is at most 6*k*T^(6*T^2), and all interval sizes sum to at
most 12*k*T^(6*T^2+1). The proof bounds variables by 2+3T+M, atoms by 2+M+2T,
and other observer states by 4+6T^3, then absorbs this polynomial and the interval
sum into the stated 64*k*T^(6*T^2+2).

The coverage module's indexed sum is proved equal to RankQuery.sumSizes.
Queries are finite lists of clauses and weight is their maximum. All finite
colour, location, state, next-marker, piece and seam alternatives are outside
the individual-clause count; the pointwise theorem handles each emitted clause.
The actual grammar's tests, equality lists, colour tables, transition tables and
captured observer/function descriptions are NOT charged by clauseWeight.
Their potentially large representation cost must not be hidden in a runtime
claim derived from this metric.

The proof includes empty queries, atom-free clauses, one-group diagrams,
zero-state input observers, unused declared variables, zero-length forward
pieces, and empty active lists. An empty active list has product 1, hence a 6k
interval observer. A one-group diagram has no intervals. No T>=2 assumption is
added at query-union level for the empty query; monotonicity covers weight zero.

For lengths, LengthRun is the existing Run relation with an edge count. The
existing product-simple chain lemma yields an accepted path of n edges with
n+1<=N*s for N graph vertices and s observer controls, retaining initial/final
controls. `lengthRun_gen` proves one emitted letter per edge. The bounded
interval trace keeps the entire decoded endpoint tuple: actual state, next
marker, seen bit, and every entering/leaving observer coordinate.

`exists_bounded_recon` fixes the common vertex assignment and replaces only the
interval traces in the existing Recon structure. A trace still observes all
active paths simultaneously. The seen=0/1 endpoints prevent a required positive
interval from collapsing to zero, including coincident origins. Its next/end
checks still prohibit an intermediate full return. Generic existing Recon
lemmas reassemble one safe first-return extension and all original query atoms,
tests and (dis)equalities. Core/portal facts are retained, not independently
regenerated under incompatible word choices.

Summing each physical interval once gives total interval length<=N*W. Add the
first emission to obtain at most N*(W+2) vertices. Finishing is shortened in its
k-state product and reconstructed using the existing original-Witness theorem.
The promotion induction multiplies these factors in descending unwind order;
commutativity gives the displayed product. `one_state_empty` handles k=1 with
terminality; the empty product handles k=2. No state/input-size identification
or finite-model restriction is used.

## 3. Executed evidence and reproducibility

**Full native CI PASS at 0b5d9de57a36591f3fd7cb38940afde3c7f9500b:**
[run 35452368681](https://github.com/mhenglein/subtail/actions/runs/35452368681),
job 105921634191. The completed job and its individual steps were read back.
The exact unchanged machine-readable audit is committed as
[results/rank-weight-native.json](../results/rank-weight-native.json), rather
than relying on an expiring artifact. Its source_sha/checkout_sha identify the
proof-source checkpoint, not the later documentation-only commit.

The job executes:

```sh
python3 scripts/check_rank_weight_native.py
# internally:
# lake build +Subtail.RankQueryWeightCounterexample +Subtail.RankQueryWeightBound +Subtail.RankQueryLengthBound
# lake env leanchecker Subtail.<each of the three modules>
# lake env lean <generated complete declaration axiom audit>
```

It performs a full Lake build of the three additive targets and dependencies,
including code generation, followed by separate kernel replay of each module.
All 87 audited top-level/generated-interface declarations have transitive axiom
closures contained in {propext, Quot.sound, Classical.choice}. Every new def and
abbrev is choice-free. The source gate rejects unfinished placeholders, custom
axioms, unsafe declarations and native proof oracles. The audit pins all 23
transitive Subtail source hashes, plus the driver hash. Those hashes were
compared successfully with the local proof-checking sources.

Environment: Lean 4.33.1, x86_64-unknown-linux-gnu, Lean commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6; GitHub Ubuntu runner,
Python 3.11.16. One Lean worker thread, 32768 KiB thread stack; 25-minute job
wall limit, 16 GiB virtual address-space cap, 1200-second CPU cap per process;
build/replay/audit subprocess timeouts 900/600/300 seconds. Deterministic proof
checking, no random seed. Build-cache reuse is not a claim of from-scratch
compilation of every unchanged dependency; kernel replay is separately run.

Source identity:

| Module | Git blob | SHA-256 |
|---|---|---|
| RankQueryWeightCounterexample | 32994ecaa887cdd7b6afec5a208d6a0fefd47605 | d3e2ebbe27bdc277f8080e5e75f8d8939784d670e396e52e69aac631681a68ce |
| RankQueryWeightBound | ef27df56ef8d1a3caa6e31666891714b56630d3c | d92069dfe5de891ba9bcfe3c5599a6a5e726fd57e2995f87a3b569fa0daabe50 |
| RankQueryLengthBound | 21e863aa682c8fb5c1690f45a53a01a25163e722 | daec0fabc8c8e8b5c9ff5b1078a110f2fddf48ef60d3cbfec04557261a794399 |

The audit JSON has SHA-256
7146d2c9f5517aafd7b8e6daa525093511f222ef303c4f956bb884acc4f3af29.
The reproduction driver has SHA-256
87f4d0e5d8114b2d8c6bb15d24ef9d1ad36ffafb1921c8af2b7f68135915e9b3.

Local evidence is separate: the container initially lacked Lean and network
lookup failed. An isolated Actions job temporarily exported the pinned Lean
runtime, tracked Lean sources and compiled dependencies without credentials or
Git configuration. After download, local elaboration, all three kernel replays
and the 87-declaration audit passed on identical source hashes, using
`python3 scripts/check_rank_weight_native.py --elaborate-only` and local
snapshot cb50de63bc95c8963502ea321ddf59a4b13ca4d7. This is proof-only local
validation, not a local full Lake/code-generation pass. Full Lake validation is
the separate successful CI run above. Temporary large runtime exports were
removed from the final workflow; it uploads only the small audit JSON.

The Research checks run 35452368682 also passed at the proof-source checkpoint.
The broader existing Lean workflow 35452368742 was still IN PROGRESS at the
readback used for this note; it is not reported passed here. Full Python
experiment suites, exhaustive diagram evaluation, observer-state materialization,
performance benchmarks and a new non-author mathematical review were NOT RUN.

## 4. Failed attempts retained for the next worker

The initial CI run 35450833969 failed with a thread-creation error before useful
proof results. The isolated job was corrected to use one Lean worker thread and
the explicit larger virtual-memory allowance; no shared toolchain version or
workflow was changed. Later prototype runs 35450956725 and 35451273519 exposed
proof-script/elaboration errors: terminality required unfolding; Bounded needed
explicit list membership rather than a missing blanket Decidable instance; a
flattened replicate needed mem_flatten/mem_replicate rather than a giant
simplifier-generated disjunction; Estimate needed an explicit dependent diagram
binder; the fold proof needed to apply to the actual compiler expression; and
Nat.pow_succ needed its exponent specified before AC normalization. These were
fixed without changing the target definitions or statements.

The first offline archive exceeded the connector's 512 MiB download limit.
Splitting that temporary artifact into three bounded parts resolved transfer.
A local full Lake attempt then failed because the deliberately stripped runtime
lacked executable IR needed by an unchanged Basic.Repr dependency. Basic was
NOT edited or marked noncomputable. The original cached dependency was retained,
local checking was explicitly limited to elaboration/kernel/audit, and a normal
full runtime on CI subsequently passed the full build. This environment failure
is not mathematical counterevidence. The final sources contain no admitted goals.

The incorrect shortcut from existential product-simple coverage to an upper bound
on EVERY diagram in the oversized enumerator is retained in PR #47. No silent
normalization or smaller enumeration was substituted to make the old U hold.

## 5. Preservation, review and integration handoff

Only seven new paths are proposed: the three Lean modules, the isolated checker
and workflow, this note, and the exact audit result. No existing source, import,
interface, scientific ledger or other worker branch was modified. Main advanced
from 3ce7cf18899ad24a5562d4b614f738bec8bc8427 to
7185b15140fbc629bf1825063d1652d4feb8a43f during this session; the exact compare
contains only four C030 advisory files, none of these paths or Lean dependencies.
This is not a claim that a future combined integration tree has been tested.
The latest active C029 completion reservation was reread and remains untouched.

The author read back all target statements and their critical dependencies and
matched source hashes to the completed CI audit. No other session has yet
performed the new modules' non-author semantic readback. That and coordinated
integration are the next gates, not a remaining unproved single-step or Fhat
premise in these modules. In particular review:

1. Membership/terminal hypotheses and the unchanged meaning of ClosureFor;
   native counterexample versus the separate ordinary satisfiable model.
2. Per-interval versus total active-coordinate counting and the metric's
   deliberate exclusions; no missing factor for duplicate occurrences.
3. Fixed common assignment/endpoint controls in bounded Recon replacement,
   positive lengths, aliasing origins, first-return safety and original Witness.
4. k=1, k=2, promotion indexing and the one-way dependency on the old decider.

Proposed canonical update for the integrator, after non-author readback:

> C080's original U_k(T)=64*k*T^(2*T+2) does not bound the current concrete
> preimage: an explicit terminal five-state counterexample is kernel-checked.
> A separate corrected bound 64*k*T^(6*T^2+2), quantitative shared-interval
> reconstruction, and its corresponding explicit terminal witness bound Fhat
> are now kernel-checked in PR #48 at source 0b5d9de. The old conditional
> ClosureFor/U/F statements retain their meanings; the old F itself and an
> alternative smaller compiler are not refuted. Qualitative terminal decision
> is unchanged and remains independent of the quantitative layer. This proves
> no additional subtype reduction or original-input-size complexity bound.

Coordinate STATE, C080, A017/A018, #30/#34 and experiment/Lean navigation updates
with the current integrator; do not overwrite active shared records. Preserve
PR #47 as discovery/ordinary-proof history and link the later native result.
The new workflow explicitly builds the additive modules even though production
imports remain unchanged, and triggers on Lean dependency changes. Re-run the
checker and repository/index/navigation checks on the actual reconciled tree.
No main merge, other-branch rewrite, branch retirement or workspace cleanup was
performed. Other agents' local-only work, stashes and unpushed commits were not
inspected. Scope release and final publication head are recorded in #30/#37.
