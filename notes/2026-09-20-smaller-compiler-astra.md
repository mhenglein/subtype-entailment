# Smaller existential compiler: retain a linear active-coordinate budget

Date: 2026-09-20. Actor: `smaller-compiler-20260920-astra`.
Workstreams A017/A018; issue #69, **compiler-only**. Original shortest-witness F is excluded.
Inspected source: `19b06d4fed9da635d9b911f0e908d04e4fc4b099`.
Branch: `codex/smaller-compiler-20260920-astra`.

> **Current validation:** the full ORIGINAL `ClosureFor I (preSmall I)` and
> `ClosureStatement I` pass pinned Lean build, kernel replay, all 22 declaration
> audits and the scoped runtime comparisons at `acf0524ffdbc9f407797b68b8953a39e1f79cf5d`.
> See Section 10 for exact receipts and preserved failed builds. Separate
> mathematical review is requested but not received: acceptance is BLOCKED on
> that review, not READY_FOR_INTEGRATION. No original-F conclusion is made.

## Status and evidence boundary

This note gives an ordinary construction and proof of the ORIGINAL existential
semantic-and-weight contract. The new Lean module attempts the same theorem
without changing any existing definition. At this note's initial publication,
its pinned build/kernel/dependency/native workflow is PENDING, not PASS.
The independently implemented local Python corpus and integer checks pass.
Separate mathematical review is requested, not presumed. Later receipts must
name exact commits and runs rather than silently relabel this initial record.

Read: current AGENTS, problem, STATE, C080/C082, relevant A017/A018 histories,
RANK_QUERY_COMPILER, preserved PR #47 discovery, exact compiler/coverage/weight
sources, issue #69 and recent #37. Scope claims: #69 comments 5750331094 and
5750364181; #37 comments 5750336344 and 5750413225. The F-only contributor's
5750331625 claim was explicitly acknowledged: that session owns F, this one
owns only compiler ClosureFor. No shared ledger, old compiler, toolchain,
import aggregator, old workflow or history is changed. No integration lease.

## 1. Exact target, not a replacement numerical statement

For a clause c, let v be its number of vertex variables, a its number of path
atom OCCURRENCES, and S the sum of their observer state counts s_i. At the
inspected source:

    t(c) = max(2, 1 + v + a + S)
    weight(phi) = max { t(c) : c in phi }, with max(empty) = 0
    U_k(T) = 64*k*T^(2*T+2).

The unchanged `RankQuery.ClosureFor I pre` requires BOTH:

    for every finite query phi and safe reference B,
      Sat(P_I(B), pre(phi))
        iff exists C, FirstReturnExt(I,B,C) and Sat(P_I(C),phi);

    for every phi and every output clause d in pre(phi),
      t(d) <= U_k(weight(phi)).

`ClosureStatement I` is `TerminalFinals I -> exists pre, ClosureFor I pre`.
Our construction is effective and in fact uses no terminality hypothesis in
this local first-return theorem. It is not the already established qualitative
semantic-only compiler and is not the corrected Uhat theorem for the old map.

A query is a finite disjunction of existential conjunctions: unary colour
tests, vertex equalities/disequalities and directed finite-observer path atoms.
Labels are F, S, K0, K1. Empty paths are allowed when a control is initial and
final and its colour test holds. Every conjunct shares one vertex assignment.
There are no new word variables, inverse edges or negated reachability atoms.

A reference is a nonempty finite binary word with a label at every cut. The
zero-cut label is final, labels obey the reversed transition equations, avoid
Bad, and satisfy the ordered flag test against EVERY border, including the
empty and whole prefix. Its graph has prefix positions, proper-failure F,
successor S, and prefix-suffix K transitions including full-prefix fallback.
Colours record the original state, accumulated flag-column mask, next bit,
root and endpoint. A first-return extension preserves the whole old labelled
prefix and has its first later occurrence of the base word end at its own
endpoint. Occurrences may overlap; an extension may have just one fresh vertex.
These are precisely the existing definitions, not a new simplified graph model.

The compiler may change which finite diagrams are retained and hence the
output disjunction. It may not change this graph class, satisfaction, safety,
first-return relation, weight, quantification over ALL safe B, or the shared-C
existential. Its output has the same query grammar. This proposal changes only
a syntactic filter. It does not demand that arbitrary existing diagrams obey a
normal-form theorem.

Disjunct count, unary-test/equality-list length and observer transition-table
storage are not charged by `clauseWeight`. This matters: a small per-clause
weight is not a small compiled file, practical runtime bound or witness bound.

## 2. Where the old representation grows

The existing finite enumeration uses:

    blockBound Bc = 3*a + 2*S
    groupBound Gc = 2 + v + 2*a + 2*S
    per-atom piece cap = 2*Bc
    core-variable cap = v + 2*a*Bc.

Thus its total piece envelope is quadratic in t. A forward piece spanning a
physical interval contributes one observer coordinate to that interval. It may
span many intervals, but never contributes twice to one interval. Seams choose
its control at intermediate GLOBAL marks. The interval observer has EXACTLY

    6*k * product(sizes of active coordinate occurrences)

states: original state, next-bit/END marker, positive-progress marker, and all
observer coordinates. Repeated traversals, including those of one observer,
remain distinct. The old enumeration allows far more of them than coverage
needs. Redundant alternatives and unused core indices also enlarge enumeration,
but they need not be removed to meet the original per-clause target.

Preserved PR #47, head 42be43f35a98d4d23a4ba26439833730bbcd6510, exhibited five
copies of one two-state atom (input weight 17), each with 35 forward/wrap pairs.
Its one interval has 175 active coordinates and output weight

    12 + 30*2^175 > 320*17^36.

The valid satisfiable diagram remains in the OLD compiler. Its refutation of
the old map's universal U bound remains true. C082's corrected Uhat theorem is
also untouched. Neither fact precludes an existentially chosen smaller map.

## 3. The one change: filter active coordinates BEFORE building products

Write `itemsAt I c D g` for the unchanged list of active coordinate occurrences
of physical interval g. Set

    activeBudget(c) = a + S
    compact(I,c,D) iff
      for every g < D.groups-1,
        length(itemsAt I c D g) <= a+S.

Define

    smallDiagrams(I,c) = filter compact(I,c) (diagrams c (budget c))
    preClause(I,c) = preimageOver I c (smallDiagrams(I,c))
    preSmall(I,phi) = concat [preClause(I,c) : c in phi].

All functions on the right are the existing finite syntactic functions except
the new Boolean guard and wrapper. `itemsAt` counts emitted active records; it
does not construct the exponential interval observer. No B, C, concrete graph,
semantic equivalence oracle or noncomputable choice enters the executable map.
Finite existing enumeration plus finite filtering proves termination/effectivity.
The guard preserves the remaining coordinates exactly, with multiplicity.

The first proposed sufficient filter capped each atom's forward pieces by
s_i+1. The final guard above is WEAKER: it permits diagrams outside that shape
whenever every interval still has at most a+S coordinates. This refinement
simplifies the checked counting interface; it does not delete zero-length
pieces or identify roles. The ordinary coverage argument below proves both
filters sufficient, but the Lean implementation uses the direct interval guard.

This remains an enormous enumerable algorithm. Filtering its output does not
remove the cost of generating rejected diagrams; no speedup claim is made.
A later direct constrained enumerator would require exact enumeration-equivalence
proofs and is not part of this change.

## 4. Coverage: every ONE-extension model has a retained diagram

Fix I, a safe B, one first-return extension C and one assignment tau satisfying
an input clause c on P_I(C). Do not replace C independently for different atoms.
For each atom i, choose an accepting observer path in this same graph between
its tau endpoints. Delete cycles of repeated (physical vertex, observer control)
nodes. The endpoints, all colour tests and acceptance remain unchanged. These
cycle deletions affect paths only, not the underlying word C or tau.

Let e=|B|+1 be the first fresh vertex. A product-simple path visits e at most
s_i times. The existing first-return edge-shape theorem says that every new
fresh block after a path's first fresh block starts at e. A block here is
maximal physically consecutive forward fresh nodes; one-node blocks are allowed.
Consequently atom i has at most s_i+1 fresh blocks. This is exactly the already
proved `RankQueryCoverage.Cov.freshCount_le`, not an assumption about all diagrams.

Use the existing coverage construction: make one ordered deduplicated GLOBAL
mark set from e, the new endpoint, fresh variable positions and endpoints of
all fresh blocks of all atoms. Coincident roles occupy one group, not different
physical vertices. Old blocks become core pieces, fresh blocks become forward
pieces, and the intervening edges become enter/exit/wrap pieces. The seams are
the original controls at each intermediate global mark of each block.

For a fixed interval g, each contributing piece is a forward fresh-block piece,
and each such block contributes at most one item. In the Lean representation,
`coversPi_block` sends a contributing piece index pi to its unique block si,
with pi=2*si. Distinct selected pi therefore cannot be counted as one occurrence.
Inject the selected piece-index list into twice the fresh-block-index list.
Summing over atom OCCURRENCES gives

    length(itemsAt I c D g)
      <= sum_i number_of_fresh_blocks_i
      <= sum_i (s_i+1) = S+a.

Thus the same coverage diagram satisfies compact. Existing `Cov.bounded`,
`Cov.valid` and `Cov.sat` are unchanged. Its old assignment sends each origin
variable to the KMP cursor of that physical mark in the ONE original C. On each
physical interval the original C supplies one generated segment together with
all its active observer runs, establishing the shared product, not independent
segment languages. Therefore every model of c in any C is covered by one
retained output clause satisfied on B. Disjunction lifts this to every phi.

## 5. Reconstruction: no spurious joint model is introduced

Every retained diagram is an old bounded diagram and is compiled by the exact
old `compileDiagram`. Hence any satisfied retained output is also a satisfied
output of the old semantic preimage. Apply the existing arbitrary-diagram
soundness theorem (`RankQueryEnumeration.preimage_sound`, ultimately
`RankQuerySound.closure_reverse`). It produces one C satisfying the whole
original query, with the required safe first-return relation.

Concretely, every interval product still couples ALL active coordinates to the
same generated bit and same fresh colours. Its boundary original states, next
markers, observer controls and origin vertices are shared. Adjacent interval
witnesses concatenate at these boundaries. Seams transport repeated traversals;
portal tests handle entry, failure exit and endpoint wrap. The positive-progress
coordinate disallows a zero-length interval between distinct mark groups,
even if their old origin vertices coincide. Masks and endpoint guards establish
safety and first return. Query unary tests and equality/disequality constraints
are unchanged. None of these obligations is replaced by per-atom satisfiability.

Coverage and reconstruction establish the required equivalence with ONE B and
ONE C for the conjunction. The implication

    conjunction_i exists C_i . atom_i(C_i)
      implies exists C . conjunction_i atom_i(C)

is neither used nor true.

## 6. Universal weight bound on EVERY retained clause

Let t=t(c), so t>=2, and k>=1 since an Instance contains an initial Fin k state.
Let n=D.groups, nc=D.coreVars, P=2*Bc and M=a*P. Existing boundedness gives

    n <= 2t,  M <= 6t^2,  nc <= v+M <= t+M.

A piece emits at most one non-interval atom and its observer has at most t
states (a sliced input observer, or a two-state portal observer). The two base
atoms each have two states. Thus emitted non-base atoms number at most M and
their observer-size sum is at most tM.

For each interval, the new guard gives r_g<=a+S<=t-1 active coordinates. Each
coordinate is an input observer, of size at most t, so

    intervalSize_g = 6k*product_j s_j <= 6k*t^(t-1).

This counts repeated coordinates with multiplicity. A seam does not multiply
coordinates within a single interval. Empty products equal one. Zero-state
observers create no accepted path; no division by their sizes is used here.

Using the exact formulas from compileValid,

    variables = 2+n+nc
    atoms = 2+emitted_atoms+(n-1)
    observer_sum = 4+emitted_sizes+sum_g intervalSize_g,

we obtain for the raw expression under max(2,...):

    8+2n+nc+(1+t)M+6k(n-1)t^(t-1)
      <= 8+5t+12t^2+6t^3+12k*t^t
      <= 28k*t^(t+1)
      <= 64k*t^(2t+2) = U_k(t).

For the middle inequality, the polynomial part is at most 16t^3 for t>=2:
8<=t^3, 5t<=2t^3 and 12t^2<=6t^3 suffice, together with 6t^3. Then t^3<=t^(t+1)
and k>=1. The maximum with two is harmless. These estimates hold for EVERY
bounded compact diagram, not merely satisfied outputs or the coverage diagrams.

The Lean proof uses a slightly looser but simpler intermediate r_g<=t and the
existing weight-counting lemmas. It bounds the polynomial by 32t^3 and the
interval contribution by 12k*t^(t+1), then by 44k*t^(2t+2)<=U_k(t). It proves the
same original final target, not a redefined U. The stronger display above is
ordinary arithmetic and separately checked over the finite aggregate corpus.

For nonempty phi, t(c)<=weight(phi), and unchanged U is monotone. Every output
comes from some input clause, giving the exact global target. For phi=[],
preSmall=[] and the output-membership requirement is vacuous despite weight=0.
No terminality, reference, satisfaction or normalization assumption is hidden
in the output-weight theorem beyond membership in the retained syntax.

## 7. Independent falsification, not only size arithmetic

The standalone checker uses literal string-suffix prefix graphs and ordered
flag safety, BFS product-simple paths, a separate Warshall path-relation
oracle, and exact finite synchronized interval-product reachability. It
reconstructs a new common C by concatenating shared interval traces, then
re-evaluates the entire original conjunction on its independently constructed
graph. No source compiler or source evaluator is imported in standalone mode.

Local Python 3.13.5; seed 2026092069. The first repeat took 0.70 seconds with
maximum RSS 95,776 KiB under a 40-second wall cap. No timing comparison with
Lean or the full compiler is implied. Two standalone outputs are byte-identical.

Observed coverage:

- 44 binary first-return word pairs through length six; 158 successful common
  coverage/reconstruction certificates, 140 with multiple atoms.
- 1,644 BFS/Warshall path comparisons; 167 interval products, including 26
  shared intervals, eight repeated-observer intervals and ten internal seams.
- 38 overlapping returns, 33 coincident first/last marks, 103 coincident
  variable roles, 23 distinct physical marks sharing one old origin, 183
  fresh zero blocks and 88 old zero blocks. Six reconstructions change length.
- All 25 one-flag variants of the five-state fixture: 14 safe and reconstructed,
  11 rejected. Empty-border and Bad-state rejection are explicit.
- 8,100 exact integer-envelope checks over aggregate v,a,S and four k values.

Adversarial examples are constructive and distinguishing:

1. A safe terminal three-state instance has separately possible interval words
   10 and 110 for two exact-length observers, but their synchronized product is
   empty at ALL lengths (finite product exhaustion). Duplicating the same
   observer still accepts. Independent generators would falsely accept the
   conflicting pair; the retained product rejects it.
2. On B=01, C=0101, the exact path S,K0,S from fresh vertex 3 to 4 traverses the
   same physical interval twice. The proposed stronger 'at most one traversal'
   filter is incomplete. The actual linear-coordinate guard retains this case.
3. With identical old origins/state/next data at two marks, an observer accepting
   only an empty path cannot satisfy a positive physical interval. Removing
   the progress bit falsely accepts it; the real construction rejects it.
4. One fresh vertex legitimately has coincident first/last marks and NO interval
   atom. Empty atom paths, zero-state observers, no-atom clauses and the empty
   query union are separately exercised.
5. The historical 175-coordinate diagram fails compact because a+S=15. It is
   NOT declared unsatisfiable. A one-forward/wrap-pair-per-atom version retains
   five coordinates and has output weight 972 instead of 12+30*2^175.

Optional `--repository` compares independently produced certificates with the
UNCHANGED Python compiler and evaluator, after checking exact source blob
hashes. At initial publication this mode is NOT RUN locally (only a partial
source/artifact worktree is available); the isolated CI workflow runs it once
its source and receipt are committed. The complete old/new diagram unions
are not exhausted. Finite tests support, but do not replace, the all-input proof.

Commands from a full checkout:

    python3 experiments/check_smaller_compiler_astra.py > /tmp/small.json
    cmp results/smaller-compiler-astra.json /tmp/small.json
    python3 experiments/check_smaller_compiler_astra.py --repository
    cd lean
    lake build +Subtail.SmallerCompilerAstra
    lake env leanchecker Subtail.SmallerCompilerAstra

The isolated workflow additionally audits every new declaration's transitive
axioms and rejects Classical.choice in executable definitions. It tests the
native compact guard on the historical diagram and the empty-query output.

## 8. Lean interface and review checklist

New module: lean/Subtail/SmallerCompilerAstra.lean. Existing definitions remain
unchanged. Principal declarations:

    compact_iff
    covered_count_le
    cov_active_length
    cov_compact
    coverage
    reconstruction
    closure_iff
    compileValid_weight_le
    preimage_clause_weight_le
    closureFor : ClosureFor I (preSmall I)
    closureStatement : ClosureStatement I
    old_counterexample_rejected

The crucial new dependency is the indexed counting injection, not a new
first-return semantic axiom. Coverage deliberately reuses the existing Cov
construction inside the original common model. Source inspection should check
that all independent atom paths stay in that same C, that coversPi_block's
injection retains multiplicity, and that weight is universally bounded over
the filtered syntax. Kernel replay and runtime-definition axiom audit remain
separate from a mathematical review of the intended semantics.

No existing module or shared interface needs modification. A later integrator
may add an import or replace a backend only after combined-tree checks and
explicit interface agreement; this contribution does neither.

## 9. Limits, failed route and proposed handoff

The once-only traversal route is falsified and preserved above. The initial
per-atom cap is sufficient but unnecessarily strong; it is superseded here by
the direct per-interval guard. Deduplicating observer coordinates without their
control-pair/role information, splitting shared generators, collapsing coincident
origins, or deleting zero-length cases is not an accepted optimization.

This establishes an ordinary compiler construction, not an efficient practical
implementation. No full compiler enumeration, total storage/runtime theorem,
subtype complexity classification, original F proof/refutation or shortest-
witness conclusion is claimed. In particular no final theorem here transports
compiler size into witness length. That belongs to the explicitly separate
F-only assignment and requires its own connecting argument.

Local environment has no Lean/lake or usable git network. The local named git
worktree is explicitly artifact-only, not a falsely claimed upstream checkout.
The GitHub connector gives pinned source and branch writes; the new isolated
workflow supplies the exact repository toolchain. No other worker's local
worktree, unpushed changes or stashes were inspected.

Suggested ledger text for the integrator AFTER independent review and actual
validation: 'A new filtered existential compiler retains the old grammar and
shared-extension semantics while meeting the original U bound. The unchanged
old compiler's universal U refutation and C082 corrected bound remain intact.
This compiler-only contribution makes no original-F conclusion.' Do not promote
C080 as a whole from this local clause.

At handoff, record the exact final commit and workflow outcomes, retain any
failed formalization diagnostics, release all five new paths and leave issue
#69 open for its separate F limb and any remaining review obligations.

## 10. Completed validation and acceptance boundary

The historical PENDING statements above describe the initial note publication
at `2b2b994c288519b79acb02962c9305a0373d5f3d`; they are not the final status.
The complete checked source is `acf0524ffdbc9f407797b68b8953a39e1f79cf5d`.
Actual execution: GitHub Actions run **35517192465**, job **106095004645**,
completed successfully on 2026-09-20 at 14:40:52 UTC. Environment: Ubuntu 24.04.5,
Lean **4.33.1** (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Lake 5.0.0.
Workflow file `.github/workflows/smaller-compiler-astra.yml` has a 20-minute job
limit, with 180-second declaration-audit and 120-second Python-command limits.

Actual completed steps:

- `lake build +Subtail.SmallerCompilerAstra`: PASS, 19 jobs. The new module
  compiled in 2.2 seconds; dependencies used the workflow's Lake cache. This is
  not a fresh whole-library build or a compiler performance benchmark.
- `lake env leanchecker Subtail.SmallerCompilerAstra`: PASS.
- All **22** new def/theorem transitive axiom closures: PASS. Only `propext`,
  `Quot.sound`, `Classical.choice` occur. Every executable `def` is free of
  `Classical.choice`. No `sorryAx`, native-decision axiom or custom axiom occurs.
- Native `compact inst input diagram` is `false` for the preserved historical
  diagram, matching the kernel-checked `old_counterexample_rejected` theorem.
  Native `(preSmall inst []).length` is `0`, matching `preSmall_nil`.
- Standalone Python checker: PASS; `cmp` with the committed JSON is exact.
- `--repository`: PASS, **62** independently constructed certificates checked
  with the unchanged Python extraction/compiler/model evaluator, plus **one**
  preserved counterexample/smaller-diagram replay. This also validates the four
  pinned source blob hashes before comparison. The full JSON is printed in the
  job log; the committed JSON intentionally remains the standalone receipt.

Final source hashes (SHA-256):

    Lean:   9d23d5922c627708bb62f6f1d68059870c4566c6ef7aa8bd6384383cfe90ce05
    Python: bf7dafe0ea0c3269261de858ee9c813d1f958cb044c0ae8fd808000d02a9741c
    JSON:   b91558da2248401349442a4603d18ca07d5217b70dfa97d9a732c298075820c2

The checked endpoints include both directions of `closure_iff`, the universal
retained-output `compileValid_weight_le`, its query-weight lift, and the exact
unchanged `ClosureFor`/`ClosureStatement`. The original final numerical target,
not just a helper or conditional statement, is now a checked declaration.
The sharper intermediate `28*k*t^(t+1)` displayed in Section 6 remains ordinary
arithmetic; the Lean proof uses the stated looser intermediate and proves the
same original U. No stronger runtime or shortest-witness conclusion follows here.

Failed native attempts are preserved in branch history and Actions logs:
`4e1d652082bcae4845487165a2fba9b879eeef82` / run 35516838445 failed on namespace,
binder and composition syntax; `7d6090007c93f80888b30a810e46452aca36cc72` / run
35516995998 failed on an explicit list-default mismatch and a missing namespace
open. The later JSON/checker commits repeated that second source failure.
`acf0524` corrected those proof-writing issues; no theorem statement, existing
definition or numerical bound was weakened. Skipped checks on failed runs are
not retrospectively labelled successful.

Coordination was acknowledged in both directions: the F-only session's
5750400657 comment agrees the split in our 5750364181. Its separate proof route
was not adopted or investigated by this compiler-only contribution. Review of
Sections 4-6 was explicitly requested in #69 comment 5750449854, with full
formal evidence reported in 5750490632. **No separate mathematical review receipt
has been received at this handoff.** Thus the implementation and its precise
formal contract are checked, while independent semantic/ordinary-size acceptance
remains BLOCKED and the PR should remain draft. A kernel pass is not relabelled
as a human or separate-agent review.

Main advanced separately to `e2c981b44418ca12a689e8ef3c4b63f62d750e64`.
The exact base-to-main comparison changes only CONTRIBUTING.md, STATE.md,
research/README.md and research/approaches.json; AGENTS, all mathematical/source
dependencies and the toolchain are unchanged. This branch retains its pinned
base. No combined-main integration run or merge is claimed; the integrator owns
that step and the shared-ledger update. All five new paths are released at the
final #69/#37 handoff, with no background work, successor assignment or retained
integration lease. Keep #69 open for its separate F limb and pending review.
