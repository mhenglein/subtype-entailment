# Original terminal witness bound F: final F-only report

Date: 2026-09-20. Actor: `f-only-astra-20260920`; A017/A018, issue #69,
coordination #37. Base: `19b06d4fed9da635d9b911f0e908d04e4fc4b099`.
Branch: `codex/f-only-astra-20260920`.

**Result: the exact original F is proved, with a complete Lean-checked endpoint.**
The final formal route consumes a separately owned, proved compiler contract
as a pinned read-only dependency. An independent ordinary proof using the
UNCHANGED compiler and one fewer promotion was completed first; its critical
steps are also checked. Independent mathematical review has been requested
but NOT obtained. No shared ledger, core definition, toolchain or existing
workflow is changed, and no main integration or issue closure is performed.

## 1. Exact target, chronology and scope

C080 records:

> Consequently every positive instance has a witness of length at most the explicit computable bound `F(1)=0, F(k)=2(k+1)*prod_{j=1..k-2}(T_j+2)` with `T_0=k+10` and `T_(j+1)=64k*T_j^(2T_j+2)`.

The quantification is over EVERY finite binary terminal instance with k states.
The product formula applies for k>=2, giving F(2)=6 by the empty product.
There is no recorded F(0); `Instance 0` is uninhabited because it has an initial
state. The executable totalization at zero introduces no input obligation.

An instance has a partial deterministic binary transition table, an initial
state s, arbitrary final and Bad sets, and an arbitrary ORDERED flag relation G.
Terminal-finality means every final state has no outgoing transition. No other
condition on s, Fin, Bad or G is added.

For a word w of length n, `Witness I w` is the ORIGINAL Basic predicate: all
run cuts c(0),...,c(n) are defined and avoid Bad, c(n) is final, and for every
0<=i<=j<=n, if w[j:] is a prefix of w[i:], then (c(i),c(j)) is unflagged.
Diagonal cuts, the empty terminal suffix, the empty word and undefined
transitions are all included.

The exact theorem is

    (exists w, Witness I w)
      iff (exists w, Witness I w and length(w)<=F(k)).

A refutation requires an actual witness PLUS an all-words proof that no witness
of length <=F(k) exists. A long arbitrary witness, oversized emitted clause or
word resisting a particular deletion is insufficient. Capped failure is UNKNOWN.

The original statement and proof/counterexample obligations were committed
BEFORE new searches in the dated outline `61666c277eff660f8994a9401c0cd1125b97f659`.
The complete independent ordinary proof, with all intermediate arguments and
historical open/checkpoint status, is preserved at
`c8a6ceafa4ae469faf07f96f47dadbc3fb21dd25`, this same note path, sections 3-9.
That immutable version is also included as an archive in the delivery bundle.
The present report updates the later formal endpoint rather than erasing the
chronology.

The old universal concrete-compiler bound U remains REFUTED. C082's larger
replacement remains valid. Neither fact alone settles F. The separately
assigned smaller-compiler contributor owns its construction, filtering, coverage
count and numerical proof; this F-only work does not investigate, modify, review
or claim that contribution.

## 2. Complete checked proof of F

The endpoint in `lean/FOnlyCompilerBridge.lean` is

    Subtail.FOnlyCompilerBridge.original_F
      (I : Instance k) (ht : TerminalRank.TerminalFinals I) :
      (Exists fun w : Word => Witness I w) <->
      (Exists fun w : Word => And (Witness I w) (w.length <= FOnlyAstra.originalF k))

There is NO caller-supplied ClosureFor, compiler, absorption, nonempty-witness,
length cap or additional semantic premise. `originalF` is the exact old
recurrence/product, not the larger C082 replacement.

### Read-only dependency, not an extra assumption

The compiler contributor supplied `SmallerCompilerAstra.closureFor` and
`mem_preClause` at immutable source
`acf0524ffdbc9f407797b68b8953a39e1f79cf5d`. Its source SHA-256 is
`9d23d5922c627708bb62f6f1d68059870c4566c6ef7aa8bd6384383cfe90ce05`.
The proved contract gives exact first-return semantics on one shared extension
and the ORIGINAL output-clause weight bound. It is an imported theorem, not a
new hypothesis. Only its exported contract and concrete-diagram membership
are consumed here. The dependency source is NOT committed on this branch.

### Coverage and reconstruction are separate

Let preSmall be that compiler. If a safe reference B satisfies preSmall(phi),
choose its satisfied emitted clause P. Membership yields an input clause c of
phi and an ORIGINAL concrete diagram D with compileDiagram(I,c,D)=P. The
exported contract gives

    clauseWeight(P) <= U_k(weight(phi)),
    U_k(t)=64*k*t^(2*t+2).

Now apply the existing `RankQueryLengthBound.compile_bounded` to THIS diagram
and the satisfied P. It reconstructs ONE safe first-return extension C, with
one shared assignment satisfying c and hence phi, such that

    |C|+1 <= (|B|+1)*(clauseWeight(P)+2)
           <= (|B|+1)*(U_k(weight(phi))+2).                    (BR)

Thus a semantic-and-weight contract alone is not used to assert a length bound.
The common-extension reconstruction is explicitly supplied. Repeated observer
coordinates, shared marks, equality/disequality tests, overlapping traversals,
seams and empty paths retain the original compiler semantics. Independent
per-atom words are never substituted for one conjunction witness.

Define Phi_h as the existing `promote preSmall (finishQuery I) h`, including
its ordinary disjunctive union at every stage. The existing generic
`RankQueryUnwind.weight_promote_finish_le`, supplied with the proved contract,
gives weight(Phi_h)<=T_h, with the ORIGINAL T_0=k+10 and recurrence above.
The existing bounded finishing theorem gives, on a safe reference B,

    Sat(P(B),finishQuery I) implies
    exists original witness w, |w|+1 <= (|B|+1)*(k+1).          (FB)

Induct on h using (BR), the old weight bound and (FB). The result is

    Sat(P(B),Phi_h) implies exists original witness w,
    |w|+1 <= (|B|+1)*(k+1)*prod_{j=1..h}(T_j+2).             (UW)

At a union branch inherited from h-1, use monotonicity of the product. At a
preimage branch reconstruct one C with factor T_h+2, then invoke the induction
hypothesis on C and Phi_(h-1). The factor order and joint witness are explicit
in `promoted_finish_original_bound`.

For coverage, use ONLY the existing qualitative `rankDecisionStatement`:
a witness gives either the empty witness, or a safe one-letter B satisfying
the existing actual compiler's promoted finishing query at depth k-2.
`RankQuerySemanticUnwind.sat_promote_preimage_iff` turns this into an at-most
k-2 first-return chain ending at ONE reference satisfying the finishing query.
Generic `sat_promote_iff`, supplied with the proved preSmall contract, maps that
SAME semantic chain to Phi_(k-2) on the same B. This is `coverage_small`.
No numerical witness bound is used in this coverage direction.

Apply (UW) with |B|+1=2 and h=k-2. This yields a witness with length+1<=F(k),
and therefore length<=F(k), for k!=1. For k=1 terminality forces every witness
to be empty, giving F(1)=0. The empty-word case is handled separately; F(2)=6
is unchanged; k=0 has no instance. The reverse implication simply forgets the
length bound. This completes the exact theorem.

Termination is by the finite promotion index and finite product-path
shortening inside the existing bounded reconstruction. Acceptance and all
new comparison tests are re-established by reconstruction, not inferred from
an arbitrary interior deletion preserving a chosen list of comparisons.

## 3. Independent ordinary proof without the smaller compiler

The complete proof at the immutable c8a6ceaf note is independent of section 2's
new dependency. Its main steps, including the delicate final-return boundary,
are summarized here; the detailed coverage/reconstruction arguments are in
that preserved version.

**Safe normalization.** If a witness returns to its initial state at cut d,
w[d:] is again an original witness. Every cut and EVERY ordered comparison
lifts by the same offset d; there is no new concatenation seam. Take the suffix
after the last initial-state visit. This single finite truncation yields a
witness whose positive cuts all avoid the initial state.

**One saved rank.** Every proper reversed prefix of the normalized witness
uses at most k-1 original states. Terminal border-state injection counts all
borders, including zero and full, so its positive border rank is at most k-2.
The full reversed word is deliberately excluded and may have rank k-1.

**New finishing QUERY, unchanged compiler.** For a safe reference B of length
m>0, start a k-control observer at failureParent(B), with control B.label(m),
and accept at the original initial state s. A K_a move from cursor v to u
with new reverse state p requires

    v<m; u=advance_B(v,a); delta(p,a)=oldControl;
    p not Bad; G(p,p)=false; mask_B(u)[p]=false;
    u<m OR p=s.

The endpoint m is allowed only with control s and has NO outgoing move. The
usual one-F-edge packaging uses three variables and observer sizes 2,k, so
the clause weight is k+8<=k+10. This is `FinishPlus`, not a compiler alteration.

Its exact semantics is a safe completion C ending at reverse state s with no
full B return at any m<j<|C|. A first return at the ULTIMATE cut is allowed.
For soundness, if pi(C)=v<m, then

    pi(Ca)=advance_B(v,a)=u<=m,
    fullMask_(Ca)[p]=G(p,p) OR mask_B(u)[p].

The target may equal m: labels and masks agree with B through the old endpoint
inclusively. This identity clears ALL new comparisons, including the empty
border and old endpoint; old cuts stay unchanged. The source must be <m,
which is why the endpoint has no outgoing move. For completeness, a parent
>=m before the final cut, or >m at the final cut, induces an earlier full B
occurrence ending at e=j-parent+m. This contradicts the no-early-return
condition. The argument allows overlap and assumes no separation of copies.
A shortest accepting path in the fixed (m+1)k cursor/control product gives
length+1<=(m+1)(k+1), with every created comparison revalidated by the mask
identity. Empty completion and diagonal tests are retained.

**Coverage with k-3 promotions.** First rank milestones among PROPER reversed
prefixes start at the one-letter reference. Successive milestones are safe
first returns: any longer parent or earlier return would give the next rank
at an earlier cut, contradicting first occurrence of that rank. The final
proper milestone has no return before the ultimate cut, so satisfies FinishPlus.
Its rank is at most k-2; reaching it takes at most k-3 promotions for k>=3.

Use the UNCHANGED C082 preimage and its shared bounded reconstruction, now
starting from FinishPlus. Write X_0=k+10 and
X_(j+1)=64*k*X_j^(6*X_j^2+2). The same finite induction gives SOME witness with

    |w|+1 <= 2(k+1)*prod_{j=1..k-3}(X_j+2).                         (B)

Coverage fixes one whole extension and one assignment; reconstruction retains
one common word for all atoms. It does not choose independent words for
separate tests. Every reconstruction reduces the finite promotion index.

**Arithmetic lag absorbs the larger recurrence.** Put a=64k. For every j,
X_j>=k+10 and a<=X_j^4. Inductively prove 6*X_j^2<=T_(j+1). The base is immediate.
If x=X_j and y=T_(j+1)>=6*x^2, then

    6*(a*x^(6*x^2+2))^2
      = 6*a^2*x^(12*x^2+4)
      <= x^(12*x^2+14)
      <= x^(4*y+4)
      = (x^2)^(2*y+2)
      <= a*y^(2*y+2).

Hence X_j+2<=T_(j+1)+2. The product in (B) fits into the old factors 2,...,k-2,
leaving the spare factor T_1+2. Therefore (B)<=EXACT original F(k).
Small states are handled directly: k=1 only empty; at k=2 normalization leaves
at most one letter, which is <=F(2)=6. Empty and one-letter witnesses need no
milestone argument. No arbitrary local deletion or unbounded shortening loop
is assumed.

The normalization, sharpened border count, inclusive final-return mask safety,
new query weight and recurrence/product comparison are checked in
`lean/FOnlyAstra.lean`. The FULL FinishPlus/milestone composition is still an
ordinary proof, not a composed Lean theorem. Section 2 supplies a separate
complete Lean theorem of F, so these two formalization statuses must not be
confused.

## 4. Falsification and independent experiments

Before searching, the preserved minimal-witness, overlapping-deletion,
recurrent-residual and old-U counterexample arguments were read. Interior
state-loop deletion can create a new flagged border; aligned deletions can
break overlapping equalities; finite residual summaries do not preserve all
recurrent left contexts. None is reported as a counterexample to F.

A failed shortcut in this investigation is reducing the OLD finishing budget
without changing its endpoint rule. On the unary terminal chain
0 --0--> 1 --0--> 2, 00 is the unique accepted word. Its one-letter reversed
reference has labels (2,1): old Finish fails and FinishPlus succeeds. The
four-state chain and B=00 require an overlapping final return to produce 000.
These have literal independent checks; the first also has Lean-evaluated guards.

`experiments/f_only_astra.py` imports NO Subtail implementation. Its forward
Witness predicate compares literal string slices for EVERY i<=j; its reverse
predicate enumerates literal borders; its FinishPlus test uses finite BFS.
Every produced word is rechecked with the independent forward predicate.
Found minima are certified by complete increasing-length enumeration of all
shorter binary words. Unique-word unary chains have a separate all-length
acceptance proof. Bounded failures remain UNKNOWN.

The receipt covers 131,072 three-state table/flag annotations (initial0, sole
terminal final2, Bad empty; all256 tables x512 ordered flag relations), all
12,820 one/two-state terminal annotations, and1,000 seeded random instances
with3-8 states. It additionally tests arbitrary safe references, bounded
completion coverage, the recurrent shared-exponent fixture, initial-return
normalization, and actual milestone chains through seven promotions.

All8,253 found minima pass the saved-rank/FinishPlus checks. Of these,180 fail
old Finish but pass FinishPlus on the selected reference;16 require overlapping
final returns. Eight unary-chain oracles cover0-7 actual promotions. Fifty-two
flagged variants have certified all-length NO because their unique accepted
word fails a specified diagonal, nonempty-border or empty-border comparison.
These are negative test oracles, not refutations of F.

The three-state cap leaves123,440 UNKNOWN and the random cap leaves389 UNKNOWN.
The preliminary checkpoint counts8,248/161/8 are superseded by the expanded
harness/receipt, which added fixtures and random draws. No theorem is inferred
from any of these finite corpus counts.

## 5. Reproducibility and actual validation

### Independent Python

    timeout 40 python3 experiments/f_only_astra.py \
      --seed 2026092069 --trials 1000 --word-cap 10 --census-cap 8 \
      --output results/f-only-astra.json

Python3.13.5, Linux6.18.44 x86_64/glibc2.41; recorded elapsed1.352611 seconds,
40-second wall cap, no additional memory cap. One/two-state word cap5,
three-state cap8, random cap10; safe-reference completions add at most4 letters.
The recurrent fixture tests m,n=1..6,z=1..4. Script SHA-256:
`c6d90046defd3ef086a2e8039588dfb6a59fec0209737d5af1c84877c1c60f5d`.
The JSON status is `PASS_BOUNDED_CHECKS_NOT_GLOBAL_PROOF`.

### Critical steps, without the smaller compiler

Source `a867c756046b0cabbd97c55ce7abb83d2794f172`; checked checkout
`1cde3445828b6625168fc33235a1070cb1794cb9`.
Run35516715375/job106093784899 SUCCESS: compilation, kernel replay,20 named
axiom audits (four runtime definitions choice-free), and unchanged default
core regression. This run independently validates the critical-step module
without the later compiler dependency.

### Complete original-F theorem

Bridge source `ef1c34ec108cafe813c4bd5a178a8cf2f0fa1d31`; checked checkout
`29fde8b11fec1376e1d232e758969f923fec8836`.
Run35517790287/job106096546132 SUCCESS; full logs read.
Dependency: immutable acf0524f source and SHA-256 pinned in section2.
Both runs use the existing Lean4.33.1 toolchain on Ubuntu24.04.5.

The NEW branch-only workflow checks out the compiler dependency separately,
verifies its SHA-256, and overlays ONLY its module into the disposable CI
checkout. No compiler source is committed here. It runs:

    cd lean
    lake build +Subtail.RankQueryLengthBound +Subtail.SmallerCompilerAstra
    lake env lean -o .lake/build/lib/lean/FOnlyAstra.olean FOnlyAstra.lean
    lake env leanchecker FOnlyAstra
    lake env lean -o .lake/build/lib/lean/FOnlyCompilerBridge.olean FOnlyCompilerBridge.lean
    lake env leanchecker FOnlyCompilerBridge
    # Audit20 critical-step and6 bridge declaration closures.
    cd ..
    timeout 600 python3 scripts/check_lean.py

The job wall cap is20 minutes. All SIX bridge closures pass, including
`original_F`, with at most propext, Quot.sound and Classical.choice. No custom
axiom or unfinished placeholder appears. `originalF` itself has no axioms;
F(1)=0 and F(2)=6 guards pass. Both submitted modules passed first try with no
proof-repair commit or weakened statement.

The unchanged default core passes with zero failures in both runs:10,160
Witness comparisons,10,160 boundary comparisons,60,960 necessary and60,960
sufficient comparisons,33 small-state decisions,511 lrs checks; seed20260904,
80 instances, words through6. This is that specific regression, not a claim
to execute every repository benchmark. Existing warnings remain unchanged.

Local execution used an isolated PARTIAL workspace, not a full source clone:
GitHub connector access worked, direct git network access failed DNS, and
Lean/Lake were absent locally. CI made real full checkouts and ran the actual
checks. No other contributor's local/unpushed state was inspected.

## 6. Review, attribution and handoff

Independent mathematical review is still PENDING. Requests in #37 and #69
identify the exact artifacts; neither an acknowledgement, these independent
algorithms, nor kernel replay is represented as a separate-agent review.
The acceptance/integration gate therefore remains with the coordinator.

The checked bridge settles F using the separately proved dependency. The
independent ordinary route remains valuable because it uses the unchanged
compiler and explains why saving one promotion suffices. Its full formal
composition is optional follow-up, not a missing premise of the checked bridge.
Confidence in the exact F theorem is high; the remaining review must verify
statement/formula alignment, imported-source pins and integration, and should
separately assess the independent ordinary argument.

All shared definitions/ledgers/AGENTS/import aggregators/toolchain/paper and
existing workflows remain unchanged. Six new branch-only files comprise this
contribution. The dependency belongs to `smaller-compiler-20260920-astra`;
no result about its construction is claimed here. The old universal U for the
old compiler remains false. No complexity, practical runtime, signature
extension or publication-priority claim is added.

After independent review, the coordinator can record F as checked with the
exact bridge and compiler pins, while retaining the old-U refutation and the
separate compiler provenance. This worker does not make that shared-ledger
change or close #69. Final scope release and immutable handoff receipts are
posted in #69/#37; no active/background writer is retained after release.
