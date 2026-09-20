# Original terminal witness bound F: one fewer promotion

Date: 2026-09-20. Actor: `f-only-astra-20260920`.
Workstreams A017/A018; issue #69; coordination #37.
Base: `19b06d4fed9da635d9b911f0e908d04e4fc4b099`.
Branch: `codex/f-only-astra-20260920`.

**Result: an ordinary proof of the exact original F, with Lean-checked critical
steps. Independent mathematical review is requested but not yet obtained at
this checkpoint. The complete F theorem is not yet a composed Lean declaration.**
No shared claim status is changed. The concrete compiler, its refuted old
universal weight contract, the separate smaller-compiler investigation, and
all core definitions remain unchanged.

## 1. Exact recorded target and proof obligation

The numerical part of C080 reads:

> Consequently every positive instance has a witness of length at most the explicit computable bound `F(1)=0, F(k)=2(k+1)*prod_{j=1..k-2}(T_j+2)` with `T_0=k+10` and `T_(j+1)=64k*T_j^(2T_j+2)`.

The preceding quantifier is every finite binary terminal instance with k
states. The product formula is for k>=2; the empty product gives F(2)=6.
The recorded statement does not assign F(0), and `Instance 0` is uninhabited
because it contains an initial state. The optional executable totalization
below gives 2 at zero, with no new zero-state input obligation.

Fix any k>=1 and a finite partial deterministic binary instance

    I = (Q, delta, s, Fin, Bad, G),  |Q|=k,
    delta : Q x {0,1} -> Option Q,
    s in Q, Fin and Bad subsets of Q, G subset of Q x Q.

Every f in Fin is terminal: delta(f,a) is undefined for both letters. There
are no other restrictions on s, Fin, Bad or the ORDERED relation G.
For a binary word w of length n, `Witness I w` means exactly:

* The run c(0)=s,...,c(n) is defined at every cut and avoids Bad, including c(0).
* c(n) belongs to Fin.
* For EVERY 0<=i<=j<=n, if w[j:] is a prefix of w[i:], then
  (c(i),c(j)) is not in G.

Thus diagonal pairs, every comparison with the empty terminal suffix, the
empty word, missing transitions and arbitrary final/Bad sets are retained.
This is the existing predicate in `lean/Subtail/Basic.lean`, not a replacement.

**Theorem (ordinary proof below).** For every such instance,

    (exists w, Witness I w)
      iff (exists w, Witness I w and length(w)<=F(k)).                 (F)

Only the forward implication requires work. A valid refutation would require
a terminal instance with a witness and an all-words proof that NO witness has
length <=F(k). A long emitted clause, an arbitrary long witness, and resistance
to a particular shortening rule do not satisfy that obligation.

The initial dated outline was committed BEFORE new searches, at `61666c2`.
It recorded the exact formula, the seven proposed proof links and their open
status. That checkpoint is preserved in this branch history. This note replaces
those open links with the arguments below and separates formal checks from
ordinary composition.

## 2. What is imported, and what is not

C082 proves, for the UNCHANGED concrete first-return preimage E, the larger
weight bound

    Uhat_k(t) = 64*k*t^(6*t^2+2).

Write X_0=k+10 and X_(j+1)=Uhat_k(X_j). In this note T always means the ORIGINAL
recurrence in section 1; X always means the corrected recurrence. C082's Fhat
uses k-2 corrected stages and, by itself, does not imply (F).

The proof uses three generic facts from the checked source:

1. Terminal accepted paths have injective border-state labels, INCLUDING the
   zero and full borders (`TerminalRank.borderState_injective`).
2. E has exact semantic preimage coverage and reconstruction for ANY query in
   the existing grammar and any safe reference, with ONE shared generated
   extension for the whole conjunction. No old weight assumption is needed.
3. If a safe B satisfies E(phi), there is a safe first-return C satisfying phi
   with

       |C|+1 <= (|B|+1)*(Uhat_k(weight(phi))+2).                       (BR)

   This is `RankQueryLengthBound.preimage_bounded`; its proof invokes the
   generic `compile_bounded` and `RankQueryWeightBound` results.

References are finite reversed words with actual original run-state labels.
A safe reference B of length m is nonempty, starts in a final state, follows
the original machine backwards, avoids Bad at every cut, and has all ordered
border-mask tests clear, including zero/full borders. `SafeReference`,
`FirstReturnExt`, the literal `prefixGraph` and query weights are unchanged.

The proof does NOT invoke `ClosureFor` for the current compiler: its old
universal weight conjunct is false. It does NOT apply the existing
`promoted_finish_bounded` directly to a different finishing query. The generic
bounded reconstruction (BR) is instead composed explicitly in section 7.
It also does not depend on the separate filtered/smaller compiler proposal.

## 3. One safe normalization and the improved proper-prefix rank

### 3.1 Delete only before the last initial-state visit

Suppose w is a witness and c(d)=s. Put v=w[d:]. Its cut i has precisely the
old state c(d+i). Definedness, Bad avoidance and finality therefore inherit.
If v[j:] is a prefix of v[i:], the SAME statement is

    w[d+j:] is a prefix of w[d+i:].

The old witness clears the same ordered state pair. This covers i=j and the
empty suffix j=|v| as well. There is no concatenation seam and hence no newly
created comparison requiring an unproved lifting assertion.

Choose d to be the LAST initial-state visit of w. The finite set of cuts is
nonempty because c(0)=s, so this choice exists. The resulting witness v has no
positive initial-state visit. This is one finite prefix truncation, not a loop
of arbitrary interior deletions. Alternatively, every globally shortest
witness has this no-return property. The proof needs only the last-visit form.

The exact suffix-inheritance and shortest-no-return statements are checked in
`FOnlyAstra.witness_drop_of_return` and `shortest_no_initial_return`.

### 3.2 Rank of every proper reversed prefix

Rename the normalized witness w; write n=|w|, rho=reverse(w), and r(j)=c(n-j).
For every j<n, ALL labels r(0),...,r(j) avoid s. The corresponding original
proper suffix is still an accepted terminal run, although its starting state
need not be the original initial state.

For an accepted word u, each border length b, including b=0 and b=|u|, labels
the cut at |u|-b. Distinct borders have distinct states: otherwise two nested
accepted prefixes would start at the same state, and the shorter one would
reach a terminal final before the longer one finished. This is the existing
terminal border-injection theorem.

There are at most k-1 available states when s is absent. Therefore that suffix
has at most k-1 borders INCLUDING zero, and at most k-2 positive borders.
Reversal preserves the set of border lengths. Consequently

    rank(rho[:j]) <= k-2  for every j<n,                             (R)

where rank is the number of positive borders, including the full nonempty
word. The full reversed word rho is deliberately EXCLUDED. Its final cut
has state s and can raise the rank to k-1.

`border_count_add_one_le_of_avoids` and `rank_le_of_avoids` check the improved
injection/count step. Its application to proper suffixes and reversal is the
ordinary argument just given.

## 4. The exact final-return finishing query

The old finishing observer forbids visiting the reference endpoint even on
its final move. Merely lowering that observer's promotion budget would be
wrong. We use a NEW QUERY with the SAME preimage compiler.

### 4.1 Literal masks and cursor

For a fixed safe reference B of length m>0, P(B) has vertices 0,...,m.
Let pi(u) be the longest proper border of nonempty u, with the empty border
permitted. Let K_B(v,a) be the longest prefix of B that is a suffix of
B[:v]a. The mask at vertex v records

    mask_B(v)[p] = OR over h in Borders(B[:v]) of G(p, B.label(h)).

In particular the mask contains the empty-border test. The full-reference
mask at vertex m is legitimate and includes the old endpoint label.

### 4.2 Definition of FinishPlus

For each q in Q use an observer with exactly k controls, the original states.
Its initial control is q and its accepting control is s. It starts at vertex
pi(B); as before, the clause has three variables and a two-control one-F-edge
atom from the old endpoint to pi(B), together with this finishing path atom.
An endpoint/state colour test requires q=B.label(m).

At graph vertex v with control q, a move on K_a to vertex u with control p is
permitted precisely when:

    v < m,
    u = K_B(v,a),
    delta(p,a)=q,
    p not in Bad, G(p,p)=false, mask_B(u)[p]=false,
    u<m OR p=s.                                                     (P)

The endpoint m is allowed only with control s and has NO outgoing observer
moves. At non-end vertices any control is allowed. Acceptance can occur at
any vertex with control s, including an empty path. No extra control is used.
This is a finite observer over the existing colours and directed labels; it
has no inverse edge, word-equality atom or hidden history parameter.

Taking the union over q gives `finishPlusQuery`. Each clause has weight

    1 + 3 variables + 2 atoms + (2+k) observer states = k+8 <= k+10.   (W)

`finishPlusObserver`, `finishPlusQuery` and `weight_finishPlus_le` are checked.

### 4.3 Exact semantics

Define NoEarlyReturn(B,C) by B extending into C with the same labels and

    for every m<j<|C|, m is NOT a border of C[:j].

The strict upper inequality is essential: a first later B occurrence may end
at the ULTIMATE cut. C=B is allowed. Then

    P(B) satisfies FinishPlus
      iff exists safe C extending B with final reverse label s
          and NoEarlyReturn(B,C).                                  (FP)

Here is a separate soundness and completeness proof.

**Soundness and all new comparisons.** Before the final step, the observer
stays at v<m. Suppose the word constructed so far is C, extends B, is safe,
and pi(C)=v. The standard literal failure update gives

    pi(Ca)=K_B(v,a)=u<=m.                                          (K)

This identity requires the SOURCE v<m, not a strict bound on its target u.
It is exactly the hypothesis pattern of `RankQueryFinishTrace.append_parent`.
If the new state is p, full-border decomposition gives

    mask_(Ca)(|Ca|)[p] = G(p,p) OR mask_B(u)[p].                     (M)

Indeed every proper border of Ca is a border of its longest proper border
prefix of length u; that prefix and all its labels, through u=m inclusively,
are inherited from B. Thus (P) clears EVERY new comparison, not a selected
subset. Existing cuts retain their words/labels/masks. The reverse transition
and Bad guard preserve the actual run and safety. This proves safe extension
by induction along the path.

When u=m, the new state must be s and the observer cannot move again. The
same mask identity remains valid; the comparison with the old endpoint is
not omitted. The checked `final_return_safe` and `final_return_witness`
formalize precisely this extra boundary step after an existing no-return
trace. If u<m, it is the existing finishing-trace safety step.

No interior constructed prefix can have a later B occurrence: its longest
proper border is the recorded cursor <m. At the end, the reverse state is s,
so the safe reference gives the original Witness upon reversing its word.
This handles an empty completion and either kind of final cursor.

**Completeness.** Let C be a safe completion on the right of (FP). If at a cut
m<j<|C| its longest proper border p were >=m, the occurrence of that border
would give a full B occurrence ending at

    e=j-p+m, with m<e<=j<|C|,

contradicting NoEarlyReturn. At j=|C|, p>m similarly gives an earlier return
e<|C|. Therefore the actual longest proper-border cursors are <m before the
ultimate cut and <=m at it. Reading the actual letters and reverse states of
C now follows (K). Its safety and full mask decomposition supply every guard
in (P). If the last cursor is m, the last actual state is s, as required.
This constructs an accepting path. The occurrence argument permits overlap:
no inequality such as j>=2m was assumed.

### 4.4 Quantitative finishing and valid shortening

On P(B), the observer product has (m+1)k vertices. An accepting path can have
all repeated product vertices removed while keeping its endpoints. This is
ordinary finite-graph path deletion in a FIXED graph and observer, not an
unjustified deletion from an original witness. It preserves every observer
guard. Each deletion strictly decreases path length and ends at a simple path.
If that path emits ell letters, ell+1<=(m+1)k. Reconstructing through (K)-(M)
gives a witness of length m+ell and hence

    length(w)+1 <= (m+1)(k+1).                                     (FB)

The exact loop-deletion invariant is the cursor/control product, and (M)
rechecks all comparisons created in the reconstructed word. No original
agreement profile or list of left contexts is required to stay unchanged.

## 5. Coverage with one fewer promotion

For normalized w of length n>=2, let

    H=max_{1<=j<n} rank(rho[:j]).

Then 1<=H<=k-2 by (R). For h=1,...,H let m_h be the first position attaining
rank at least h. The first threshold cannot skip a rank because
rank(u)=1+rank(u[:pi(u)]). Thus rank(rho[:m_h])=h and m_1=1.

Successive first milestones give safe FIRST-RETURN extensions B_h to B_(h+1).
For completeness, put t=m_(h+1), p=pi(rho[:t]). The recurrence gives rank of
the prefix at p equal to h, so p>=m_h. If p>m_h, truncate its final occurrence
to length m_h: a copy of B_h ends at e=t-p+m_h<t. It is a proper border there,
so that earlier prefix has rank at least h+1, a contradiction. Hence p=m_h.
An earlier return of B_h between m_h and t would give the same contradiction.
The equality at t and the absence of an earlier return are precisely the
first-return condition, including overlaps and adjacent cuts.

After the last proper milestone B_H, there is no return before the ultimate
cut n; such a proper prefix would have rank >H. A return at n may occur and
is exactly what FinishPlus permits. Thus B_H satisfies FinishPlus by (FP).
The chain from the safe one-letter B_1 to B_H has H-1<=k-3 promotions.

This is the weakest semantic improvement needed here: existence of such a
chain for the particular finishing query. It is not an assertion that all
accepted words, all compiler diagrams or all witnesses admit a universal
local shortening operation. For a normalized one-letter witness the final
length conclusion is immediate and this milestone argument is unnecessary.

## 6. Finite query preimages preserve one whole extension

Let E be the unchanged concrete preimage and define Q_0=FinishPlus and
Q_(j+1)=E(Q_j). This uses exact iteration, not a claim that the old finisher
or old conditional ClosureFor has changed. Generic semantic completeness
applied backwards along the chain in section 5 says P(B_1) satisfies Q_(H-1).
Every intermediate object is finite and effectively constructible.

The scalar bounds apply to the WHOLE query conjunction. In (BR), coverage
first fixes ONE extension and ONE existential assignment. Its paths may be
normalized in their fixed product graphs, while the extension itself remains
fixed. Reconstruction chooses common intervals carrying every active observer
coordinate, and restores all tests, equalities, disequalities, endpoints,
seams and repeated traversals on ONE reconstructed word. Coincident marks and
zero-length paths retain the existing semantics. No separate per-atom word
existence argument is substituted for this generic theorem.

The query may have arbitrary repeated observations after iteration; (BR)
already bounds the unchanged compiler's larger syntactic envelope. No claim
about a smaller representation or per-atom pruning is made in this workstream.

## 7. Bounded reconstruction and global termination

By (W), generic weight monotonicity and C082's universal corrected weight
bound, weight(Q_j)<=X_j. From a safe B satisfying Q_j with j>0, (BR) yields a
safe first-return C satisfying Q_(j-1) and

    |C|+1 <= (|B|+1)*(X_j+2).

Induction on j, ending with (FB), therefore yields SOME original witness w'
with

    |w'|+1 <= (|B|+1)(k+1)*prod_{t=1..j}(X_t+2).                   (LR)

The induction order matters: the first reconstructed factor is X_j+2; the
remaining factors are X_(j-1)+2 down to X_1+2. All factors are >=1. Starting
from a one-letter reference and j=H-1<=k-3 gives, for k>=3,

    |w'|+1 <= B(k):=2(k+1)*prod_{t=1..k-3}(X_t+2).                 (B)

There is no circular use of F in this proof. Coverage comes from a given
witness, not from a guessed length bound. Normalization is one last-visit
suffix truncation. Rank chains have at most k-3 steps. Quantitative unwinding
strictly reduces the finite iteration index. Within each fixed finite product,
removing a cycle strictly decreases the finite path length. Shared interval
reconstruction then revalidates all masks/observations. These are the global
termination measures; recurrence in the original machine is not discarded.

## 8. The exact arithmetic comparison, now checked in Lean

Put a=64k. For all j, X_j>=k+10 and a<=X_j^4. The latter follows from k<=X_j
and 64<=X_j^3. We prove by induction the one-stage lag

    6*X_j^2 <= T_(j+1).                                            (L)

For j=0 the old recurrence gives
64k*(k+10)^(2(k+10)+2)>=6*(k+10)^2. For the induction, let x=X_j and
y=T_(j+1), so x>=11, a<=x^4, y>=6x^2. Then

    6*(a*x^(6x^2+2))^2
      = 6*a^2*x^(12x^2+4)
      <= x^(12x^2+14)              [6<=x^2 and a^2<=x^8]
      <= x^(4y+4)                 [y>=6x^2 and x>=3]
      = (x^2)^(2y+2)
      <= y^(2y+2)
      <= a*y^(2y+2).

This is (L) at j+1. In particular X_j+2<=T_(j+1)+2. Therefore, for k>=3,

    prod_{j=1..k-3}(X_j+2)
      <= prod_{j=2..k-2}(T_j+2)
      <= prod_{j=1..k-2}(T_j+2).

The original product has one spare factor T_1+2. Consequently B(k)<=F(k),
with EXACTLY the original exponent, seed, prefactor and indices. No numerical
approximation or evaluation of an enormous tower is used.

`budgets_lag`, `growth_lag` and `one_less_product_le_originalF` check this
comparison against the existing old and corrected Lean recurrences. This
resolves the arithmetic link independently of the proposed semantic saving.

## 9. Small states and conclusion

If an empty witness exists, it already satisfies the bound. For k=1, any
accepted nonempty word would begin at the only state, which is then final
and terminal; impossible. Thus F(1)=0 is exact.

For k=2, normalize at the last initial visit. If a nonempty witness remains,
all its positive cuts use the one other state. Its endpoint makes that state
final and terminal, so there cannot be more than one letter. The witness has
length <=1<=F(2)=6. `original_F_small` independently checks the exact original-F
statement at k<=2 by specializing the existing checked C082 endpoint.
There is no k=0 instance. For k>=3, a one-letter witness is already short;
otherwise sections 3-8 yield a witness satisfying (B), hence length<=F(k).
The converse direction of (F) simply forgets the bound. This proves (F) in
ordinary mathematics, conditional only on the explicitly identified existing
checked semantic and reconstruction theorems, not on the false old U. QED.

## 10. Falsification, failures and independently justified fixtures

The preserved failures were read before new searching: the minimal-witness
note's state-loop deletion creates a new flagged border; the overlap audit's
two aligned deletions can destroy overlapping equalities; recurrent residuals
can have identical finite summaries but incompatible left contexts; and the
old U counterexample concerns oversized emitted clauses, not shortest words.
None is reclassified as a counterexample to F.

A shortcut in the new route is genuinely false: reducing the old finishing
budget WITHOUT changing its endpoint rule. On the terminal chain
0 --0--> 1 --0--> 2, with initial0, final2, no Bad or flags, 00 is the unique
accepted word. Its one-letter reversed reference B=0 has labels (2,1).
The old finish query fails on B because it must return to the endpoint to
reach state0. FinishPlus succeeds and reconstructs 00. The four-state unary
chain and B=00 give an OVERLAPPING final return reconstructing 000. Both
boundaries are literal Python regressions; the first is also a Lean-evaluated
`#guard` against the existing and new query semantics.

The independent harness imports NO Subtail implementation. Its forward
Witness test examines every pair i<=j by literal string slices; its reverse
predicate enumerates literal borders; its finishing test uses a finite BFS on
(cursor,original-state). Every produced word is rechecked by the independent
forward predicate. Shortestness for found words is certified by exhaustive
increasing-length enumeration of ALL shorter binary words. The unary-chain
fixtures have a separate all-length proof: each has exactly one accepted word.

The expanded receipt contains 131,072 three-state table/flag annotations
(initial0, sole terminal final2, Bad empty; 256 partial tables x 512 arbitrary
ordered flag sets), all 12,820 one/two-state terminal annotations, and 1,000
seeded random inputs with 3-8 states. It also includes arbitrary safe-reference
soundness and bounded completion coverage, the published recurrent shared-
exponent fixture, last-initial-visit examples and rank-saturating unary chains.
These are tests of the proof's critical predictions, not an exhaustive check
of a huge F or an all-input theorem derived from statistics.

Expanded results: 8,253 found minima pass the saved-rank/FinishPlus route;
180 fail old Finish but pass FinishPlus on the selected reference; 16 minima
have overlapping final returns. Eight unique-word chains exercise 0 through
7 actual milestone promotions. Fifty-two flagged chain variants have a
certified all-length NO answer because their unique accepted word fails a
specified diagonal, nonempty-border or empty-border comparison. They are
negative fixture oracles, NOT counterexamples to a positive witness bound.

The three-state cap leaves 123,440 annotations UNKNOWN, and the random cap
leaves 389 UNKNOWN. These are not claimed negative instances. The earlier
#69 checkpoint reported 8,248/161/8; the expanded harness adds fixture families
and extra random draws, so its versioned receipt supersedes those counts.
No mathematical conclusion depends on either corpus size.

## 11. Commands, environments, revisions and actual validation

### Local independent experiment

The local directory is an isolated PARTIAL workspace, not a full clone.
Direct git network access failed DNS and Lean/Lake were absent locally;
GitHub connector read/write was available throughout. No other contributor's
local worktree, stashes or unpushed state was inspected.

    cd /mnt/data/subtail-f-only
    timeout 40 python3 experiments/f_only_astra.py \
      --seed 2026092069 --trials 1000 --word-cap 10 --census-cap 8 \
      --output results/f-only-astra.json

Python 3.13.5; Linux 6.18.44 x86_64, glibc2.41. Final recorded elapsed time
1.352611 seconds (diagnostic, not a matched performance benchmark). Wall cap
40 seconds; no additional memory cap was imposed. One/two-state test words
are enumerated through length5, the three-state census through8, random
witnesses through10; bounded safe-reference completions add at most4 letters.
The recurrent fixture uses m,n=1..6 and z=1..4. Seed is 2026092069.

Final harness SHA-256:
`c6d90046defd3ef086a2e8039588dfb6a59fec0209737d5af1c84877c1c60f5d`.
The JSON records the complete counts and reports
`PASS_BOUNDED_CHECKS_NOT_GLOBAL_PROOF`. Its review/Lean fields explicitly say
those are separate from this Python run, not that CI was never executed.

### Actual Lean execution, not a planned check

Source module commit: `a867c756046b0cabbd97c55ce7abb83d2794f172`.
Checked checkout: `1cde3445828b6625168fc33235a1070cb1794cb9`.
Actions run: `35516715375`; job: `106093784899`; conclusion: SUCCESS.
Host Ubuntu24.04.5 x86_64; Lean4.33.1, Lake5.0.0-src+819816b.
The first submitted module passed; no proof-repair commit was needed.

The NEW branch-only `.github/workflows/f-only-astra.yml` runs:

    cd lean
    lake build +Subtail.RankQueryLengthBound
    mkdir -p .lake/build/lib/lean
    lake env lean -o .lake/build/lib/lean/FOnlyAstra.olean FOnlyAstra.lean
    lake env leanchecker FOnlyAstra
    # Reject unfinished placeholders/custom axioms; audit all 20 named closures.
    cd ..
    timeout 600 python3 scripts/check_lean.py

The job has a 20-minute wall cap. Existing toolchain and existing workflows
are unchanged. The runner made its own full checkout; this does not turn the
local partial workspace into a full repository clone.

All 20 named axiom audits passed. The four new runtime definitions
`finishPlusObserver`, `finishPlusQuery`, `oldGrowth`, `originalF` have no
Classical.choice dependency; proof closures use at most the repository's
standard propext/Quot.sound/Classical.choice set. No new axiom or unfinished
placeholder occurs. New-module kernel replay passed. The unchanged default
core passed with zero failures: 10,160 Witness checks, 10,160 boundary checks,
60,960 necessary and 60,960 sufficient checks, 33 small-state decisions and
511 lrs checks, seed20260904, 80 instances, words through6. This is that
specific regression, not a claim to run every repository benchmark.

## 12. Review boundary, remaining work and proposed integration

The proof above is the author's complete ordinary argument. The literal
Python algorithms provide independent computational checks; Lean provides
actual kernel checks of the listed critical steps. Neither is an independent
mathematical review of the whole composition. Review requests were posted in
#37 comment5750401444 and #69 comment5750400657; no response is presumed.

The complete original-F Lean endpoint remains UNDECLARED. The outstanding
formal composition is (FP), its bounded finishing corollary, the proper-prefix
milestone application and the generic quantitative unwind with FinishPlus.
The new formal boundary-step theorem and the recurrence comparison are already
checked, so those are not left as unstated assumptions. A reviewer should
particularly check the inclusive target m in (M), the strict final-cut bound
in NoEarlyReturn, the single shared extension in (BR), and product indices.

The exact proposed final Lean statement is:

    theorem original_F (I : Instance k) (ht : TerminalFinals I) :
      (Exists fun w : Word => Witness I w) <->
      (Exists fun w : Word => And (Witness I w) (w.length <= originalF k))

This is the proposed signature in namespace Subtail.FOnlyAstra. The definitions
and checked critical declarations are in `lean/FOnlyAstra.lean`; the displayed
final statement is not presented as an already checked declaration.

Confidence is high in the ordinary proof's mechanism, especially the boundary
mask and arithmetic now checked by Lean; review of the remaining composition
is still required before a shared status promotion. The original old-U
refutation stays intact. No complexity classification, practical runtime
improvement, signature extension or smaller-compiler theorem is claimed.

Suggested integrator text AFTER review: record that original F has this
separate proof using last-initial-visit normalization, final-return finishing
and one fewer C082 promotion, without repairing the false old universal U.
Keep the smaller-compiler question separate. Do not apply that ledger change
on the strength of this unreviewed checkpoint alone. All shared ledgers and
core sources remain untouched; release/publication receipts belong in #69/#37.
