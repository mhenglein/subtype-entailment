# Collective flag transport, exact gap equivalence, and cross-gap certificates

Date: 2026-09-08. Workstreams: A012/A017. Reviewed main:
`5f65593175b6639e35cef3e9f20016d9600069ad`.

**Status: written all-length proofs and executed independent-algorithm checks.
Independent mathematical review pending; not Lean-checked. This contribution
DOES NOT decide unrestricted Problem 1.7.** The new finite normalization
terminates, but completeness of a final existence/refutation procedure is not
proved. Section 9 records an explicit limit of one proposed closing procedure.
No priority claim or new global C/E number is assigned.

This continues the preceding exact one-letter flag-transport work and reviews
the current main regular-decoration obstruction. It does not insert a top
constructor, replace arbitrary trees by finite trees, or claim a new semantic
subtype reduction. All results below concern the recorded binary terminal
BorderAvoid model. Transfer to subtype entailment retains C030/C031 and the
forward bridge's existing proof statuses.

## 1. Three relations which must not be conflated

Fix a finite partial deterministic binary automaton I with initial state s,
terminal accepting states F, and forbidden states Bad. Let R be the regular
language of defined accepted words avoiding Bad. R is independent of the flag
relation. Write c_w(i) for the run state after i letters of w, N=|w|.

For an ordered flag relation G define

    D_G(w) = {d : exists i, 0<=i<=i+d<=N,
                    (c_w(i),c_w(i+d)) in G,
                    w[i+d:] is a prefix of w[i:]}.

The word is a witness exactly when w is in R and D_G(w) is empty. d=0 records
diagonal failures; d>0 includes comparisons with the final empty suffix.

A *gap implication* G <=gap H means

    for every w in R, every d>=0: d in D_G(w) implies d in D_H(w).

Gap equivalence is equality of these sets for every word. It implies equality
of witness languages, but is stronger: two annotations can reject the same
word at different gaps. A counterexample to gap implication need not be a
witness of either instance.

An *aligned occurrence* is one particular comparison (w,i,j), with d=j-i.
Moving that occurrence along a match preserves d; comparing non-adjacent
copies of a periodic suffix can change it to 2d,3d,... . This is the distinction
between the first two constructions and the periodic-grid rule in Section 7.

Terminality supplies the following fact, used repeatedly: two matching suffix
occurrences cannot have equal states at any aligned position. Otherwise the
earlier run reaches the terminal accepting state before the complete word
ends. This is nonmerging, NOT a prohibition on recurrence of the pair itself.

## 2. Collective backward transport with a sound cyclic proof

The previous one-letter rule required uniquely determined predecessor EDGES.
The new rule permits arbitrarily many predecessor states and cyclic proofs.

Let B contain G. For every extra pair (r,t) in B\G require:

1. r is not the initial state;
2. both states have nonempty incoming transition sets, and every incoming
   transition to either state carries one common letter a;
3. every pair (p,q) of incoming source states, with p--a-->r and q--a-->t,
   belongs to B.

Only distinct pairs with nonfinal first coordinate are added. Original
boundary/diagonal flags are retained.

**Theorem 1.** If these local conditions hold, then G and B are gap equivalent.

*Proof.* G subset B gives one inclusion. For the reverse let (r,t) in B\G
occur at agreeing cuts i<j. Since r!=s, i>0; necessarily j>0 as well. The
actual preceding letters at both cuts are a by condition 2. Prepending that
letter extends the agreement to cuts i-1,j-1. Their states form a pair in B
by condition 3. If the new pair is in G we are done. Otherwise repeat.
Each step decreases the nonnegative source index i. A step cannot end at an
extra pair with source index zero, because every extra first coordinate differs
from s. Thus a G pair is reached after finitely many steps, at the SAME gap.
The proof graph may contain cycles; the occurrence index, not graph acyclicity,
is the well-founded measure. Empty target suffixes are covered by prepending
one letter in exactly the same way. No diagonal is added. QED.

The greatest such B is computable. Start with G plus every pair satisfying
conditions 1 and 2; repeatedly remove extra pairs whose predecessor-pair set
is not contained in the current set. At most k(k-1) removals are possible.
At the fixed point every required rule is present, so Theorem 1 applies.
`backward_closure` implements this greatest fixed point.

For removing old flags, use the finite synchronized pair graph. Its vertices
are (p,q), p!=q, p nonfinal, and its letter edges follow both defined transitions
without merging or entering a final on the left. Endpoints have q in F. If
EVERY path from an old G root to an endpoint meets a proposed H, every G
violation contains an H violation with the same gap. This is a sufficient
finite graph test, not an assertion that every graph path is realizable.
Together with H subset B it certifies G ==gap H. Diagonals are preserved
separately. `verify_rewrite` recomputes both gates from the actual input table.

### The latest six-state barrier is repaired

The current main barrier has this table, start 0, sole final 5:

| state | 0 | 1 |
|---|---:|---:|
| 0 | 1 | 2 |
| 1 | 1 | 2 |
| 2 | 3 | undefined |
| 3 | 3 | 4 |
| 4 | 5 | 2 |
| 5 | undefined | undefined |

Its flags are G={(0,2),(0,3),(1,2)}. Main proves that all candidates

    0^n 1 (0^+11)* 0^m 10, n>=0,m>=1,

are bad, and proves the stronger obstruction to regular candidate-covering
separator decoration with these flags fixed.

Add (1,3). All incoming edges to states 1 and 3 carry zero. Their predecessor
pairs are (0,2),(0,3),(1,2),(1,3): the first three are in G and the fourth is
the guarded recursive rule. Thus the addition preserves every bad-gap set.
Every old (1,2) violation starts with zero and advances to (1,3). Consequently
we may also remove (1,2), leaving

    H={(0,2),(0,3),(1,3)}.

The earlier unique-predecessor-edge transport has NO moves on this table;
this example genuinely uses collective premises.

The only unflagged positive-time part after an H root is now
(2,4)--0-->(3,5): (1,3) itself is flagged and its zero loop is no longer
eligible as the interior of a last-aligned comparison. Thus every last-aligned
H violation has length at most two. The word 1010 attains two. The previous
finite necessary automaton is now exact at (L,D)=(2,0), and its 14-state
exhaustion proves NO. The exact gap-saturation implementation independently
obtains the same bound, using a 24-element joint monoid.

**The separator colouring did not improve:** all zero edges remain marked.
What changed is which occurrence is last-aligned. This does not contradict
the main barrier, whose hypothesis explicitly keeps the flags unchanged.

## 3. Maximal periodic tails make gap implication exactly decidable

The forward pair-graph certificate above is conservative. An exact decision
is possible for the WHOLE gap relation, including earlier same-gap comparisons.

Fix w in R and 1<=d<=N. Let T be its longest suffix having period d, and write
w=xT. Every word of length d has period d, so |T|>=d. Put y=T[:d], divide
|T|=e*d+r with 0<=r<d, and split y=uv at |u|=r. Then

    w=x(uv)^e u,  v nonempty, e>=1, d=|uv|.             (1)

Maximality has a particularly simple exact guard:

    x=epsilon OR last(x)!=last(v).                    (2)

Indeed, if x is nonempty, extending T left by its preceding letter preserves
period d exactly when that letter equals the last letter of y, which is the
last letter of v. If the two letters differ, every putative earlier agreeing
comparison with gap d crosses that mismatch and fails. Thus ALL agreeing
comparisons with gap d start at or after |x|.

The states at positions |x|+h*d for h=0,...,e are pairwise distinct. If the
states for h<h' coincided, applying the later copy's remaining suffix from
the earlier state would reach a terminal final strictly before w ends. Hence

    e<=k-1.                                          (3)

The common compared suffix is z=(uv)^(e-1)u. Starting at pair
(c_w(|x|),c_w(|x|+d)), its synchronous run on z enumerates exactly every
agreeing cut pair with this gap, including the final empty suffix.

**Theorem 2.** Gap implication G <=gap H, and therefore gap equivalence, are
effectively decidable on every finite terminal input.

*Finite construction.* The d=0 difference is ordinary regular reachability:
find an admissible word visiting a G-diagonal state and no H-diagonal state.
For positive d use one finite complete machine consisting of:

- the original single states, with Bad transitions disabled;
- distinct synchronized pairs, with a Boolean recording any G hit;
- an absorbing failure state reached on H hits, undefined transitions, a
  merge, or a left final;
- a two-state last-letter observer.

A flagged initial pair is observed BEFORE reading; otherwise an empty suffix
or root-only hit would be lost. Enumerate its finite joint transition monoid.
For each common u action, nonempty v action, exponent 1<=e<=k-1, and reachable
head endpoint, require (2), compute the first-gap target, and apply the action
of z. A terminal pair endpoint, a recorded G hit and no H hit certify a word
with d in D_G(w)\D_H(w). Reconstruct the factors using the SAME representatives
at each occurrence. The last-letter observer distinguishes the empty identity
from every nonempty word and retains the guard on v.

Every returned word satisfies (1)-(2); hence no H violation at that gap was
hidden earlier in the head. Conversely the maximal-periodic-tail decomposition
of any separating (w,d) supplies one enumerated case. Replacing its factors
and head by representatives preserves the whole joint action, the head guard,
and admissibility. This proves both implications and termination. QED.

**Why the head guard is indispensable.** For the unique terminal path 000,
G={(1,2)} and H={(0,1)} both detect precisely gap 1. Looking only at x=0 and
the later periodic tail 00 would see G and miss the earlier H. Condition (2)
rejects that nonmaximal split; the correct algorithm returns IMPLIES.

No unrestricted quantified word-equation solver is invoked. The quantified
conclusion is specific to ONE selected gap per witness and its maximal
periodic tail. It is not a decision of absence of all G gaps simultaneously.

## 4. A separate exact orbit algorithm

`orbit_implication` does not enumerate functions. It enumerates an injective
tuple Q=(q_0,...,q_e), e<=k-1, representing the states after whole uv copies.
Read a common u simultaneously from all e+1 coordinates, recording G hits and
rejecting H hits at each ADJACENT coordinate pair. When the last coordinate
is final, drop it and read a NONEMPTY common v from the first e coordinates.
The result must equal (q_1,...,q_e). Check the head's last-letter condition.

These equations give delta(q_h,uv)=q_(h+1) and delta(q_e,u) in F. Adjacent
coordinates during u and v exhaust the comparisons at gap d, including their
boundaries. Joint reading enforces one common word for all coordinates.
The graph of tuples, phase, hit flag and last letter is finite. Exhaustion
therefore supplies an independent exact backend for Theorem 2. It also
reconstructs concrete separating words, checked by the literal gap predicate.

Both implementations keep resource limits explicit. Caps produce UNKNOWN;
removing them gives the finite decision. The Python breadth-first implementation
is not advertised as a space-efficient complexity-bound implementation.

## 5. The greatest gap-preserving annotation and its optimality

Define

    G* = {a in QxQ : {a} <=gap G}.

Theorem 2 computes this relation by finitely many implication queries. It
contains G. By taking the union of the individual implications, G* ==gap G.
Conversely if K ==gap G, each pair in K individually implies G, so K subset G*.
Thus G* is the UNIQUE GREATEST gap-equivalent annotation on this fixed table.
A cap may return only a sound partial extension, never a claim of maximality.

There is a useful optimality statement. Fix any bad (w,d). Among its agreeing
positions, the last G* hit is at least as late as the last hit of any other
gap-equivalent K, because K subset G*. A last-aligned violation for a gap is
exactly the rightmost flagged occurrence at that gap. Therefore G* minimizes
the target suffix length for each bad (w,d), simultaneously over all words.
It also minimizes any FIXED nonnegative occurrence cost of that suffix.

In particular:

    some gap-equivalent K has bounded last-aligned lengths
      iff G* has bounded last-aligned lengths.

This is a complete synthesis/optimality theorem for this stated normalization
class. It does NOT optimize a separator colouring that itself changes with the
flags; that would not be a fixed occurrence cost. It does not cover all
witness-language equivalences, since those may change the bad-gap set.

## 6. An obstruction to every gap-preserving length normalization

Use seven states, start 0, final 6:

| state | 0 | 1 |
|---|---:|---:|
| 0 | 1 | undefined |
| 1 | 1 | 2 |
| 2 | 3 | undefined |
| 3 | 3 | 4 |
| 4 | 5 | undefined |
| 5 | 5 | 6 |
| 6 | undefined | undefined |

Candidates are 0^n1 0^m1 0^l1 for n,m,l>=1. Let

    G={(2,5),(3,4),(0,3),(1,2),(0,4)}.

Flags (2,5),(3,4) respectively reject m<l and m>l, so any witness needs m=l.
Under that equality, (0,3),(1,2) reject n<m and n>m, so it also needs n=m.
Flag (0,4) rejects n=l. Thus the entire candidate language is NO.

For w_t=(0^t1)^3, t>=1, the ONLY violation is at (i,j)=(0,2(t+1)), with flag
(0,4), gap 2(t+1), and target length t+1. The exact G* computation adds 24
pairs, but each is vacuous: a separate exact singleton-versus-empty query
proves it has no agreeing occurrence on any candidate. The executable result
includes all original implication checks and separately counts these vacuity
proofs.

Thus G* has the same sole violation on every w_t. Section 5 proves that NO
gap-equivalent annotation on this fixed automaton can have bounded last-aligned
lengths. Moreover every finite Necessary(L,D) language remains inhabited under
any such annotation: choose t with t+1>L and 2(t+1)>D. There are no new active
occurrences available to create a shorter test at that gap.

This is a flat three-block instance, already within the repository's exact
fixed-schema/arithmetic scope. It is not a new hardness family or a barrier to
all separator methods. Its role is to refute completion of the GAP-PRESERVING
length/budget route, even with the mathematically greatest possible annotation.

## 7. Cross-gap periodic-grid implication

The obstruction above motivates a different sound inference. For a proper
comparison rooted at (p,q), with source i and gap d, its suffix w[i:] has
period d. Define its periodic grid to contain every agreeing pair (a,b) with

    i<=a<b<=N,  b-a a positive integer multiple of d.

**Theorem 3.** It is decidable whether EVERY admissible occurrence of a
specified distinct pair (p,q) has a G violation on its periodic grid. If yes,
adding (p,q) preserves the entire witness language.

*Proof and algorithm.* The occurrence has form w=x(uv)^e u with v nonempty
and e<=k-1, but x need NOT satisfy the maximality guard: the grid starts at
the supplied source i, not at the earliest matching position. Enumerate the
same injective tuple (q_0,...,q_e), fixing q_0=p and q_1=q. Read common u,
then nonempty common v, with the same endpoint conditions as Section 4.
Now reject G hits at EVERY ordered pair of coordinates, not only adjacent
ones. Two coordinates h<h' correspond to gap (h'-h)d. The u and v phases
exhaust all cut positions and all positive integer multiples of d within the
periodic tail. Hence an accepting orbit is exactly an antecedent occurrence
with NO G hit on its grid.

If no orbit exists, every antecedent occurrence forces some G violation, so
no old witness is removed by adding it; G is retained, so no old non-witness
becomes a witness. Every loop in the search is finite-state; e is bounded, so
uncapped exhaustion terminates. QED.

A failed test returns NOT_CERTIFIED with a real antecedent occurrence lacking
G on that grid. G may still occur at another gap or before the source. This
is NOT a witness verdict and NOT a counterexample to unrestricted semantic
implication. Diagonal antecedents are outside this rule. Existing diagonal
conclusions may of course be used by other rules.

### The seven-state contradiction is automatically closed

Add (0,2) to the preceding seven-state instance. A comparison from the first
block entry to the second requires

    0^m1 0^l1 prefix of 0^n1 0^m1 0^l1.

Delimiter alignment forces n=m=l. The existing (0,4) comparison is then at
TWICE the antecedent gap. The generic periodic-grid checker proves the
implication by exhausting 14 orbit states across two tuples. This addition
is NOT gap equivalent; the exact gap backend supplies a separating gap.

The guarded backward rules can now add, in order,

    (1,3), (2,4), (3,5), (4,6).

For (1,3), predecessor pairs are (0,2),(0,3),(1,2),(1,3).
For (2,4), the sole predecessor pair is (1,3) on letter 1.
For (3,5), they are (2,4),(2,5),(3,4),(3,5).
For (4,6), the sole predecessor pair is (3,5) on letter 1.

Every candidate visits state 4 before final 6. The derived flag (4,6)
therefore gives an empty-suffix contradiction and boundary normalization
eliminates the entire candidate language. This is a finite machine-generated
proof crossing gaps, followed by a decidable cyclic proof; it is not merely
a restatement of the three-variable arithmetic argument.

## 8. Finite saturation, and exactly what terminates

`power_transport.saturate` alternates guarded backward closure and all
periodic-grid implication queries for absent pairs. It adds only certified
flags. At most k^2 distinct flags can be added, and each uncapped query is
finite. Thus the normalization itself always terminates and preserves the
complete witness language.

The result is SATURATED_IN_CALCULUS, NOT a final YES/NO answer. A cap keeps
verified additions and returns PARTIAL. Even complete saturation may need an
existing necessary-language, arithmetic, or other exact certificate. No
completeness theorem says every NO input is closed by these rules.

A finite experiment exhausts all 4,096 effective flag relations on the fixed
seven-state three-positive-unary-block table. A separately proved weak-order
oracle gives 709 YES and 3,387 NO. The calculus derives a final-column
contradiction in ALL 3,387 NO cases. This is a complete FINITE classification
of annotations on one table, not an all-state normalization theorem.

The oracle is complete because cross-block comparisons depend only on the
weak order/equality pattern of the three positive lengths. There are 13 such
patterns. For stages i<j, require equality of the intervening later reference
blocks; conditional on that guard, the four effective flags are determined by
ni<nj, ni=nj, ni>nj, or always present at empty data tails. Consecutive positive
ranks realize every pattern. The checker separately compares that formula
with direct words for every weak order and each individual effective flag
through four stages.

## 9. Preserved failure: saturation plus bounded-length spectra is not complete

Here is a different seven-state instance, start 0, final 6:

    delta=((1,2),(1,3),(4,4),(5,5),(-1,0),(6,1),(-1,-1))
    G={(0,4),(0,5),(1,4),(1,5)}.

It is obtained from the repository's four-state one-flag example by a regular
history bit requiring an earlier zero transition from its original state 0.
Every accepted word consequently has such a zero, and its final zero starts
in state 5. The earlier source is state 0 or 1, so a flagged one-letter
violation always exists. Necessary(1,0) is empty (14-state exhaustion).

The full new calculus reaches a fixed point with these flags:

    (0,1),(0,2),(0,4),(0,5),
    (1,0),(1,2),(1,4),(1,5),
    (2,0),(2,3),(2,4),
    (3,0),(3,2),(3,4),
    (4,0),(4,2),(4,3),(4,5),
    (5,0),(5,2),(5,3),(5,4).

The checker rechecks that backward closure adds nothing and returns an actual
grid-free occurrence for each of the 14 remaining eligible pair queries.
Thus this is an exhausted fixed point, not an interrupted search.

Nevertheless put z_r=10 1^(3r+2)0 and w_r=0 z_r z_r for r>=0. At positions
1 and 1+|z_r| the pair is (1,5). Its later pairs are (3,1), (5,1), then the
cycle (1,3),(3,5),(5,1), finally (5,6). None is in the displayed saturated
relation. It is therefore a last-aligned comparison of length 3r+5 for every
r, while the same word also has the short decisive violation at another gap.

This refutes completion by **this finite calculus followed only by the
bounded last-aligned-length criterion**. It does not defeat Necessary(1,0),
which already solves the example. A portfolio including that check must retain
it. Nor does the example refute richer context-sensitive rules or a general
finite case-cover theorem.

## 10. Reproduction and evidence boundaries

    python3 experiments/check_collective_research.py
    python3 experiments/run_experiments.py
    python3 experiments/check_lastflag_spectrum.py

The new deterministic result is results/collective-gap-research.json, seed
2026090874. Important exact scopes:

- All 266 binary terminal tables through three states, fixed start 0 and
  sole final k-1, with every effective off-diagonal nonfinal G,H: 4,106
  monoid/orbit implication comparisons; 1,034 backward closures; 67,830
  raw words through length seven for bounded cross-checks. These words
  are NOT used to infer general NO.
- 240 complete increasing-index acyclic-language oracles, with 327 accepted
  candidates fully enumerated: 960 exact implication queries, 150 literal
  periodic-grid oracles, and 240 normalization checks. Bad states, multiple
  finals, empty languages and nonzero starts are included.
- 220 additional seeded cyclic instances: both exact implication backends
  compared, and 56,100 raw-word original/normalized/reversed checks.
- 1,096 reconstructed separating counterexamples independently checked by
  the literal comparison profile; 13 explicit boundary/input/cap regressions.
- The complete three-stage annotation census just described, with 1,968
  additional direct checks of the weak-order oracle through four stages.
- 16,383 raw words for the six-state equivalence; 64 of its original unique
  violation words; 216 three-block vectors and 64 escaping-budget words for
  Section 6; 24 separate exact vacuity proofs for the added gap-equivalent
  pairs. All 44 seven-state maximality queries and all 24 vacuity checks
  also agree with the independent orbit backend.
- For Section 9, 32,767 raw words, 862 accepted words, 33 growing-comparison
  words, and all 14 failed rule certificates at the exact fixed point.

No caps were hit in the enumerated backend/normalization runs; explicit
cap regressions deliberately return UNKNOWN. No five-state/general terminal
census is claimed. Tests substantiate implementations, not all-length proofs.
The latter are the mathematical arguments above.

The existing core and last-flag checkers are unchanged and are included in the
standalone replay. Their recorded source/result hashes are checked before and
after execution. This is a partial-snapshot local reproduction, not full
repository CI or a new Lean build. No remote publication is implied by these
local files.

## 11. What is still needed for Problem 1.7

The exact bad-gap theorem closes a new verification/normalization question.
The cyclic and periodic-grid rules provide a reusable finite proof calculus
that escapes the latest fixed-flag decoration barrier and a genuine cross-gap
contradiction. Neither supplies an existence-complete word/schema cover.

A full solution would need a proof that an effective combination of these
rules, regular candidate restrictions and/or symbolic cases certifies every
NO instance, or an unconditional computable witness bound, or an exact
undecidability reduction. Reaching a finite flag fixed point alone is not
that proof. The explicit limits in Sections 6 and 9 are mandatory regressions
for any proposed completeness claim.

The external not-contains theorem remains a technique source, not an imported
solution: Havlena et al., MFCS 2025, DOI 10.4230/LIPIcs.MFCS.2025.56, decides
one fixed negated-containment predicate under regular constraints. It does not
automatically quantify over all coloured internal cuts here. No theorem in
this contribution depends on that literature result.

Relevant repository dependencies: C016 boundary handling; C036/C038 terminal
nonmerging and exponent; the September 7 last-flag implementation; the
September 8 regular-decoration barrier; and the repaired C064 four-state
one-flag example. New statements remain written proofs pending independent
mathematical review.
