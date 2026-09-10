# Arbitrarily repeated source cycles: exact existential compilation

Date: 2026-09-10. Base: `f85ba3af769041349979e6130f1e2bc109b07c91`.
Workstreams A008/A017; existing dependencies C067/C068 and Q004.
Proposed canonical records C071-C072 / E045.

**Status: written proofs plus reproducible checks; independent mathematical
review pending, not Lean-checked.** This is an exact decision-theoretic
compilation for a SUPPLIED finite source-cycle power scheme. It is not a
complete cover for arbitrary terminal instances, and does not solve Problem
1.7. The practical string backend is incomplete and retains UNKNOWN.

The [route outline](2026-09-10-source-power-route.md) was written before the
supporting implementation. The main new implication is elimination of an
unbounded number of source-boundary obligations, not another fixed-word test.
All repeated words, rotations, tails, and suffix captures below share the same
assignments. No delimiter encoding or primitive-word assumption is imposed.

## 1. Setting and prior interface

I is the existing binary partial deterministic Instance, on Q={0,...,k-1},
start q0, terminal finals F, Bad states and ordered flags G. Missing transitions
reject. All paths below are safe, including endpoints. S is the set of sources
of G. For a state p, L(p,H) is the regular language of paths from p ending in H.
Write L_t=L(t,F); terminality makes L_t prefix-free. Write A_t for the regular
language having no prefix in L_t. Its (k+2)-state DFA is defined in C067.

C067 supplies a positive existential formula Phi_(p,t)(W), valid when W is
accepted from p, which says that NO suffix comparison from position zero ends
at a cut labelled t. Its exact construction is recalled here so the dependency
is visible:

    W in A_t
    OR exists V,X: W=VX, V in L_t, and
       (V is not a suffix of W
        OR exists D: W=DV and D in L(p,Q minus {t})).

There is at most one prefix V in L_t. A variable-dependent non-suffix test is
positive existential too. NS(V,W) is

    (exists R nonempty: V=RW)
    OR OR_(a!=b) exists R,T,Z: V=RaZ and W=TbZ.

If the right-aligned words disagree, use their longest common suffix Z.
Otherwise the only non-suffix case is that V properly extends W on the left.
This formula includes either empty word. No length predicate is used.

Every automaton language used in the construction is given by an explicit
finite automaton. Regex state elimination is only a practical serialization
choice, not the polynomial theoretical representation.

## 2. First-return loops replace the lexical primitivity restriction

Let B be a nonempty first-return word at p: its run starts/ends at p but
never visits p at a strictly internal position. B may be imprimitive as a
WORD; for example 00 can first-return around a two-state zero cycle.

**Lemma 1.** For such B,

    UB=BU and U in L(p,{p})   iff   U=B^m for some m>=0.             (1)

Proof. The reverse implication is immediate. For nonempty U, cancellation
induction on |B|+|U| shows that commuting words are powers of a common primitive
word r: B=r^a,U=r^b. (Cancel the shorter prefix from the longer until equality;
reassemble the common root.) Let a0 be the least positive return time of the
state p under the action of r. It exists since r^a returns p. Every positive
return time is a multiple of a0, by determinism of this finite orbit. A return
at a0<a would be an internal p-position of B, impossible. Thus a=a0 and a
divides b, giving U=B^(b/a). The empty U is m=0. QED.

First-return membership is regular: take a fresh initial copy of p with p's
outgoing transitions, stop at original p by removing its outgoing edges, and
accept only original p. This has k+1 states and excludes the empty word.

The guard is essential. On a p-state zero self-loop, B=00 and U=0 are both
p-loops and commute, but U is not a whole-number power of B. C070 used a
primitive marker block to avoid this issue; (1) instead uses the actual return
structure and works without a marker format.

## 3. The complete power-conjugacy calculation

Fix nonempty B and any word Q. Write uniquely

    Q=A B^ell,  ell>=0, with B NOT a suffix of A.                    (2)

For j>=0 ask whether

    B^j Q = D_j B^j.                                              (3)

When it exists D_j is unique, since it is a prefix of known length |Q|.

**Lemma 2.**

* For 0<=j<=ell, (3) always holds with D_j=B^j A B^(ell-j).
* For j=ell+1, (3) holds iff BA=D B for some D. Then D_j=B^ell D.
* For j>ell+1, (3) holds iff BA=AB. Then D_j=Q.

Proof. The first case is substitution. Cancel the last ell copies of B in
(3). For j>ell, B^j A must end in B^(j-ell). If |A|>=|B| this is impossible:
its final B would be a suffix of A, contradicting (2). Thus |A|<|B|.
For j=ell+1 the suffix test is exactly whether BA ends in B.

For j>ell+1, at least two final B copies must match. Put b=|B|,a=|A|<b.
The equality of these two copies gives B^2 A=E B^2 where |E|=a. If a=0 the
claim is immediate. Otherwise B^2 has period a: compare its prefix with the
copy shifted by a in this equation. Comparing a complete length-b block in
B^2 with the block shifted by a says that circular rotation of B by a fixes B.
Thus letters of B are constant on residue classes modulo gcd(a,b). Both E
(the length-a prefix) and A (the length-a suffix of B^2) are the same power
of that gcd-length block, and commute with B. Hence BA=AB. Conversely this
commutation gives (3) with D_j=Q for every j. QED.

No assumption on automata or primitive roots is used in this lemma. When B
loops at p, the target states delta(p,D_j) in the first case are exactly

    delta(p,A B^(ell-j)),

the exceptional target is delta(p,D), and every later target is already the
j=0 target delta(p,Q). This last fact, not merely a bound on overlap exponent,
is what makes the unbounded comparison list finite in the next section.

## 4. All repeated source boundaries of B^m Y (C071)

Suppose B first-returns at p, Y is safely accepted from p, and U=B^m. Consider
ONLY source positions at the displayed boundaries, including Y's start. Their
suffixes are B^j Y for j=0,...,m. Targets may occur ANYWHERE later, including
inside B copies, in Y, or at the terminal end. No boundary-only target
restriction is made.

Fix T={t:(p,t) in G}. We construct an exact finite positive existential formula
for absence of all these comparisons. It does not separately check other source
positions inside B or Y; the complete scheme will account for them.

### 4.1 Matches contained in a periodic prefix

Suppose a violating target suffix V at some displayed source B^j Y has
|V|<=j|B|. It is a prefix of B^j and therefore of U. It is also a suffix of
UY, at the same target state: adding m-j complete p-loops to the left does not
change its terminal run. Thus it is a violation at the EARLIEST displayed
source UY. Conjoining Phi_(p,t)(UY) for t in T eliminates every such match.
This argument includes the empty suffix. It does not claim that checking the
earliest source alone handles the remaining matches.

### 4.2 Every other match leaves a border of the tail

If |V|>j|B|, the matching prefix has form V=B^j P with nonempty P a prefix of
Y. Since V is a suffix of B^j Y and |P|<=|Y|, P is also a suffix of Y. Write
Y=QP. The target gap has length |Q| and the agreement is exactly

    B^j Q P = D_j B^j P,  equivalently B^j Q=D_j B^j.                (4)

Its target state is delta(p,D_j). Conversely, a nonempty border P of Y and
(4) with that state in T give a genuine forbidden comparison. Diagonal gaps
Q=epsilon are included; P=Y need not be discarded. Empty P belongs to the
periodic-prefix case, not this case.

All nonempty borders P of Y can be represented with at most k captures.
For each r in Q, either Y has no accepted prefix from r, or its unique captured
prefix P is considered. It is a relevant border precisely when it is nonempty,
it is a suffix of Y, and the actual state at that suffix cut is r. These are
exactly C067's no-capture, non-suffix and wrong-cut-state alternatives. Reusing
one common Y is essential. Terminal prefix-freeness makes the captures unique.

### 4.3 Express the entire exponent range without an integer variable

Fix one relevant Y=QP and decompose Q=A K as in (2), where K=B^ell.
By Lemma 1, K being a power is expressed by KB=BK and K in L(p,{p}).
Maximality is the positive existential clause NS(B,A).

We need every D_j in (3), for j<=m, to end outside T. Define a regular language
H_(p,s,T) on a pair of states: start at (p,s), read each bit in both coordinates,
reject undefined/unsafe transitions and any pair (p,t) with t in T, and accept
at every remaining pair. The state set is Q x Q. Since B is first-return,
while reading powers of B the reference coordinate equals p exactly at block
boundaries. Consequently H_(p,s,T) checks precisely the actual states at those
boundaries, INCLUDING both endpoints, without knowing B as a constant.

Define Guard(Z,K) by the finite disjunction over s:

    Z in L(p,{s}) AND K in H_(p,s,T).

There are two cases, both ordinary word equations:

* If K=J U (ell>=m), require Guard(AJ,U). This checks j=0,...,m.
* If U=K J with J nonempty (m>ell), require Guard(A,K), and also

      NS(B,BA)
      OR exists D: BA=D B AND D in L(p,Q minus T).                 (5)

  The guard checks j=0,...,ell. Formula (5) excludes the exceptional target
  at j=ell+1. Every larger j has the j=0 state by Lemma 2, already checked.

These equations automatically make J the appropriate power of B; no division
of lengths is hidden in the formula. In both cases the actual state path
inside Q is safe because Q prefixes Y.

### The exact repeated-boundary formula

Conjoin first-return membership of B, UB=BU, U in L(p,{p}), Y in L_p, the
initial Phi clauses, and the following clause for each r. Either Y in A_r,
or capture Y=P X, P in L_r, and take one of:

    P=epsilon; NS(P,Y); or Y=QP and
       [Q in L(p,Q minus {r}) OR the guarded power test above].

**Theorem C071.** This finite positive existential formula holds exactly when
all comparisons sourced at the displayed boundaries of UY are permitted.
All auxiliary variables are fresh except shared B,U,Y. The proof is the two
exhaustive capture cases and Lemma 2, in both directions. It covers overlaps,
diagonals, empty terminal suffixes, arbitrary Bad sets and multiple terminal
finals. It does not quantify over j, use string lengths, or assume a copy limit.

## 5. A missed-copy counterexample is not optional bookkeeping

Use start 0, terminal final 5, G={(0,2)}, Bad empty, and

    delta=((1,3),(-1,2),(0,-1),(4,-1),(-1,5),(-1,-1)).

Here B=010 first-returns at 0 and Y=101 is accepted from 0. On


    W=B^2Y=010010101,

the earliest source position zero has NO forbidden comparison. But the source
at position 3 has suffix 010101; its target at position 5 has suffix 0101,
a matching prefix, and the state pair is (0,2). W is not a witness.

The tail border P=1 leaves Q=10, with A=10,ell=0. At j=1,

    B A = 01010 = 01 B,

and delta(0,01)=2 is flagged. This is precisely the exceptional case. At j=2
no such conjugacy exists. Removing that case would let the finite formula
incorrectly accept W even though its earliest-source clauses pass.

The earliest-source predicate passes directly; the optional solver returns
UNSAT for the isolated conjugacy clause in the recorded tests. The forward
and reversed word predicates
independently confirm the full bad word. The complete free formula is not
claimed fast on this instance; the theoretical solver and practical string
engine are different objects.

## 6. Supplied source-cycle power schemes (C072)

A phase has a pivot p in S. It is either an ordinary source visit, or a
starred SOURCE-SIMPLE cycle with a supplied cyclic list

    (p=s0,s1,...,s_(d-1)),

of distinct source states. Its base B is an UNKNOWN concatenation of positive
safe paths between those successive states and back to p. Each segment has no
source at an interior position. Segment DFAs have k+1 states: a fresh initial
copy of the source, all original source states stopping, and the designated
next source as sole final. This makes each source occur once per base cycle,
though the source-free segments may have arbitrary nonflat recurrence.

A fixed finite scheme consists of h such phases and the bridges between them:

    W=C0 U1 C1 ... Uh Ch.

C0 reaches the first pivot at the first source visit. An intermediate bridge
Ci is a positive source-free-interior path from pivot i to pivot i+1. Ch safely
accepts with no positive later source visit. For a plain phase Ui=epsilon.
For a starred phase Ui is either empty or Ui=Bi^mi with mi>=1 and one Bi shared
by ALL iterations. An empty star does not require an inhabitant of its base
language. The compiler handles it in a separate disjunct.

First encode each active power using Lemma 1. Define the actual shared tail
Yi=Ci U_(i+1) C_(i+1) ... Uh Ch. Check Phi at the phase-exit source pivot p on
Yi. To check the sources inside Ui, split Bi=A_a C_a at each listed source
s_a and put R_a=C_a A_a. This is a first-return word at s_a. Introduce Va with

    Ui=A_a Va C_a.

Together with Ui=Bi^mi this fixes Va=R_a^(mi-1). Apply C071 to

    (pivot=s_a, base=R_a, power=Va, tail=C_a Yi).

Its displayed boundaries are exactly the s_a occurrences inside the repeated
phase. The exit-pivot source is checked separately, so it is neither omitted
nor required to occur inside the last base. Every source in the whole word is
accounted for by these clauses; bridges have none in their interiors. Later
phases and all earlier obligations concern the SAME words, not independent
choices of tails.

**Theorem C072.** The resulting positive existential word-equation formula with
regular constraints is satisfiable iff the supplied scheme contains a witness.
The construction is effective and finite even though every mi and every base
word length is unbounded. Soundness follows by partitioning actual source
positions as above and C071; completeness uses the given bases, bridges and
rotations of any witnessing scheme member as the common assignment.

The formula size with DFA atoms is polynomial in k and the explicit scheme
length (including its source lists). The languages H have k^2 states. The
applicable external result is Theorem 4 in Diekert, Gutierrez and Hagenah,
*The Existential Theory of Equations with Rational Constraints in Free Groups
is PSPACE-Complete*, arXiv:cs/0103018 (2001): the theorem is for free MONOIDS
with involution. Use its involution-free fragment, constrain every variable
to the original binary alphabet, and existentially prefix the fresh branch
variables. These are finite Boolean combinations of equations and regular
constraints; no cancellation in a free group or extra length arithmetic is
introduced. The same exact theorem mapping is recorded in C067.

Thus supplied-scheme existence is decidable and has a PSPACE upper bound.
No lower bound for this particular scheme format is asserted. Optional GNFA
serialization to regex may grow exponentially and is not the theoretical
polynomial reduction. The native Z3 engine is an incomplete practical backend,
not an implementation of the complete theoretical decision algorithm.

This is MIXED-FAMILY SYNTHESIS, unlike checking that every member of a proposed
family is valid. A scheme may contain both good and bad words; the existential
formula selects a good member if one exists. It also differs from C068, which
lists every source visit: here source visits inside a powered phase are not
listed and can be arbitrarily numerous.

## 7. What is still missing, and what is not claimed

The supplied scheme is not an automatic complete cover of a general Instance.
A run may use many different return words, change cycle traces, or require many
phases. Every finite witness has a trivial finite plain-visit scheme, so
increasing the phase bound gives a positive search; no effective all-input
phase bound follows. Q004 remains open. A complete existence-preserving family
of such schemes, or another terminating treatment of changes between return
words, is still needed for an unrestricted decision.

This result is not a generic theorem about iterating arbitrary word relations.
It exploits one unchanged first-return word per phase and actual loop paths.
It does not accelerate the two independent append accumulators that encode PCP.
Nor does it revive the refuted claims of source-simple witnesses, polynomial
budgets, regular witness languages or full-profile-safe arbitrary loop deletion.

The exact new finite interface gives a sharper next experiment: can different
return words in a shortest witness be grouped into a bounded number of these
phases while preserving existence? A counterexample must distinguish the
supplied-phase theorem from that presently unproved cover.

## 8. Executed evidence

Standard-library command:

    python3 experiments/check_source_power.py

The deterministic output records 173,910 direct power-conjugacy comparisons;
2,200 loop/tail contexts from every partial three-state terminal table;
204 additional generated contexts; 14,424 forward/reversed boundary-set
comparisons; 2,404 independently captured border sets; 56,896 first-return
commutation checks; 2,097 rotation comparisons; 81 full agreement profiles of
a two-cycle family; six exact canonical-model paths and six guards.

Another 2,404 queries use exponent 10^60 without expanding the word. They agree
with the proved stabilization threshold max(k,1+floor(|Y|/|B|)). Those are tests
of the symbolic calculation, not independent enumeration at astronomical length.
The explicit small-word comparisons provide the independent word-level checks.
The 81 full-profile cases do not assume lexical primitive bases: their base
words 00 and 11 traverse two-state first-return loops.

Optional command:

    python3 experiments/check_source_power.py --with-smt

The recorded run has 28 probes. Sixteen are grounded boundary formulas, one
isolates the necessary exceptional conjugacy, and six are full two-cycle
formulas. Three further grounded one-phase formulas test 0^m100 at m=0,1,2;
its exact witness condition is m<2. Two more probes leave m unbounded, with
m>=1 or m>=2. This is a genuinely mixed family, but the practical engine does
not necessarily resolve its free-parameter probes within the stated caps.

The saved run reports 5 SAT, 10 UNSAT and 13 UNKNOWN. All six full TWO-cycle
probes and both free-exponent probes are UNKNOWN. Thus the backend is NOT
reported to have solved those cases. Both positive grounded one-phase words
are reconstructed and checked against the independent predicates. Definitive
grounded answers agree with their finite word-level oracles. UNSAT retains
the backend trust boundary, not an independently checked proof.

Timed outcomes are not a byte-identical CI oracle. A preliminary larger random
formula batch exceeded its total process timeout and supplied no saved
conclusions; it was replaced by these explicit bounded probes. Several
additional simplification settings did not remove the two-cycle timeouts.
The ordinary all-length proof, not Z3's incomplete engine, establishes the
supplied-scheme decidability result.

All all-length statements rely on the proofs, not the finite counts. No new
Lean proof, independent mathematical referee, full repository CI or general
coverage theorem is claimed. Original core predicates are unchanged.
