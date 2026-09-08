# Terminal copy synchronization: large budgets and a top-free hardness reduction

Date: 2026-09-05. Base: `2c6b4aac57634bf2b802c1bf4fae323862fd21e1`.
Approaches: A008, A009, A011, A017. Claims: C046-C049. Experiment: E029.

**Status: WRITTEN PROOFS + IMPLEMENTATION + REPRO; pending independent review.
Not Lean-checked. No unrestricted decision procedure or upper complexity bound
is claimed.** The reductions concern arbitrary, possibly infinite trees.
Literature priority of these specific constructions has not been established.

## 1. C046: an eight-state refutation of Q002 and Q003

Start at 0, accept only terminal state 7, and take Bad empty:

| State | 0 | 1 |
|---|---|---|
| 0 | undefined | 1 |
| 1 | undefined | 2 |
| 2 | 3 | 1 |
| 3 | undefined | 4 |
| 4 | undefined | 5 |
| 5 | undefined | 6 |
| 6 | 7 | 4 |
| 7 | undefined | undefined |

Set

    G = {(0,4), (0,5), (0,6), (1,3), (2,3)}.

The boundary-safe accepted words are precisely

    1^a 0 1^b 0,       a in 2*N_positive, b in 3*N_positive.

If a<b, the last block has an interior suffix `1^a 0`, matching the first
block from state 0. Its target state is 4, 5, or 6, so one of the first three
flags is violated. If a>b, the first block has an interior occurrence of
`1^b 0`, starting at state 1 or 2 and matching the suffix from state 3.
One of the last two flags is violated.

Conversely these are the only flagged source/target combinations. Matching a
suffix ending at the last 0 to an earlier factor forces alignment with the
first 0. No such flagged comparison exists when a=b. Consequently the exact
witness language is

    { (1^(6t) 0)^2 : t >= 1 }.

The unique shortest witness is `11111101111110`, of length 14. Its sufficient
budget is 7, and every other witness has budget at least 7, by Section 2.
Thus this terminal eight-state instance has

    B(I) = 7 > 8-2.

The construction has only five flags. E029 independently exhausts all 28
Strong Sandwich splits with L+D<=6; every graph is empty. It tests all eight
splits with L+D=7 and obtains checked positive witnesses. The largest graph
among these 36 searches has 29 states. There is no resource-cap exit.

Let w be the shortest witness. If A(v) were contained in A(w), every flag
preserving w would also preserve v. Hence v would be a witness of I. Since
all witnesses have budget at least 7, Q002's budget-six replacement does not
exist. Since no witness is shorter than w, Q003's strictly shorter replacement
does not exist either. E029 also tests the maximal preserving flag relation
(the complement of A(w), containing 42 pairs), exhausts its 28 lower splits,
and directly rejects profile domination for all seven shorter accepted words.

This refutes Q002 and Q003, not the equivalence C044 between the budget/profile
formulations. It does not invalidate the local hypotheses of C045, the
four-state census C034, or the computable-skeleton hypothesis Q001. No claim
that eight states is the smallest possible counterexample is made.

### A genuine 17-variable subtype instance

Applying C030's unchanged terminal realization gives 17 variables and 21
normalized constraints, querying `a0 <= v0`. In the following table b is the
seventeenth variable and is constrained by `b <= bottom`:

| Upper constraints | Lower constraints |
|---|---|
| a0 <= b x a1 | b x v1 <= v0 |
| a1 <= b x a2 | b x v2 <= v1 |
| a2 <= a3 x a1 | v3 x v1 <= v2 |
| a3 <= b x a4 | b x v4 <= v3 |
| a4 <= b x a5 | b x v5 <= v4 |
| a5 <= b x a6 | b x v6 <= v5 |
| a6 <= a7 x a4 | v7 x v4 <= v6 |
| a7 <= b x b | (no lower constraint) |

Add `a0<=v4`, `a0<=v5`, `a0<=v6`, `a1<=v3`, and `a2<=v3`.
The system is satisfiable and its separating paths are exactly the witness
language above, under C030. The existing independent `topfree_bridge.py`
constructs and validates a regular countermodel for the displayed path;
its path-set NFA has 109 states. E029 checks 30 paths for this system, including
rejected paths. A rejected path is not an entailment certificate.

## 2. C046 continued: an exact LCM family with super-polynomial budgets

Take r>=2 positive integers p_1,...,p_r. For each block use one fresh entry
state e_i and a disjoint p_i-cycle on the letter 1. Entry requires one 1;
the cycle can exit on 0 exactly after a positive multiple of p_i letters.
The exit leads to the next entry, or to a single terminal final after block r.
There are

    k = 1 + r + sum_i p_i

states. The candidate language is

    1^a_1 0 ... 1^a_r 0,       a_i in p_i*N_positive.

For every i<r flag (e_i,q) for every interior state q of the last block, and
flag (p,e_r) for every interior state p of block i. Exactly the two comparison
arguments in Section 1 force a_i=a_r, for every i<r. Thus, with
M=lcm(p_1,...,p_r),

    Witness(I) = { (1^a 0)^r : a>0 and M divides a }.

All strongly connected components are simple cycles or singleton transient
states. These are already FLAT terminal instances, not a nonflat artifact.

### Exact budget and shortest length

Write s=a+1 and n=rs. For every nonempty suffix of w=(1^a0)^r, its occurrence
at position j can be shifted back to position j mod s. Therefore its earliest
occurrence starts at a position at most s-1=a. C041's exact budget summand is
`n - earliest_start - 1`, so every summand is at least

    n-a-1 = (r-1)(a+1).

The length-one suffix 0 first occurs exactly at position a, attaining equality.
The L=n convention is no smaller. Consequently

    word_budget((1^a0)^r) = (r-1)(a+1),
    B(I) = (r-1)(M+1),
    shortest_witness_length(I) = r(M+1).

Examples:

| Periods | States k | Exact B | Shortest length |
|---|---:|---:|---:|
| 2,3 | 8 | 7 | 14 |
| 3,4 | 10 | 13 | 26 |
| 2,3,5 | 14 | 62 | 93 |
| 2,3,5,7 | 22 | 633 | 844 |
| 2,3,5,7,11 | 34 | 9244 | 11555 |

The larger rows are evaluations of this proved formula, not reports that all
their lower-budget automata were searched. E029 separately records which
families received exhaustive lower-split certificates.

### An elementary super-polynomial lower bound

Use periods 1,2,...,t, so r=t and k=(t+1)(t+2)/2. Put M_t=lcm(1,...,t).
Every binomial coefficient binom(t,j) divides M_t: for each prime p, the
factorial valuation formula writes its p-valuation as a sum of terms

    floor(t/p^a)-floor(j/p^a)-floor((t-j)/p^a),

each 0 or 1, with no nonzero term for p^a>t. This is at most the p-valuation
of M_t. Since the t+1 binomial coefficients sum to 2^t,

    M_t >= 2^t/(t+1),
    B(I_t) >= (t-1)2^t/(t+1).

For t>=3 this is at least 2^(t-1). As k=Theta(t^2), the required budgets grow
as at least `2^(Omega(sqrt(k)))` along this family. In particular **no polynomial
state-count bound on successful terminal budgets is possible**. The explicit
transition/flag encodings also have polynomial size in k.

This says nothing against a larger computable bound. In fact the family has
an immediate arithmetic decision and a bounded skeleton with r unary loops.
Large exponents must not be confused with many essential blocks.

## 3. C047: forcing copies of arbitrary regular words

Given r>=2 ordinary binary DFAs M_1,...,M_r, construct a terminal automaton
T over {0,1,#}. It reads sequential blocks

    u_1 # ... u_r #,         u_i in L(M_i).

Each block has a fresh entry state labelled by a marker BEGIN, and states
(q,a) recording its DFA state q and its immediately preceding data letter
a in {0,1}. Transitions update both q and a. Reading # is permitted only from
an accepting DFA state (including an accepting entry/start), and leads to the
next block entry or to one terminal final. Empty blocks are allowed exactly
when the corresponding DFA accepts the empty word.

Between every earlier block i<r and the last block r, flag exactly the pairs
of states with DIFFERENT marker labels (BEGIN, 0, or 1).

**Theorem.**

    Witness(T) = { (u#)^r : u in intersection_i L(M_i) }.

**Proof.** A target suffix within the last block has the form x#, with x a
suffix of u_r. An earlier matching factor must be the same suffix x followed
by the delimiter of its own block; # cannot occur inside a data word.

If u_i=u_r, aligned suffixes have the same predecessor letter, or both start
at their respective BEGIN states. They never create a flagged pair.

If u_i!=u_r, let x be their longest common suffix. Immediately before x,
either the two data letters differ, or one word has ended on the left and
contributes BEGIN while the other contributes a data letter. The two positions
reading x# therefore have different marker labels, giving a flagged agreement.
This includes x empty and includes empty data words. Thus witnesshood is
exactly equality of all blocks, in addition to their regular membership.

If N is the sum of the input DFA state counts, T has 1+r+2N states and at most
quadratically many flags. Construction time and output encoding size are
polynomial in the explicit input tables.

## 4. C048: exact binary coding without a new semantic constructor

The ternary alphabet above is only an intermediate device. Encode

    h(0)=00, h(1)=01, h(#)=10.

Replace each ternary transition by its two-bit code, sharing its first-bit
intermediate state when possible. Only original states retain flags, Bad
annotations, and final annotations; intermediate states are unflagged and
nonfinal. The code 11 is undefined.

Every accepted binary path starts and ends on original states and decodes
uniquely. Both endpoints of every potentially flagged agreement are original
states, hence aligned on code boundaries. For aligned suffixes, the equal-length
injective code preserves and reflects the prefix relation. Therefore

    Witness(binary_encode(T)) = h(Witness(T)).

Terminality is preserved, and at most two intermediate states are added per
original state. No self-synchronizing property at arbitrary bit positions is
needed, because such positions cannot supply flagged endpoint pairs. The
encoding preserves witness languages, **not numerical word budgets**.

## 5. C049: a direct top-free PSPACE-hardness route

Nonemptiness of the intersection of a supplied list of binary DFA languages
is PSPACE-complete. A primary source explicitly covering a binary alphabet is
Arrighi et al., *On the Complexity of Intersection Non-emptiness for Star-Free
Language Classes*, FSTTCS 2021, Theorem 21, printed page 34:12:
[official paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol213-fsttcs2021/LIPIcs.FSTTCS.2021.34/LIPIcs.FSTTCS.2021.34.pdf).
The theorem statement was checked in the rendered PDF; its stronger restrictions
on the input languages are not needed here.

C047 and C048 give a polynomial many-one reduction from that problem to binary
terminal-final BorderAvoid witness existence. C030 then gives a polynomial
reduction to non-entailment in an always-satisfiable normalized subtype system
using only bottom and binary product, with arbitrary possibly infinite trees:

    intersection_i L(M_i) nonempty
      iff terminal encoded instance has a witness
      iff C does not entail alpha <= beta.

Hence **top-free non-entailment is PSPACE-hard under the recorded C030/forward
reduction assumptions and proof status**. Entailment is PSPACE-hard as well:
PSPACE is closed under complement, so the complementary source intersection-
emptiness problem is PSPACE-hard and reduces to entailment through the same map.

This does not use ambient top, does not require the missing unrestricted
BorderAvoid converse, and does not assert any polynomial-space upper bound.
The source theorem supplies the complexity fact; the new written construction
supplies the fragment-specific reduction. Neither passing tests nor that source
paper alone proves this new reduction. Independent mathematical review is needed.

For the CONSTRUCTED subclass, when its component DFAs are supplied, ordinary
finite product reachability is an exact solver. The implementation returns YES
with a common word, NO only on graph exhaustion, and UNKNOWN at a cap. It is
not a recognizer/solver for arbitrary terminal BorderAvoid inputs.

## 6. E029: evidence and reproducibility

Run from the repository root:

    python3 experiments/check_terminal_copy.py
    python3 experiments/run_experiments.py

The new standard-library experiment writes `results/terminal-copy.json`.
With seed 2026090546 it checks:

- all 32,767 binary words through length 14 for the eight-state example;
  all 28 original and all 28 maximal-profile lower-budget splits are exhausted;
- 100 LCM parameter families and 16,466 candidate words, including 268 exact
  positive per-word budgets; seven families receive complete lower-budget
  exhaustion (254 splits in total, with no cap);
- 126 tuples of DFAs, 35,548 block candidates, and 12,264 arbitrary binary
  words, comparing the language formula with both forward and reversed
  predicates before/after coding;
- 126 product decisions against an independent backward fixed point on the
  complete Cartesian graph: 33 YES and 93 NO;
- 65 exact canonical subtype-path checks (30 for the LCM example, 35 for the
  regular-copy constructions), plus three cap and ten invalid-input regressions.

The original border regression passes unchanged: 10,160 word checks and
121,920 automaton comparisons. Its output retains Git blob
`aa6d1680b5442493744c667024d2df77a1bd8e78`. The checked copies of the three
existing modules have exactly their base-branch Git blob hashes; they were
not altered to obtain these results. No Lean build or full repository suite
is claimed by this experiment.

## 7. Revised frontier

Q002 and Q003 must not remain live proof targets in their sharp k-2 form.
The old random samples missed arithmetic synchronization, which this generator
can enforce deliberately. Keep their historical data as finite observations.

The positive route is still to find a COMPUTABLE bound or a finite complete
symbolic representation. Q001's skeleton hypothesis survives: the LCM family
uses few blocks with large exponents, and the existing flat Presburger solver
is designed to retain such unbounded exponents. General copy synchronization
also admits a finite product representation once the common block is identified.

The missing general step is not another small-budget census. It is to prove
that arbitrary terminal obligations admit finitely many such controlled
synchronization contexts, or supply a different complete certificate calculus.
Any proposed normalization should now be tested on both the LCM family and the
regular-copy generator, while keeping arbitrary nonflat join obligations explicit.
