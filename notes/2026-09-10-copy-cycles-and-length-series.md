# Unbounded copy cycles: nonsemilinear lengths and exact symbolic acceleration

Date: 2026-09-10. Base main: `2e431ff3d74d3ab1268866f86e24fd835ffe7fda`.
Workstreams: A008/A017, with an opposing-route observation for A011.
Proposed records C069-C070; experiment E044.

**Status: WRITTEN PROOFS + REPRO; independent mathematical review pending;
not Lean-checked. No general decision or undecidability result is claimed.**
Read the [route outline](2026-09-10-copy-cycle-route-outline.md).

The latest other-agent C067/C068 source-capture result already decides all
single-source terminal instances at its recorded proof level. This attempt
therefore does not restart joint-period counting to establish that subclass.
It tests whether counting ALL witnesses could be a viable general extension,
then gives a finite symbolic summary for an actual unbounded-copy recurrence.
The older normalization and capture results remain intact.

**Concurrent integration check.** Main advanced to `f79286f4155144ff32d8622baf6e932325b49565` during this investigation. Its source-visit census and live-source counterexample changes are retained, not overwritten or independently re-certified. The original blobs of STATE.md, A008.md and the indexer were re-fetched and matched the research base before appending this checkpoint.

## 1. Explicit eleven-state instance

Let I have state set {0,...,10}, binary alphabet {0,1}, initial state 0,
sole terminal final 5, no Bad states, and flags

    A=(0,4), B=(2,4), C=(1,3).

Its partial deterministic transition table is:

| State | 0 | 1 |
|---|---:|---:|
| 0 | undefined | 6 |
| 1 | 7 | 6 |
| 2 | 8 | 6 |
| 3 | undefined | 9 |
| 4 | 10 | 9 |
| 5 | undefined | undefined |
| 6 | undefined | 1 |
| 7 | 2 | undefined |
| 8 | undefined | 3 |
| 9 | undefined | 4 |
| 10 | 5 | undefined |

All eleven states are reachable and co-reachable. No minimization claim is made.
Regard `11` as one data token, `00` as a block delimiter, and `01` as the
one switch to the final stage. The unique candidate grammar is

    w = (11)^n1 00 ... (11)^nm 00 01 (11)^n 00,
    m>=1, n1,...,nm,n>=1.                                  (1)

Parsing is at even bit positions. Raw unaligned substrings do not create
extra comparisons at flags: every flag endpoint is a token-boundary state.
All helpers are unflagged. There are no diagonal or final-column flags.

### All comparisons, not just selected ones

For any candidate (1), a flagged target lies in the final stage. The relevant
suffix is `(11)^t 00`. Its first delimiter must align with the earlier
occurrence's first delimiter; an earlier tail with more or fewer data tokens
mismatches at that first delimiter. Consequently:

* A fires exactly when n1<n: start 0 matches a proper tail beginning in 4.
* B fires exactly when some ni<n for i>=2. State 2 at the switch cannot
  contribute: its prefix `01` differs from either `11` or `00` at a target.
* C fires exactly when some ni>n: an internal data boundary in state 1
  matches the entire final block beginning in state 3.

The equality case never fires. These statements also cover the zero-data tail
at state 4: a source starts with data or the switch, not `00`. No other
forbidden pairs exist. Thus with all three flags,

    Witness(I) = { B_n^m 01 B_n : n>=1, m>=1 },
    B_n = 1^(2n) 00.                                      (2)

The number of earlier equal blocks is UNBOUNDED and is not supplied as an
input parameter. This is the recurrent analogue of earlier fixed-stage copy
examples; the equality mechanism itself is not claimed as a new principle.

## 2. Multiplication appears in the exact length projection (C069)

Every word in (2) has length

    (m+1)(2n+2)+2 = 2ab+2,
    a=n+1>=2, b=m+1>=2.                                   (3)

Different pairs (n,m) give different words, even at equal total lengths:
there is one switch token, and the preceding delimiters and data determine
both parameters. Let tau(N) be the number of positive divisors of N. Then

    number of witnesses of length 2N+2 = tau(N)-2, N>=2,
    number of witnesses of every other length = 0.         (4)

For N=1 the coefficient is also zero, handled separately. In particular,

    a witness of length 2N+2 exists iff N is composite.     (5)

The shortest word is `1100011100`, length 10. For example the nonzero lengths
start 10,14,18,20,22,26; lengths 12,16,24 do not occur.

### The length set is not ultimately periodic

If the composite numbers were ultimately periodic with period P, their
complement among integers >=2 (the primes) would be too. Choose a prime q
beyond the alleged threshold. Periodicity would make q+qP=q(1+P) prime,
a contradiction. There are arbitrarily large primes by Euclid's argument.
An affine even coding as in (5) cannot restore ultimate periodicity: using an
even multiple of a hypothetical length period pulls back a period for N.
Thus this fixed terminal instance has a nonsemilinear unary length set.
In particular no Presburger formula in the sole length variable defines it.
This is NOT a statement that individual supplied skeletons lack Presburger
formulas. Their number or fixed bases are not bounded by that theorem.

### Its length-counting series is not rational

Put t=z^2 and D(t)=sum_{N>=1} tau(N)t^N=sum_{a,b>=1}t^(ab). Formula (4) gives

    W_3(z) = z^2 [D(z^2)-2z^2/(1-z^2)+z^2].               (6)

Here is a self-contained proof of nonrationality, without inferring it from
nonregularity of the language. For s>0,

    D(exp(-s)) = sum_{a>=1} 1/(exp(sa)-1).

For a<=floor(1/s), the summand lies between
1/((e-1)sa) and 1/(sa). The sum over this range is of order
log(1/s)/s. The remaining tail is at most a constant times
sum_{a>1/s}exp(-sa), hence O(1/s). Therefore

    D(exp(-s)) = Theta(log(1/s)/s), s -> 0+.

The rational correction in (6) has order O(1/s), so W_3(exp(-s)) has the
same logarithmic order. In particular s W_3(exp(-s)) tends to infinity,
while s^2 W_3(exp(-s)) tends to zero. A rational function near z=1 has a
pole of an integer order, or is bounded; neither possibility has these two
limits. Thus W_3 is not rational over the rationals.
This proves absence of a finite constant-coefficient linear recurrence for
its counts, not just failure to discover a recurrence in a finite sample.

### Even two flags already give a nonrational count

Remove A and retain B,C on exactly the same table. The exact witness condition
is n1<=n and ni=n for all i>=2. For length 2N+2, write a=n+1>=2 and
c=n1+1 in {2,...,a}. Then

    N=ma+c, m>=1.

There is one solution for each a in {2,...,N-2}, except a dividing N-1.
The excluded count is tau(N-1)-2; hence for N>=2 the coefficient is

    N-1-tau(N-1).

This yields

    W_2(z)=z^4 [z^2/(1-z^2)^2-D(z^2)],                   (7)

which is again nonrational. The length support is now all even lengths >=10;
nonrational counts and nonsemilinear support are distinct conclusions.

### A single recurring source can also have nonrational RAW counts

Retain only B=(2,4). The first block is unrestricted; every subsequent earlier
block has at least n data tokens. With t=z^2, summing the independent first
block and arbitrary number of remaining blocks gives

    W_1(z) = t^3 sum_{a>=2} t^a/(1-t-t^a).                 (8)

This series is nonrational. For each a>=2 the denominator 1-t-t^a has a unique
positive root r_a in (0,1). The r_a are distinct and increase to 1. Its term
has a genuine simple pole there. On compact subsets of |t|<1 excluding the
poles, the tail of the sum converges locally uniformly: for large a its
summands are bounded by a constant times |t|^a. At r_a every other term is
analytic locally, so the pole cannot cancel. The meromorphic continuation
has infinitely many poles in the unit disk, impossible for a rational
function. Substituting t=z^2 leaves infinitely many poles as well.

**This does not contradict C065.** That theorem first normalizes to a
return-free source and counts that existential normal form. It does not
assert rationality for every witness of the original recurrent automaton.
Here first-to-last deletion of source 2 removes the intervening earlier
blocks; the resulting one-visit family has rational series t^5/(1-t)^2.
Nor is C067 affected: its argument uses existential word equations, not a
rational series for the full original language.

### Consequences and semantic transfer

A strategy assuming rational counts or semilinear length support for EVERY
terminal witness language is false. This does not refute a computable
existential source/run bound, rational counting AFTER a justified
normalization, or a complete symbolic cover that preserves only existence.
The fixed example itself is positive with a ten-letter witness.
C030 gives an always-satisfiable 23-variable normalized bottom/product
realization with the same separating words. That transfer retains C030's
written/audited status; the current work does not re-formalize it in Lean.
The multiplicative length projection is not an undecidability reduction.

## 3. Thirteen-state arbitrary-word copy cycle

The positive construction below treats arbitrary data, not only unary counts.
Let E(0)=10, E(1)=11. Use states {0,...,12}, start 0, sole terminal final 7,
Bad empty, and this table:

    ((-1,8),(9,8),(9,8),(10,8),(-1,11),(12,11),(12,11),
     (-1,-1),(1,2),(3,-1),(-1,4),(5,6),(7,-1)).

The source boundaries 0,1,2,3 have predecessor tags START,0,1,START;
target boundaries 4,5,6 have tags START,0,1. Flag exactly the eight pairs
whose tags differ, from a source boundary to a target boundary. Helpers
8,...,12 are unannotated. The candidate language is

    E(u1)00 ... E(um)00 01 E(v)00,
    m>=1; every ui and v is a nonempty binary word.        (9)

If ui differs from v, their longest common suffix has different predecessor
tags at its two starts. The corresponding final suffix E(x)00 matches earlier,
and its pair is flagged. Conversely, for ui=v, matching from token boundaries
requires equal tails up to the first 00 delimiter, hence the same predecessor
tag. Source 3 at the switch starts with 01, which cannot match any final-stage
boundary suffix. These are all possible flag endpoints. Thus exactly

    W_copy = {B^m 01 B : B=E(u)00, u nonempty, m>=1}       (10)

are witnesses. The graph is genuinely recurrent and nonflat, and the number
of flagged-source visits is unbounded over its witness language. This is an
exact description of this graph, not a decomposition of arbitrary inputs.

## 4. One unchanged shared block admits exact acceleration (C070)

### A regular primitive-block guard

Every B=E(u)00 for nonempty u is unbordered, hence primitive. Indeed it begins
with 1, ends with 0, and E(u) contains no 00. A proper prefix ending in 00 can
only be B with its last bit removed, when E(u) ends in 0. Such a border would
have length |B|-1, forcing period one and hence a unary word, impossible.
Length-one borders are excluded by the endpoint letters. These cases rule
out all proper nonempty borders.

For a nonempty primitive B, the word equation

    U B = B U, U nonempty                                (11)

is equivalent to U=B^m for some m>=1. To see this, the usual cancellation
induction on |U|+|B| shows that commuting nonempty words are powers of one
common word: cancel the shorter prefix from the longer and repeat. Primitivity
of B then forces that common root to be B's primitive root B itself.
Without the guard the implication is false: U=11, B=1111 commute but U is not
a whole-number power of B. The regression retains this counterexample.

Consequently (10) has an EXACT finite shared-word template

    B in (10|11)^+ 00, U in {0,1}^+,
    U B = B U,
    W = U 01 B.                                         (12)

The same B is used at every occurrence. There is no variable concatenation
iteration left, no supplied copy count, and no universal quantifier hidden in
(12). A regular restriction on data u becomes a regular constraint on B, by
coding its automaton. Regular constraints on W may also be added. The proof
does not appeal to a generic closure of arbitrarily iterated template relations:
it accelerates only repetitions of ONE UNCHANGED primitive word. The earlier
PCP objection to two independent append accumulators remains valid.

### A complete implemented solver without an external string engine

Inputs are two partial binary DFAs: a data language L (ell states) and a
whole-output domain D (d states). L may accept epsilon, but the family uses
only L intersect {0,1}^+. D need not have terminal finals. Both may have safe
state exclusions, implemented by removing Bad transitions; they have no flags.
The exact decision question is

    exists nonempty u in L and m>=1:
         (E(u)00)^m 01 E(u)00 belongs to D.              (13)

Complete D with an absorbing rejecting sink. A word induces an action on its
d+1 states fixing that sink; at most M=(d+1)^d actions are possible.
The finite search state is

    (current L state, action of E(u) on all D states,
     whether u is nonempty).

The initial state uses L's start, the identity action, and false. On data bit
a, advance L and right-compose the action by the fixed two-bit word 1a.
Undefined/unsafe L transitions are omitted. All nonempty accepting L states
qualify. There are at most 2*ell*M states, with actual parent paths retained.
A Bad initial state gives NO directly.

For each qualifying action H, compose the action of 00 to obtain A, the action
of B=E(u)00. Let s be D's start and T the action of 01. Enumerate the positive
orbit A(s), A^2(s),... until a state repeats. Accept when

    A(T(A^m(s))) is an accepting D state.                (14)

If a positive orbit position succeeds, one succeeds with m<=d: the rejecting
sink never succeeds, and repeated states give no new test. Multiple primitive
blocks inducing the same A may share this test. Retaining one representative
u is sound because (14) depends only on A; the reconstructed word still has
one common B at ALL occurrences.

For completeness, any solution of (13) yields a reachable H. Replace u by its
stored representative with the same H and L acceptance, and replace m by a
successful earlier positive orbit position. The equality-defined witness family
and D membership both survive. Hence finite exhaustion proves NO for (13).
This is an existence-preserving substitution, not the previously refuted
claim that transition actions preserve arbitrary agreement profiles/contexts.

A representative has data length at most 2*ell*M. A conservative output bound is

    (d+1)*(4*ell*(d+1)^d+2)+2.                            (15)

All explicit state/work/output caps in the implementation return UNKNOWN.
With caps disabled the construction terminates. A reconstructed output is
checked against both original witness predicates, D membership, and L membership.
The search does not promise the globally shortest output.

This is a complete filter/acceleration component for the SUPPLIED family.
It neither recognizes an arbitrary automaton as a copy-cycle image nor proves
that every positive terminal instance has a witness in such a family. Some
older special-case solvers may also decide these examples; no claim that the
new family defeats every existing restricted solver is made.

## 5. A source/target asymmetry worth retaining

The one-visit source normalization of C067 has no unconditional target dual.
Take five states, start 0, terminal final 4, no Bad states,

    delta=((2,-1),(4,3),(1,3),(0,2),(-1,-1)),
    G={(0,2),(1,2),(3,2)}.

All flags have the SAME target 2. Word 01100 is a witness and visits 2 twice.
Every accepted path visits 2, since it is the only first-step destination.
After its first visit, the only accepting path not returning to 2 is the
00 path via 1 to 4. Thus the sole accepted word with at most one target visit
is 000, which is bad: its initial state 0 matches target 2 at its first cut.
So some positive one-target instance requires at least two target visits.
This refutes that single-visit shortcut, not a computable bound or a one-target
decision theorem. No minimal-state or unbounded-lower-bound claim is made.

## 6. Executed evidence and its scope (E044)

Run `python3 experiments/check_copy_cycle.py`.
The deterministic run uses seed 2026091071 and records:

* 131,071 raw binary words for the 13-state all-data grammar and both predicates;
* 1,048,568 raw word/annotation checks for all eight subsets of the unary flags;
* 1,350 general-data tuples and 10,880 unary tuple/annotation checks;
* EVERY one of the 10,926 accepted unary candidates through bit length 42,
  with exact witness counts under the three, two and one-flag variants;
* 86 direct equality/two-flag coefficients, 22 one-flag series coefficients,
  and 500 independently enumerated divisor coefficients;
* 510 unbordered-code blocks and 12,282 explicit commutation-word tests;
* 313 complete regular-filter oracles: all 64 total two-state binary filters
  (36 YES/28 NO), 136 modular length filters (100/36), 90 finite dictionary
  filters including independent data restrictions (46/44), and 23 exact-length
  filters (14/9). The two-state oracle enumerates data words through length
  four because the four transformations on a two-element set give a complete
  positive-action bound, not because a guessed word cutoff is assumed;
* 8 exact canonical regular-countermodel path checks using the unchanged
  C030 implementation and semantic checker (23/27 variables for the two graphs);
* 72 accepted words for the single-target regression, plus its all-length proof;
* three deliberate resource caps and a malformed-domain guard.

The raw and tuple checks use both existing independent word predicates. The
series and semantic claims covering all lengths rest on the proofs, not this
finite sample. The optional source-capture SMT engine is not used here.
The original border regression is replayed separately. No full repository CI,
Lean build, independent mathematical reviewer, or literature-priority claim is
implied by these checks.

## 7. What this changes, and what would actually finish the route

The general all-witness rational-series hypothesis is false. It fails even for
one flag before its valid existential normalization, and three flags already
yield a nonsemilinear length projection. Adding higher incidence terms does
not by itself justify a rational representation of arbitrary recurrent-source
languages. C065's correct normalized argument and C067's existential argument
are not contradicted.

The constructive gain is an exact acceleration for repeated use of one shared
primitive block, with arbitrary regular filters and a finite termination proof.
A fixed finite template with finitely many such commuting pairs remains an
existential constrained-word-equation instance. That observation alone does
NOT supply a finite template COVER for a general automaton.

The next required theorem is a complete existence-preserving decomposition
into finitely many stable-copy phases, or a different terminating representation
when the shared block itself changes along a cycle. An example with multiplication
in length is not that theorem and does not establish undecidability. The opposing
route would need to share independently chosen factors between successive
multiplication zones and combine them consistently, with every terminal
comparison proved correct. No such reduction is supplied here.
