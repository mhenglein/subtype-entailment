# Universal terminal run normalization and bounded-run decisions

Date: 2026-09-06. Base: PR #9, `df54d87ec4432f489d0b845c7834612f6af70c12`.
Approaches A008/A017. Proposed C054-C055; experiment E035.

**Status: written proof plus reproduced finite checks; independent review
requested; not Lean-checked.** This is not a decision procedure for unrestricted
Problem 1.7. Unlike the preceding marker certificate, the main normalization
statement applies to every binary partial DFA word ending at a terminal
accepting state, with arbitrary flags and Bad states and no marker encoding.
It controls run lengths but does not supply a computable bound on run count.
No literature-priority claim is made.

## 1. Statement and exact scope (C054)

Let M be a k-state partial DFA over {0,1}. A terminal state has no outgoing
transition. Let w be a defined word ending at a terminal accepting state f.
Write its canonical run-length encoding as

    w = a_0^n_0 a_1^n_1 ... a_(r-1)^n_(r-1),
    n_i >= 1, a_i != a_(i+1).

Thus r counts maximal homogeneous runs, not positions or visits to automaton
states. The empty word has r=0. Write c_w(t) for the run state after t letters,
and define the full agreement profile, including diagonals and empty suffixes,

    A_M(w) = { (c_w(i),c_w(j)) : 0<=i<=j<=|w|,
                                    w[j:] is a prefix of w[i:] }.

**Theorem.** One can construct a defined accepted word v with the same ordered
list of run letters, the same state at every run boundary, the same set of
visited states, and

    |v| <= |w|,
    A_M(v) = A_M(w).

Put H=(k+1)^2. For each letter a, let P_a be the least common multiple of the
cycle lengths eventually reached by the a-transition orbits starting at the
runs of w labelled a. Totalize an undefined transition with an absorbing dead
state, whose cycle length is one. An unused letter has P_a=1. Put P=max(P_0,P_1).
The construction satisfies

    every new run length <= r(H+P),
    |v| <= r^2(H+P).

Every selected cycle has length at most k (or is the dead self-loop), and at
most r of them are selected. In particular

    P <= min(lcm(1,...,k), k^r).

Thus the completely input/run-count based bound is

    F(k,r) = r^2((k+1)^2 + min(lcm(1,...,k), k^r)).

The empty-word case is interpreted as F(k,0)=0. No optimality of this bound is
claimed. The slightly looser period from all states of M works as well.

For EVERY flag relation G and Bad set, w is a witness iff v is a witness,
because both the complete agreement profile and visited-state set are equal.
The construction is not limited to words already known to be witnesses.

## 2. Finite unary information

For a letter a, let T_a be its totalized transition function on k+1 states.
From any state, its orbit is a finite transient followed by a cycle. The
transient has length at most k. A cycle in the original states has length at
most k; the added dead state is fixed.

Consequently, for a chosen start p whose eventual cycle length divides P_a,

    x,y >= k and x == y mod P_a  ==> T_a^x(p)=T_a^y(p).

The set of states visited by an orbit prefix has stabilized after at most
k+1 positions. A synchronized pair of a-orbits is an orbit of T_a x T_a on
(k+1)^2 states. Its SET of visited pairs has stabilized after at most H
positions. This statement bounds distinct visited pairs, not the period of
the word or the length of a witness.

For starts p,q and positive run lengths x,y, define the positive equal-tail
pair set

    U_a(p,q;x,y) = { (T_a^(x-t)(p), T_a^(y-t)(q)) :
                                            1<=t<=min(x,y) }.

If x<=y, this is the prefix of length x of the synchronized orbit starting
at (p,T_a^(y-x)(q)). For y<x swap which component has the initial shift.
It follows that U is preserved when all the following hold:

1. the order of x and y is preserved;
2. their difference, if at most H, is unchanged; otherwise it remains above H
   and is unchanged modulo P_a;
3. min(x,y), if at most H, is unchanged; otherwise it remains above H.

For a large difference, the shifted initial state is the same by unary
periodicity. For a small difference it is literally the same. For a small
minimum, both synchronized prefixes have exactly the same length. For a large
minimum, both prefixes already contain their entire eventual pair-orbit set.
Only the periods of p and q are used; no unvisited orbit is needed.

## 3. Compress GAPS between distinct counts, not each count independently

For each letter separately, sort its distinct positive run lengths and prepend
zero as an anchor:

    0=x_0 < x_1 < ... < x_d.

For each adjacent gap g=x_h-x_(h-1), replace it by

    g' = g                                  if g<=H,
    g' = H+1 + ((g-H-1) mod P_a)             if g>H.

Set x'_h to the cumulative sum of the new gaps. Replace every run of length
x_h by the same value x'_h. The same map is used for every run of that letter.

Each new gap is positive, no larger than the old gap, at most H+P_a, and
congruent to the old gap modulo P_a. Hence the mapping is strictly increasing,
preserves all equalities, and only shortens runs. For ANY two listed values,
including the zero anchor:

* if their difference is at most H, every intervening gap is unchanged;
* if the difference exceeds H, either all intervening gaps are unchanged or
  at least one new gap itself exceeds H; in either case the new difference
  still exceeds H;
* the difference remains congruent modulo P_a, by summing adjacent gaps.

In particular values at most H stay unchanged and larger values stay larger
than H. These are exactly the conditions from Section 2. As d<=r, the largest
new count is at most r(H+P_a).

Run boundary states are unchanged by induction. For a small run the count is
unchanged. For a large run the two counts exceed H and agree modulo its
selected period, so their endpoints agree. The visited-state set inside each
run agrees too: either the run is unchanged or both copies cover the entire
unary orbit from the same start. Thus undefined transitions, safety, and finality
are preserved, not merely the final state.

### Why separate per-run truncation fails

Take the five-state transition table

    0: 0->2, 1->1       1: 0->2, 1->1
    2: 0 undefined, 1->3
    3: 0->4, 1->3       4: terminal.

For N=10^80, the word 1^N 0 1^(N+1) 0 has no agreement pair (0,2): the two
positive runs have unequal lengths. Independently replacing both large counts
by the same small residue representative creates that pair. This can turn a
witness into a non-witness for the maximal preserving flag relation.

The gap construction instead gives counts 37 and 38, since H=36 and P_1=1:

    1^(10^80) 0 1^(10^80+1) 0  -->  1^37 0 1^38 0.

The normalized word has length 77 and the EXACT original profile. The large
word is handled symbolically; it was not expanded or checked letter by letter.

## 4. Exhausting all possible suffix agreements

The run-length formula below applies to the original raw binary word. It does
not impose a token format, insert a marker, or discard flags inside runs.

Let p_i be the state at the start of run i, let l=r-1 be the last run index,
and write m=n_l. Terminality implies

    m <= k-1.

Indeed a repeated state while reading the last homogeneous run would create
a unary cycle from which the run could not subsequently reach a terminal
state. Its m+1 states must all differ. In particular the last run is unchanged
by the compression, since m<H.

### 4.1 Diagonal and empty-suffix agreements

These pairs are exactly (q,q) and (q,f), respectively, for visited states q.
The visited-state set and endpoint f are preserved, so these pairs agree.

### 4.2 The target begins before the last run

Choose distinct source and target cuts, in runs i and j with j<l. A match must
start with the same letter. The first change of letter in the target suffix
must occur at the same offset in the source; otherwise the words already
differ there. Consequently i<j, a_i=a_j, and the positive numbers of letters
remaining in the two starting runs must be equal.

After those equal tails, put d=l-j. All intervening complete target runs must
match the corresponding source runs. The exact guard is

    n_(i+h)=n_(j+h) for h=1,...,d-1,
    n_(i+d) >= n_l.

The last relation is an INEQUALITY, not equality: the target may end inside a
longer source run. Binary alternation and a_i=a_j ensure all corresponding
letters agree. For i<j we have i+d<l, so that final source run exists.
Conversely, this guard plus equal starting tails supplies the complete match.

When the guard holds, the set of starting state pairs contributed is precisely

    U_(a_i)(p_i,p_j;n_i,n_j).

The guard is preserved: equalities compare counts of the same letter and its
strictly increasing map preserves equality. The final threshold n_l is at
most k-1 and is unchanged; every count below H is unchanged and every larger
count remains larger than H. Section 2 proves equality of the U pair sets.
Two distinct cuts in the SAME nonlast run cannot match, because their first
letter change would be at different offsets. There is no omitted same-run case.

A fixture `01101` demonstrates why the last inequality matters: its final
suffix `01` matches an earlier occurrence followed by an extra `1`. Replacing
>= by equality would lose a genuine agreement.

### 4.3 The target begins in the last run

Such a positive suffix is a pure-letter word a_l^t with 1<=t<=m<=k-1.
Its target state is T_(a_l)^(m-t)(p_l), unchanged by normalization.
A source can begin in any run i of that letter with n_i>=t. Its possible
states are exactly

    { T_(a_l)^x(p_i) : 0<=x<=n_i-t }.

This includes source and target in the last run, with the proper ordering
x<=m-t. If n_i<=H its count is unchanged. Otherwise both n_i and n'_i exceed H,
and both prefix bounds exceed H-(k-1), which is greater than k. Both source
state sets have therefore already saturated along the unary orbit.
The comparison n_i>=t is preserved as well. Thus these profile pairs agree.

Sections 4.1-4.3 cover every pair of positions. They prove A_M(v)=A_M(w).
Summing r new counts bounded by r(H+P) proves the claimed length bound. QED.

## 5. Polynomial checking of compressed candidates

The preceding formula computes the full profile directly from binary-encoded
run lengths. Unary orbit tables require polynomial work in k. A large power
uses a transient/cycle calculation and modular arithmetic on the encoded
count, not a loop through all its letters. Each U pair set requires at most
(k+1)^2 orbit positions. The final-run loop has fewer than k iterations.
The remaining loops range over the r run indices and context-guard comparisons.

Therefore checking a supplied canonical RLE terminal witness is polynomial
in k, r, and the total binary bit length of its counts, including arbitrary G
and Bad. `profile_runs` is the exact symbolic checker; it is not a guessed
finite approximation of large counts. The separate direct and reversed
letter-level profiles supply bounded independent tests of its implementation.

## 6. The bounded-run problem is NP-complete (C055)

Define the decision problem:

    Input: an explicit binary terminal BorderAvoid instance I and R in unary.
    Question: does I have a witness with at most R maximal homogeneous runs?

**Membership.** C054 gives a witness, whenever one exists, whose run counts
are at most

    R((k+1)^2 + min(lcm(1,...,k), k^R)).

There are at most R counts. Their binary bit lengths are polynomial in k and
the unary input size R, since lcm(1,...,k)<=k!<=k^k for k>=2. Guess a first
letter, at most R positive counts, and alternating letters, then use the exact
polynomial RLE checker. Handle epsilon separately. This proves NP membership.
It does not claim that exhaustive enumeration is polynomial time.

**Hardness.** Unary DFA intersection nonemptiness is NP-complete. A primary
reference recording that classical fact is Fernau, Hoffmann, and Wehar,
*Finite Automata Intersection Non-Emptiness: Parameterized Complexity Revisited*
(2021), page 2, lines 40-43:
https://arxiv.org/abs/2108.05244 . The positive-length version is equally hard:
prefix one symbol to each input language. Add a universal DFA if needed to
ensure at least two inputs. The source theorem is not claimed as new.

For r unary DFAs M_i, introduce a fresh block entry s_i and one copy of every
input state. From s_i, a first 1 enters the copy of the state reached from the
input start by 1. Copies follow the unary transition on 1. An accepting copy
may read 0 to the next fresh entry, or to the terminal final after the last
block. Entries have no 0 transition. Thus the candidates are exactly

    1^n_1 0 ... 1^n_r 0, n_i>=1 and 1^n_i in L(M_i).

As in C046, flag each earlier entry against every copied state in the final
block, and every earlier copied state against the final entry. These flags
reject respectively n_i<n_r and n_i>n_r. Equal counts introduce no flagged
agreement. Thus the exact witness language is

    { (1^N0)^r : N>=1, 1^N in every L(M_i) }.

Every witness has exactly 2r maximal runs. The construction has
1+sum_i(|Q_i|+1) states and polynomially many flags. Set R=2r, in unary.
This is a polynomial reduction and establishes NP-hardness. QED.

The implementation `compile_unary_sync` makes this reduction explicit and
checks every pair of partial two-state unary DFAs on the finite fixtures.
The conceptual source problem differs from general binary DFA intersection,
which supplied the PSPACE lower bound in C049.

### Fixed R and exact practical verdicts

For any FIXED R, the bound using k^R is polynomial in k. Enumerating the at
most two alternating letter patterns per run count and every bounded exponent
vector yields a polynomial-time algorithm with degree depending on R (an XP
algorithm when parameterized by R). No fixed-parameter tractability claim is
made. R given in binary is not covered by the NP-completeness statement.

`solve_run_bound` implements an exact, capped finite enumeration. It returns
YES with a symbolic witness, NO_WITHIN_RUN_BOUND after exhausting that bounded
question, or UNKNOWN at a count-table/run-prefix cap. A bounded negative is
NOT unrestricted NO. The implementation intentionally does not guess a global
run-count bound. Nonterminal-final inputs are rejected as unsupported.

## 7. What this does and does not finish

C054 applies to every terminal input without the marker or annotation-position
restrictions of C052-C053. It deals with arbitrary cuts by separating matched
run tails, intervening full runs, and a potentially partial final run. This
eliminates a need to bound homogeneous exponent magnitudes independently.

A computable bound R(k) on the number of runs in SOME witness of every positive
k-state terminal instance would now give the explicit length bound F(k,R(k))
and a complete finite decision. No such run-count bound is proved here.
The equivalence does not turn a minimum defined over finitely many instances
into a computable function. Merely increasing the run cutoff still supplies
only a positive semiprocedure.

Moreover, R(k) cannot be polynomial if the prior C050 construction is correct.
That construction has the UNIQUE witness

    W_d=(E(C_d)00)^(d+1), E(0)=10, E(1)=11,

where C_d lists every d-bit word, least-significant bit first. C_d contains
exactly d*2^(d-1) zeros. Each encoded zero contributes an isolated zero run,
and each final delimiter contributes one more. The encoded data ends in 1,
and every block starts in 1. Hence the EXACT number of maximal runs is

    runs(W_d)=(d+1)(d*2^d+2).

C050's compiled state count is at most 18d^2+11d+3. Thus the run-count parameter
itself can be superpolynomial in the original instance size. The new NP result
has R as part of its unary input; it does not imply unrestricted NP membership
or contradict C049's PSPACE hardness.

The earlier Q002/Q003 refutations remain intact. C054 preserves run count and
can stop far above k-2 budget; it does not promise strict shortening for every
high-budget word. A general solution still needs an effective bound on
alternation structure, a complete symbolic treatment of unbounded runs, or
another complete decision method.

## 8. E035: executed checks and limitations

Run `python3 experiments/check_run_normalization.py`.

The committed final run uses seed 2026090654 and records:

* all 256 partial three-state tables with start 0 and sole terminal final 2,
  and every accepted word through length 7: 780 full-profile comparisons;
* 1,974 further accepted short words from 450 random terminal tables;
* all 288 complete unary transformations through four states, supporting
  135,535 gap identities and 26,136 exact equal-tail pair-set comparisons;
* 344 expanded longer words, plus 216 large binary-count words with selected
  exponents using powers of ten between 10^25 and 10^89; 331 strict compressions
  across these two portions;
* 120 acyclic candidate automata with complete finite-language oracles,
  queried at run bounds 0,1,2,3: 215 YES and 265 NO_WITHIN_RUN_BOUND;
* all 1,296 pairs of partial two-state unary input DFAs and 20,736 block-count
  vectors cross-checking the explicit hardness compiler;
* two exact canonical regular-model checks, the independent-count-truncation
  failure, the final-run >= fixture, six C050 run-count checks, and a deliberate
  cap preserving UNKNOWN.

The large encoded words were not expanded. Their checks exercise the symbolic
formulas and normalization assertions; they are not independent letter-level
comparisons at those enormous lengths. The expanded finite cases compare
against direct/reversed formulations. The quantified claims rest on the proof,
not these observations. The unary-intersection finite oracle uses the complete
four-state product bound, not a guessed cutoff.

An unfinished earlier runtime did not retain its scratch files. This checkpoint
reconstructed the source from the recorded attempt, tightened the active-period
bound, and reran the final suite before saving results. A generator-consumption
hazard in count_map was removed by materializing its input iterable; the final
suite includes that regression. No discrepancy in the mathematical assertions
was observed in the completed runs. Independent review and Lean verification
remain outstanding. The full original repository suite is not claimed.

The original core regression was rerun from this checkpoint and reproduced
Git blob aa6d1680b5442493744c667024d2df77a1bd8e78 exactly. The new registry
evidence paths and generated A017 row were checked, and all other generated
tracker rows are unchanged. This is a partial snapshot: no repository-wide
link validation, full suite, or Lean build is claimed.
