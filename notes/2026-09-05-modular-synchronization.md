# Modular synchronization refutes Q002 and Q003

Date: 2026-09-05. Base commit: `2c6b4aac57634bf2b802c1bf4fae323862fd21e1`.
Approaches: A008, A009, A017. Claims: C046-C047. Experiment: E031.

**Status: written all-length proofs and reproduced finite checks; independent
review requested; not Lean-checked.** The general subtype entailment problem
is not settled here. Q002 and Q003 are refuted, not proved. Earlier finite
searches remain valid observations about their tested inputs. No literature
priority is claimed for these constructions.

## 1. A modular family of terminal instances (C046)

Choose r>=2 positive integers p_1,...,p_r. For each block i use a fresh entry
state s_i and fresh cycle states t_i,1,...,t_i,p_i. Add one terminal final f.
The initial state is s_1; f is the only accepting state; Bad is empty.

- From s_i, letter 1 leads to t_i,1; letter 0 is undefined.
- Letter 1 advances around the p_i-cycle.
- From t_i,p_i only, letter 0 exits to s_(i+1), or to f for i=r.
- Other 0 transitions, and both transitions from f, are undefined.

For each i<r put precisely these flags into G:

    (s_i, t_r,j) for every 1<=j<=p_r;
    (t_i,j, s_r) for every 1<=j<=p_i.

There are k=1+sum_i(p_i+1) states. All accepting states are terminal.
The candidate graph is flat: every productive cyclic component is a single
unary cycle. No variable-length encoding or nonterminal acceptance is used.

### Exact witness language

Write P=lcm(p_1,...,p_r). Then

    Witness(I) = { (1^N 0)^r : N is a positive multiple of P }.

**Proof.** Every accepted word has the unique form

    1^n_1 0 1^n_2 0 ... 1^n_r 0,

where every n_i is a positive multiple of p_i.

Suppose i<r and n_i<n_r. In the final block start the suffix exactly n_i
ones before its closing 0. This start is strictly inside the final cycle,
so its state is some t_r,j. That suffix is 1^n_i 0 and matches the beginning
of the earlier suffix at s_i. The pair is flagged.

Suppose instead n_i>n_r. In block i, start exactly n_r ones before its 0.
The start lies inside its cycle at some t_i,j. The suffix from s_r is
1^n_r 0, which matches there. This pair is also flagged.

Hence every witness has n_i=n_r for each i<r. This common positive count N
must be divisible by every p_i, equivalently by P.

Conversely, let all n_i=N. A suffix from a cycle state in the last block has
fewer than N remaining ones before its 0, so it cannot match the prefix from
an earlier s_i, which has N ones. Similarly, a suffix at an earlier cycle
state encounters its 0 before the N initial ones of the suffix from s_r end.
Thus none of the listed flags is violated. There are no diagonal or
final-column flags and no Bad states. The word is a witness. QED.

### Exact budgets and shortest witnesses

For every N>=1 and r>=2, the intrinsic sufficient budget of w=(1^N0)^r is

    b(w) = (r-1)(N+1).

To see this directly from C041, let a_m be the earliest start of the suffix
of length m. Its budget summand is

    m-1 + ((|w|-m)-a_m) = |w|-1-a_m.

Every suffix has an occurrence starting at its residue modulo N+1, hence
at a position at most N. The single-letter suffix 0 has earliest start
exactly N. Therefore max_m a_m=N and b(w)=|w|-1-N=(r-1)(N+1).
The additional L=|w| case cannot improve this minimum.

Combining the two proofs gives

    exact instance budget B(I) = (r-1)(P+1),
    unique shortest witness = (1^P0)^r,
    shortest witness length = r(P+1).

These are all-length formulas, not extrapolations from fixed-budget scans.

## 2. Eight states refute both conjectures

Take p_1=2 and p_2=3. Number the states as follows:

| State | 0 | 1 |
|---|---|---|
| 0 = s_1 | undefined | 1 |
| 1 = t_1,1 | undefined | 2 |
| 2 = t_1,2 | 3 | 1 |
| 3 = s_2 | undefined | 4 |
| 4 = t_2,1 | undefined | 5 |
| 5 = t_2,2 | undefined | 6 |
| 6 = t_2,3 | 7 | 4 |
| 7 = f | undefined | undefined |

    G = {(0,4),(0,5),(0,6),(1,3),(2,3)}.

The exact witness language is

    { 1^(6a) 0 1^(6a) 0 : a>=1 }.

The shortest witness is `11111101111110`, length 14, and the exact budget is
7. But k-2=6. Every one of the 28 budget splits with L+D<=6 is independently
exhausted by the existing finite Strong Sandwich construction; each is empty.
At budget seven, (L,D)=(0,7) and (7,0) accept the displayed word.

This refutes the terminal k-2 budget bound, and therefore Q002. More explicitly,
let A(w) be the full agreement profile of that shortest witness. Its profile
avoids G. Any accepted v with A(v) subseteq A(w) also avoids G, so v belongs to
the displayed witness language and has budget at least seven. Allowing v to
be longer does not rescue Q002.

It also refutes Q003: any profile-dominated accepted v is a witness for G,
and no such word is strictly shorter than 14. Thus a word with no strictly shorter
profile-dominated accepted replacement can have budget greater than k-2. Simultaneous
loop deletion cannot shorten this word safely either, regardless of how many
loops are deleted.

The earlier Q003 scan used k=5,6,7 and words through length 12. This example
has k=8 and length 14, outside that coverage. No state-minimality claim is made.
The one-state boundary issue in the original statement of Q003 is separate;
this eight-state refutation applies even after imposing k>=2.

## 3. Superpolynomial terminal budgets

The same family refutes not only k-2 but every polynomial upper bound in the
terminal state count.

Take r=m and periods 1,2,...,m, with m>=3. Then

    k = (m+1)(m+2)/2,
    P = lcm(1,...,m),
    B = (m-1)(P+1).

Here is a self-contained lower bound. Every binomial coefficient binom(m,j)
divides P. For any prime l, its valuation in binom(m,j) is

    sum_(a>=1) [floor(m/l^a)-floor(j/l^a)-floor((m-j)/l^a)].

Each summand is zero or one; only l^a<=m can contribute. The sum is at most
floor(log_l(m)), which is exactly the valuation of l in P. This proves the
divisibility. Since the m+1 binomial coefficients sum to 2^m, at least one is
at least 2^m/(m+1). Therefore

    P >= 2^m/(m+1),
    B >= (m-1)2^m/(m+1) >= 2^(m-1).

As k is quadratic in m, this gives B>=2^(Omega(sqrt(k))) on this family.
In particular no polynomial in k bounds all terminal witness budgets. The
shortest witness lengths have the same superpolynomial lower bound.

Some concrete formulas, all following from Section 1:

| Periods | States | P | Exact B | Shortest length |
|---|---:|---:|---:|---:|
| 2,3 | 8 | 6 | 7 | 14 |
| 3,4 | 10 | 12 | 13 | 26 |
| 2,3,5 | 14 | 30 | 62 | 93 |
| 2,3,5,7 | 22 | 210 | 633 | 844 |

**This is not an undecidability result.** The entire family is decided exactly
by computing a least common multiple. It is already inside the flat-graph
class covered by C033. The point is that any general bound must accommodate
arithmetic synchronization, not just the number of states or a polynomial
in it. This construction neither supplies nor excludes a general computable
bound for arbitrary terminal instances.

### Transfer to normalized subtype constraints

C030 realizes each instance on 2k+1 subtype variables with the same witness
words and budgets. The primary example has 17 variables and 21 normalized
constraints. E031 constructs it and checks the separating word by exact
regular-language countermodel operations, as well as rejected paths.

For periods 1,...,m the realization has m(m+3)+3 variables and
(5m^2+3m+4)/2 normalized constraints. Thus the lower bound is also
superpolynomial in either of these input counts. A binary-index encoding
uses O(m^2 log m) bits, so the lower bound is superpolynomial in that size too.
The arbitrary, possibly infinite tree semantics are unchanged. The subtype
transfer retains the recorded written/audited status of C030; no new Lean
formalization is claimed.

## 4. No universal constant number of loop deletions (C047)

A second specialization answers the immediate question raised in the C045 note.
Take p_i=1 for every i=1,...,r. There are k=2r+1 states. Call the entry states
s_i and the self-loop states t_i. Let

    w_r = (1110)^r.

This word has budget 4(r-1)>k-2 for every r>=2. Every accepted word is
1^n_1 0 ... 1^n_r 0 with n_i>=1. A profile-dominated accepted word must be a
witness for the family's flags, hence all n_i equal.

In this specialization the full profile of (1^N0)^r is independent of N>=1:
it consists of every visited-state diagonal, every visited state paired with
f (the empty suffix), and

    (s_i,s_j) and (t_i,t_j),  i<j.

Equal-type cross-block pairs occur by aligning equal remaining run lengths;
entry-to-loop and loop-to-entry pairs cannot occur because the next 0 occurs
after different numbers of ones. No other ordered state pair can occur.
Thus both (10)^r and (110)^r have exactly the same profile as w_r.

Every equal-state loop interval is entirely inside a single unary block:
state copies from different blocks are disjoint, entry states occur once,
and f is terminal. A strictly shorter profile-dominated result must decrease
ALL r counts together, since they started equal. Therefore at least r loop
intervals must be deleted. Deleting two ones in each block achieves (10)^r,
so the minimum is exactly r.

For r=3 this is the seven-state word

    111011101110 -> 101010,

requiring three simultaneous deletions. For arbitrary r it rules out every
constant deletion bound independent of k; it gives a necessary deletion
count (k-1)/2 in this family. It does not rule out a computable state-dependent
bound on deletion counts. This all-ones-period family supports Q003 for its
own words; the different-period family in Section 2 is what refutes Q003.

## 5. E031 reproduction and evidence boundaries

Run from the repository root:

    python3 experiments/check_modular_sync.py

The saved result is [modular-synchronization.json](../results/modular-synchronization.json).
The generator is [modular_sync_family.py](../experiments/modular_sync_family.py).

The completed regression records:

- all 32,767 binary words through length 14 for the eight-state example;
- exactly seven shorter accepted candidates, none profile-dominated;
- 596 complete finite Strong graph searches over nine parameter tuples,
  including every lower-budget split of the primary example;
- 288 parameterized exponent vectors and 18 uniform-word budget checks;
- 153 exact regular-countermodel checks and 152 full/reduced summary checks;
- all 3,276 count vectors in {1,2,3}^r for r=2,...,7;
- all 40 sets of zero, one, or two disjoint loop deletions for the seven-state
  three-block example, including adjacent intervals.

The large-number growth rows are evaluations of proved formulas, not
exhaustive searches at those budgets. Any capped graph search makes this
regression fail as inconclusive; it is not counted as a negative verdict.
The saved tests use only the standard library. Their dependency blob hashes
are included for the reference border predicates and the existing bridges.

## 6. Consequence for the research program

Q002 and Q003 must be marked REFUTED. The preceding local lemmas, exact budget
identity, terminal realization, and flat Presburger decision remain compatible
with this example. Reproducing a finite search with no counterexample never
established the conjectures; the new construction changes the conclusion,
not the historical search outcomes.

A successful general normalization argument must allow an arithmetic base
case: some shortest witnesses are already very long. The
computably bounded-skeleton direction remains meaningful because it can
represent these large numbers without enumerating their letters. What remains
unproved is a complete effective cover for arbitrary nonflat terminal graphs,
or another complete unrestricted decision procedure.
