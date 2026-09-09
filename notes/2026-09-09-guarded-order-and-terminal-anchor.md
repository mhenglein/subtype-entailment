# Guarded-order completeness, modular witnesses, and the terminal-anchor gap

Date: 2026-09-09. Base main: `05b20ee73841d0e7105a44beb761e553a7081a8d`.
Workstreams A012/A016/A017; opposing-route input for A011.

**Status: written complete proof for an explicitly restricted infinite class,
plus a written undecidability reduction for a NEARBY TRAILING-CONTEXT pattern
problem and executable differential checks. Independent mathematical review
pending; not Lean-checked. Neither result settles unrestricted Problem 1.7.**
No new global C/E numbers or literature priority claim are allocated.

[End-to-end route and remaining implications](../research/ORDER_COVER_ROUTE.md).
The purpose is to replace the earlier three-stage finite census by a uniform
complete argument, then identify exactly why neither that argument nor the
opposing computation encoding currently transfers to arbitrary terminal inputs.

## 1. Exact class and finite compiler

An input is a finite stage count r>=1, domains

    D_i = {n>=L_i : n == a_i (mod m_i)},
    L_i>=1, m_i>=1, 0<=a_i<m_i,                        (1)

and an arbitrary ordered flag relation on the roles E_i, U_i (0<=i<r) and F.
Its candidate words are exactly

    w(n) = 0^n_0 1 ... 0^n_(r-1) 1, n_i in D_i.       (2)

E_i is the state before the first zero of stage i. U_i is the role of every
positive-count state in that stage, including the state immediately before its
ending 1. F is the sole terminal accepting state. A role flag (A,B) is lifted
to EVERY ordered pair of actual states with those roles. No Bad states are
needed in this class. All roles occur on every candidate, and every count is
strictly positive.

This is an effective ordinary binary terminal DFA, not a new tree constructor
or infinite-state model. At stage i, use one E_i state, states representing
positive counts 1,...,L_i+m_i-1, and a zero cycle from the last of these back to
count L_i. A 1-edge exits to E_(i+1), or F at the last stage, precisely at cycle
states whose count is a_i modulo m_i. No earlier count can exit. Positive-count
states all have role U_i. Start at E_0; all unspecified edges are undefined.
The compiler has

    k = 1 + sum_i (L_i+m_i)

states. It enforces (1)-(2) exactly and has no outgoing edge from F. Its flags
are the full role rectangles just specified. The implementation returns both
the concrete DFA and its role map. A compilation/expansion cap is an error,
never an existential NO result.

The decision procedure takes the supplied symbolic class description. It does
NOT pretend to recognize every arbitrary DFA as a member of this class, and
it does not ignore phase-sensitive flags in a supplied DFA.

## 2. Exact translation to equality-guarded order clauses

For i<j define

    Gamma_ij = AND_{h=1,...,r-1-j} (n_(i+h)=n_(j+h)).   (3)

The empty conjunction is true. The exact violation conditions are:

| Source/target roles | Violation exists exactly when |
|---|---|
| E_i,E_j | Gamma_ij AND n_i=n_j |
| E_i,U_j | Gamma_ij AND n_i<n_j |
| U_i,E_j | Gamma_ij AND n_i>n_j |
| U_i,U_j | Gamma_ij |

**Proof.** In two matching suffix fragments, the first 1 must occur at the
same offset. Thus the initial zero tails have the same length t. Each later
whole target zero block must equal the corresponding source block, giving
(3). The source has enough later blocks because i<j. The first entry/entry
case fixes t=n_i=n_j. Entry/interior fixes t=n_i<n_j. Interior/entry fixes
t=n_j<n_i. For interior/interior, t=0 is always available immediately before
both 1-edges because all counts are positive. Conversely these cuts concatenate
the equal tails and following whole blocks, producing the required agreement.
The argument permits overlapping occurrences. QED.

Different cuts within one zero block cannot agree: their first 1 offsets
differ. Backward-stage role flags cannot occur in an ordered comparison.
A diagonal role flag gives an actual diagonal failure. A flag to F gives an
empty-suffix failure from its source role. Since every role occurs on every
candidate, either such flag eliminates the entire candidate language.
Source-F flags with a distinct nonfinal target are irrelevant.

After handling those cases, witnesshood is exactly the conjunction of:

    Gamma_ij -> n_i != n_j          for E_i,E_j;
    Gamma_ij -> n_j <= n_i          for E_i,U_j;
    Gamma_ij -> n_i <= n_j          for U_i,E_j;
    Gamma_ij -> false               for U_i,U_j.       (4)

These are equality-guarded order-Horn constraints. The technique is related to
the classical Ord-Horn temporal constraint language, rather than a claimed new
invention of Horn order reasoning. A primary technique source is Bodirsky and
Kara, *A Fast Algorithm and Datalog Inexpressibility for Temporal Reasoning*,
arXiv:0805.1473. The proof below is self-contained and explicitly accounts for
the arithmetic progression domains, so no unproved transfer from that paper
is needed.

## 3. Complete saturation: every supplied stage count, not just three

Maintain a directed graph on {0,...,r-1}. Edge i->j means the entailed inequality
n_i<=n_j. Reachability means the same weak inequality by transitivity. Mutual
reachability forces equality. Initially only reflexive reachability is present.

Repeat the following rules until no edge can be added:

1. If every equality in a guard Gamma is forced by mutual reachability, its
   weak-inequality conclusion can be added as an edge.
2. If an activated false conclusion is present, report NO. If an activated
   disequality has equal endpoints, report NO.
3. If mutually reachable indices i,j have incompatible domains,

       a_i != a_j (mod gcd(m_i,m_j)),                 (5)

   report NO.

The implementation scans clauses deterministically and recomputes transitive
closure after an actual addition. Each added edge relates previously unrelated
ordered vertices; there are at most r(r-1) additions. Thus saturation always
terminates. There is no guessed candidate word length or parameter-value cap.

Every NO has a finite proof object: the list of activated inequality clauses,
followed by the violated clause or inconsistent congruence pair. An independent
verifier replays graph reachability, checks each equality guard BEFORE adding
its conclusion, then verifies the final contradiction. A proof referring to
an unproved equality is rejected.

### Soundness

Every added inequality is a logical consequence of (4) and previous inequalities.
Mutual reachability forces equality in every solution. The false/disequality
contradictions are immediate. Condition (5) is necessary for equal integer
values satisfying both congruences. Hence a reported NO is sound.

### Completeness and the important generic-model argument

Suppose saturation stops without contradiction. Collapse its strongly connected
components, and take a topological ordering of the quotient DAG. Within one
component the congruences are pairwise compatible. The generalized Chinese
remainder theorem gives a common arithmetic progression; its values are
unbounded above, so all lower bounds can also be met.

Assign ONE common value to each component, choosing the values STRICTLY
increasing in that topological ordering. Each choice is possible because its
common progression is unbounded. Thus all entailed weak inequalities hold and
two stages get the same value exactly when they belong to the same component.

Consider any guard in (4). If every equality was forced, its conclusion was
activated and is satisfied, since no contradiction occurred. Otherwise some
guard pair lies in distinct components. Those values were chosen distinct,
so the guard is false. In particular, we do NOT accidentally create a new
true guard by choosing equal values for unrelated components.

Every clause and every domain is satisfied. By Section 2, the resulting
candidate is an original witness. This proves completeness. QED.

**Theorem.** Witness existence in the stated modular phase-blind serial class
is decidable in time polynomial in the symbolic input bit length, with a finite
NO proof or a compact count-vector YES certificate.

A conservative bound for the simple graph implementation is O(r^5) ordinary
Boolean graph operations, plus polynomial-time integer arithmetic. Clause
count is O(r^2), each equality guard has O(r) size, at most O(r^2) edges are
added, and each closure uses O(r^3) Boolean operations. This is not an optimized
complexity claim for the Python implementation or a claim about unrestricted
terminal BorderAvoid.

## 4. Explicit bounds and large witnesses without expansion

Put

    P = lcm(m_0,...,m_(r-1)), L = max_i L_i.

For each component, its common modulus divides P. Choose its least admissible
value strictly larger than the previous component's value, beginning at L.
Each step increases by at most P. Consequently

    max_i n_i <= L+rP,
    |w| <= r(L+rP+1).                                (6)

The bit length of P is at most the sum of the input modulus bit lengths.
Hence the vector can be constructed and checked in polynomially many bits,
even when the expanded word is enormous. For m_i=L_i=1, the construction
assigns consecutive ranks 1,...,c to c<=r components, giving the sharper bound

    |w| <= r(r+1).                                   (7)

This explains why enumerating weak order types was complete in the previous
three-stage experiment, and replaces exponential enumeration by a terminating
proof-producing algorithm for every r.

### The modular synchronization lower bounds remain intact

Put flags E_i->U_(r-1) and U_i->E_(r-1) for each i<r-1. Their empty guards force
all n_i equal. With L_i=1 and a_i=0, the exact witness language is

    { (0^n1)^r : n is a positive multiple of P }.

Its shortest length is exactly r(P+1). For periods 2 and 3, the compiler has
8 states and shortest witness length 14, reproducing the structure of the
known modular obstruction rather than contradicting its lower bound.

The recorded twelve-stage prime-period case has common count
15343363347736655767223341 and exact shortest length
184120360172839869206680104. The program returns a count-vector certificate;
it does NOT expand that many symbols or claim a brute-force word check. Exact
minimality here follows from the displayed language formula. Adding E_0->E_1
creates a finite contradiction once the equalities have propagated.

## 5. Genuine scope boundary: phase-sensitive flags cannot be collapsed

Take two stages with positive EVEN counts. In each stage the zero cycle has
an odd and an even phase. Put only one concrete flag from the odd phase of
stage 0 to the even phase of stage 1.

The word 001001 is a witness: any equal zero tails in the two stages have the
same phase, so that particular odd/even pair cannot match. Treating this one
flag as if it were the entire U_0 x U_1 rectangle would produce the false
clause true -> false and incorrectly report NO.

The checker retains this concrete counterexample. It rules out that particular
phase-forgetting generalization, not the existence of richer exact summaries.
Likewise, the generic-model proof needs unbounded common component domains.
It must not be applied unchanged to arbitrary finite value domains, arbitrary
word-valued blocks, or a candidate graph which can revisit earlier stages.

## 6. Opposing route: two copies suffice if trailing context is allowed

Here is a precise undecidability boundary, not an undecidability claim for
BorderAvoid. Consider the following problem:

    Given a regular prefix-free candidate language R and a finite union of
    pattern languages A_i X_i B_i X_i C_i, with regular A_i,B_i,C_i and
    X_i constrained to 0+, decide whether R is included in that union.    (8)

Each pattern has exactly two occurrences of its one repeated variable. Other
factors are independently chosen regular words. The second copy is NOT
required to end the candidate: C_i can contain an arbitrary future history.

**Theorem.** Problem (8) is undecidable. The arbitrary trailing factor is
essential to this stated reduction; no elimination of it is proved here.

### Named source and regular candidate language

Start with a finite two-counter machine. Each transition records source and
target control states, zero/nonzero tests, and changes delta_1,delta_2 in
{-1,0,1}, with no decrement at zero. Existence of an accepting finite run is
undecidable. A precise primary source for this source model and its use in
pattern reductions is Nowotka and Wiedenhoeft, *The Equivalence Problem of
E-Pattern Languages with Regular Constraints is Undecidable*,
arXiv:2411.07275v1, Section 2.1.

Encode a configuration (q,c_1,c_2) by a control token and two delimited fields
0^(c_1+1),0^(c_2+1). Write transition labels between consecutive configurations,
and unique initial/final delimiters around the entire history. The regular
candidate language R checks the initial configuration (initial counters zero),
final accepting control, adjacent source/target control, and all zero tests.
It does NOT check the unbounded numeric update relations. Every condition just
listed has a finite-state check: only finitely many controls and the predicates
field length one / field length at least two need be retained.

A unique final delimiter absent elsewhere makes R prefix-free. Thus an
ordinary terminal-final DFA recognizes it. Arbitrarily many transitions are
permitted by R; their count is not a supplied finite-stage bound.

### Exactly two unary copies detect each incorrect update

For one selected counter of one transition, let N=c+1 and M=c'+1 be its two
positive field lengths. Correctness requires M=N+delta.

If M>N+delta, then M>=N+(delta+1), where delta+1 is 0,1 or 2. Capture the entire
source field as X=0^N and match a copy at the beginning of the target field,
followed by at least delta+1 further zeros. The pattern is A X B X C, with
that fixed extra-zero requirement in regular C.

If M<N+delta, then N>=M+(1-delta), where 1-delta is 0,1 or 2. Capture X=0^M as
a prefix of the source field, require at least 1-delta further source zeros,
then match X as the ENTIRE target field. Put the source excess in regular B.
Again there are exactly two copies of one unary variable.

The regular contexts select the same counter in ADJACENT configurations of the
specified transition. They start or end the capture at actual field boundaries
as described; the unused counter fields, other history prefix and arbitrary
future history are regular context. The executable regex builder implements
these two cases, with one capture and one recall per pattern.

Over R, their finite union matches exactly histories with at least one wrong
numeric update. Therefore R minus that union is exactly the set of valid
accepting computations. A decision of (8) would decide whether such a computation
exists, proving the theorem. Both directions use the update equivalences above,
not merely an analogy with general backreference universality.

The presentation uses a finite delimiter/control alphabet. A fixed-length
injective binary code transports every regular context and the candidate
language to binary words. The repeated unary variable then ranges over powers
of one fixed binary word. Injectivity and the transported regular domains
preserve both implications. This does not append a new constructor to subtypes.

### Why this does not settle our problem

An original forbidden comparison requires the ENTIRE suffix at its target to
match. The numerical error detector just built can stop after its second unary
field and ignore an arbitrarily different future computation. That permission
is not present in the original predicate. The implemented interior-error
example uses precisely this additional power.

Thus a reduction to Problem 1.7 still requires a finite terminal-anchored gadget
that replaces the arbitrary C_i without introducing spurious witnesses or
losing invalid histories. The finite-copy decomposition of bad words does not
supply that gadget. Conversely, a constructive normalization must exploit this
terminal anchoring rather than appeal to a theorem for arbitrary copy patterns.

The new reduction is a scoped, self-contained version of the familiar
invalid-computation approach; no claim that its general idea is new is made.
Freydenberger's *Extended Regular Expressions: Succinctness and Decidability*
is additional context for why unrestricted single-variable backreferences are
dangerous, not an imported undecidability theorem for BorderAvoid.

## 7. What has and has not been discharged

The uniform guarded-order backend is complete for (1)-(2), including arbitrarily
many SUPPLIED stages, conflicting noncoprime congruences, and delayed equality
guards. It generates checked positive or negative certificates rather than
relying on finite word search or repeating the old three-stage observation.

OPEN constructive implication: an effective, existence-preserving finite cover
of arbitrary recurrent terminal inputs by this or another decidable class.
Serial role-uniform counts are not such a cover. The phase counterexample is
one explicit reason not to assume they are.

OPEN opposing implication: elimination of arbitrary trailing context in the
counter-update reduction under the original terminal comparison semantics.
The two unresolved implications are different. Neither a failed generalization
nor undecidability of (8) decides the original problem. No new witness bound for
all terminal inputs is asserted.

## 8. Executed evidence and reproducibility

```sh
python3 experiments/check_guarded_order_chains.py
python3 experiments/check_trailing_copy_barrier.py
python3 experiments/run_experiments.py
```

The first checker, seed 2026090953, covers all 4,113 effective annotation sets
through three stages (including the old 709 YES / 3,387 NO three-stage result),
all 512 one-stage role-flag subsets including boundaries, 700 modular cases
against a complete weak-order oracle, 23,968 literal modular count vectors,
and 204,700 raw binary words comparing the compiled candidate language to its
independent arithmetic parser. Every returned positive modular word in these
cases is directly checked against both witness predicates. Larger 8/16/32/64-
stage examples and the huge compact-count example have replayed certificates;
they are not exhaustive censuses of those stage counts. Ten guards include
forged proof steps and attempts to expand or compile beyond explicit caps.

The second checker compares 9,800 selected-counter queries across 4,900
regular candidate histories and all nine update vectors. It finds 4,891 bad
histories and nine valid ones, and includes an incorrect INTERNAL update with
a valid later transition. Finite checks support the regex builder, not the
undecidability theorem; that theorem rests on the reduction in Section 6.

The original core checker is unchanged. No new Lean work, independent human
referee, or complete local checkout/CI is claimed. Remote CI results must be
reported separately for the pushed commit, not inferred from these local runs.

## Sources

- Bodirsky and Kara, arXiv:0805.1473: https://arxiv.org/abs/0805.1473
- Nowotka and Wiedenhoeft, arXiv:2411.07275v1, Section 2.1:
  https://arxiv.org/html/2411.07275v1
- Freydenberger, extended-regex scope:
  https://www.ddfy.de/publications/F-ERESaD.html
- Prior exact stage oracle and finite census:
  [collective/cross-gap note](2026-09-08-collective-and-cross-gap-transport.md).
- [Modular lower bounds](2026-09-05-modular-synchronization.md),
  [terminal semantic transfer](2026-09-05-terminal-realization.md).
