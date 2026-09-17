# An unrestricted first-return hierarchy, and the failure of finite reference summaries

Date: 2026-09-15. Research base: `47adf83c194aa941b525240f6470f3d77a69f81d`.
Workstream A017, with A008/A012 implications.

**Outcome: an exact all-input representation, an exact fixed-reference subroutine,
and counterexamples to the proposed terminating quotient. NOT an unrestricted
solution.** These are ordinary written arguments plus executable independent
checks, not independent mathematical review or Lean verification. No new C/E/Q
identifiers have been allocated. The existing subtype bridge retains its own
recorded status; no finite-tree substitution is made.

This investigation deliberately attempts an end-to-end unrestricted procedure,
not another input class defined by a return-closure hypothesis. The global
reference hierarchy below covers every terminal word, but has infinite branching.
Two natural finite quotients fail, including a quotient retaining full transition
actions and complete internal agreement profiles. The failed proof step is not
promoted to a theorem because the other steps work.

## Subsequent repair within this investigation

The failed representative rules below were not the end of the attempt. An
[exact finite-interface construction](2026-09-15-one-promotion-elimination.md)
now eliminates ONE unknown first-return reference without a length cutoff.
It computes reachability in the next matching graph as that pattern is built,
and repairs both false negatives. Its scope is at most one additional rank
milestone; iteration across all k-1 possible levels is still unproved. It is
not an unrestricted decision or a justification of the refuted quotients.

## 1. Exact model

Let I=(Q,delta,s,F,Bad,G) be a partial deterministic binary automaton, with k
states and no outgoing transitions from F. Undefined transitions reject. The
run c(0),...,c(N) of w is safe when it avoids Bad, including its endpoints.
For a safe accepted word, the exact witness condition is

    for all 0<=i<=j<=N:
       w[j:] is a prefix of w[i:] implies (c(i),c(j)) not in G.

Put rho=reverse(w) and r_i=c(N-i). For each prefix rho[:m], let pi(m) be its
longest proper border length, with pi(0)=0. The border chain at m consists of
m, pi(m), pi(pi(m)), ..., 0. Then witnesshood is exactly

    (r_m,r_t) not in G for every m and every t in its border chain.

This includes full and empty borders. It is the repository's existing reversal
identity, not a new semantic reduction. The checker compares it with both
independent existing predicates rather than using only a new implementation.

Define depth(0)=0 and depth(m)=1+depth(pi(m)) for m>0.

### Terminal depth bound

All original state labels along a border chain are distinct. Suppose b<a are
border lengths of one scanned prefix and r_b=r_a. Reversing their prefix-equal
strings makes the shorter suffix a prefix of the longer accepted suffix from
that same state. The shorter one reaches a terminal state before the longer
one finishes, impossible. The same argument includes b=0, since r_0 is already
terminal. Thus every scanned prefix has depth at most k-1.

This is not the false statement that a synchronized pair path has no repeated
vertices. It only constrains states on one nested BORDER chain. Cyclic pair
paths and arbitrarily long comparisons remain possible.

## 2. Global first-return milestones

For h>=1, when such a prefix exists, let m_h be the FIRST position of depth h.
Set P_h=rho[:m_h]. Let H be the largest depth in rho.

**Lemma 1.** m_1=1. For every 2<=h<=H,

    pi(m_h)=m_(h-1),

and m_h is exactly the end of the first occurrence of P_(h-1) starting at a
positive position. After m_H, the full P_H never occurs again.

**Proof.** No depth can first appear by skipping a smaller depth: its parent
chain would contain the skipped value at an earlier position. The parent b
of m_h therefore has depth h-1 and b>=m_(h-1). If b>m_(h-1), the copy of the
length-b prefix ending at m_h contains a copy of P_(h-1) ending at
m_h-b+m_(h-1)<m_h. At that earlier endpoint P_(h-1) is a proper border, giving
border-chain depth at least h, a contradiction. Hence b=m_(h-1). An earlier
return of P_(h-1) would give the same contradiction. A further return of P_H
would give a prefix of depth at least H+1. QED.

Consequently EVERY nonempty terminal accepted word has a canonical description
with at most k-1 reference-growth levels:

    choose one letter P_1;
    grow P_h until its first positive-position return, obtaining P_(h+1);
    after the last level, continue without returning to the full reference.

Returns may overlap. These are actual prefixes of one common rho; no separator,
independent copy, or new bit is inserted. This is a finite-depth description,
not a finite family of bounded-length words.

## 3. Exact fixed-reference layer

Fix a nonempty concrete reference B and its full reverse run r_0,...,r_m,
where m=|B| and r_0 is terminal. Assume every already scanned border test is
safe. Until the first NEW complete occurrence of B, every proper border of
the current scanned prefix has length at most m. A longer proper border
would contain an earlier new full occurrence of B. At the first return,
the longest proper border is exactly m.

Construct a finite automaton over labelled reverse steps (a,p), meaning that
a new bit a is prepended in the original direction and the new original
state is p. Its live state is (q,j): current original reverse state q, and
longest suffix of scanned text that matches a proper prefix of B, length j<m.
Initially q=r_m and j=pi_B(m). The initial occurrence of B is not a return.

A transition on (a,p) requires delta(p,a)=q and p not in Bad. Update j by the
ordinary failure-prefix recurrence of B. Call the result t, 0<=t<=m. The
new proper borders are t and its pi_B chain. Reject when (p,p) is flagged or
when (p,r_b) is flagged for any b in that chain, including b=0. If t=m,
enter a terminal first-return endpoint labelled p. Otherwise retain (p,t).
No transition is permitted after a first-return endpoint.

There are at most k*m live states and k terminal return endpoints, plus a
rejecting state if totalization is desired. A completion endpoint is any state
whose current original state is s, including a return endpoint if present.
Its reversed full string is an original witness. Equivalently, use a finish
mode that excludes return endpoints and let the next layer handle them.
The implementation permits immediate acceptance at a return, which is identical
for the existence question.

**Lemma 2.** This automaton recognizes exactly the safe labelled extensions up
to and including their first new occurrence of B. It records every possible
next reference and decides exactly whether any completion is possible before
such a return.

**Proof.** The reverse edge condition is precisely the original run. Before
and at the first return, the preceding paragraph bounds the proper borders by
m; the failure recurrence enumerates them exactly. Their reference endpoint
labels are r_b. The full-border diagonal is tested separately. Thus each step
is valid exactly when it introduces no forbidden comparison. Finite graph
reachability handles arbitrarily long extensions and is not a word cutoff.
QED.

The independent checker uses a literal suffix window with original states,
not failure links, and exhausts the symmetric-difference product of the two
finite machines. This proves equivalence of the FIXED-reference regular
languages in those test instances, not completeness of a reference quotient.

## 4. The candidate unrestricted procedure and its missing step

One could try to recurse through Lemma 2, promoting a first-return endpoint's
entire scanned string as the next B. Lemma 1 bounds recursion depth by k-1.
There can nevertheless be infinitely many first-return strings at an endpoint.
A complete procedure needs a proved finite existence-preserving representation
of those choices and their effect on later reference growth.

I implemented and falsified two precise candidate choices:

1. Keep a shortest return string per endpoint original state.
2. Keep a shortest return string per endpoint, totalized forward transition
   action, visited-state set, and COMPLETE internal agreement profile.

For the second candidate the layer graph tracks these finite accumulators,
so it really does enumerate every attainable summary at that layer; this is
not just a bounded sample of candidate summaries. Its successor branches
retain one representative per summary. Both procedures terminate under the
proved depth bound when uncapped, but they are NOT complete. Their negative
result is EXHAUSTED_HEURISTIC, never NO.

### Four-state failure of endpoint-only selection

    delta=((2,-1),(3,1),(1,-1),(-1,-1)), s=0, F={3}, G={(0,2)}.

The candidate language is 00 1* 0. Word 000 is bad; every 00 1^m 0 with m>=1
is a witness. Starting backwards from final 3, the first reference is 0 with
labels (3,1). The shortest first return at endpoint 2 is 00 with labels
(3,1,2); it has no safe completion. The longer first return 010 at the SAME
endpoint does extend by 0, yielding rho=0100 and witness 0010. The endpoint
procedure exhausts its selected branches and misses this actual witness.

### Six-state failure of full action/profile selection

Use start 0, sole terminal final 5, Bad empty:

| q | 0 | 1 |
|---|---|---|
| 0 | 4 | undefined |
| 1 | 2 | undefined |
| 2 | 1 | 5 |
| 3 | 1 | undefined |
| 4 | 4 | 3 |
| 5 | undefined | undefined |

Initially take G={(0,1),(0,3),(4,3)}. The exact accepted language is

    0^a 1 0^(2b) 1, a>=1,b>=1.

The two flags into state 3 reject exactly a>=2b: equality fires (0,3), and a
larger initial block fires (4,3) at an interior initial zero. Flag (0,1) rejects
exactly the remaining odd values of a: state 1 occurs before an odd number of
remaining trailing zeros. Therefore

    Witness = {0^a 1 0^(2b) 1 : b>=1, a positive even, a<2b}.

The shortest witness is 00100001, with a=2,b=2.

Every first return of the initial reversed letter 1 is

    B_b=1 0^(2b) 1,

ending at original state 4. All these references are locally safe. Their
forward transition action maps 4 to 5 and every other state to the undefined
sink. Their visited-state set is {1,2,3,4,5}. Their entire agreement profile is

    {(q,q):q in {1,2,3,4,5}}
      union {(q,5):q in {1,2,3,4,5}}
      union {(4,2)}.

Indeed all proper prefixes before the final 1 are unbordered, and B_b itself
has exactly the proper nonempty border 1. Repeating states 1 and 2 along the
zero run adds no new profile pair.

Nevertheless the exact legal completions of B_b in the reversed direction are

    {0^a : a positive even and a<2b}.

For b=1 this is empty; for b=2 it contains 00. Keeping the shortest reference
B_1=1001 discards B_2=100001 despite their identical ENTIRE proposed signature.
The enriched finite procedure therefore misses the eight-letter witness.

This is not a defect in fixed-reference graph reachability. That subroutine
correctly declares B_1 uncompletable and B_2 completable. It is precisely the
substitution of one parameter word for another that is unsound.

### An infinite antichain of ACTUAL first-return continuations

On the same table replace G by {(0,1),(0,2),(4,3)}. Now the two flags from 0
reject all a<2b, and (4,3) rejects a>2b. The exact witnesses have a=2b. Thus
for these same B_b, their continuation languages are the pairwise disjoint
nonempty singletons

    R_b={0^(2b)}, b>=1.

The common signature above still agrees. This is a live parameter dependence
inside the global rank decomposition, not merely an unrelated residual-language
example. It refutes a concrete-residual inclusion well-quasi-order or a finite
exact contextual quotient here. It does NOT refute a symbolic shared-parameter
representation, an existence-preserving noncontextual selection, or a larger
computable witness bound. This fixed example itself is easy: one integer
parameter and equality express it exactly.

The existing repository already contains finite-action/profile residual
counterexamples. The narrower new point is that imposing the canonical
first-return/rank structure does not repair that quotient. No priority claim
for the general counterexample principle is made.

## 5. Bounded failure depth is not bounded graph width

A possible alternative was to invoke a tree-shaped graph algorithm just from
the rank bound. The relevant graph includes the SUCCESSOR path as well as
failure-parent edges. Those extra edges matter.

For even a>=2 and b>=1, put

    rho=0 1^a (0 1^(a-1))^b,
    w=reverse(rho).

All these w are witnesses of ONE fixed four-state terminal instance:

    delta=((-1,1),(0,2),(3,1),(-1,-1)),
    s=0, F={3}, G={(1,0)}.

Its earlier one-blocks have odd length a-1, and its final one-block has even
length a. At any eligible earlier source (odd parity state 1) too few ones
remain before its zero to match a later state-0 suffix. Thus no flag fires.
The flag is genuinely live elsewhere: 1110110 is bad at source cut 1 and
target cut 4. This example is not created by vacuous annotations.

The initial prefix 0 1^a has failure parent zero at every position. In each
later length-a block, the q-th prefix endpoint (1<=q<=a) has failure parent q.
No longer border is possible because 0 1^a occurs only at the beginning.
Every later endpoint therefore has depth two.

Take the undirected graph on positions 0..|rho| with edges {i-1,i} and
{i,pi(i)}. Retain master vertices 1..a. Contract the successor path inside
each of the b later blocks into a single vertex. Its a failure edges connect
it to all a masters. After deleting irrelevant vertices and extra edges this
is K_(a,b). Taking a=b arbitrarily large gives unbounded graph width. For
example K_(a,a) has a K_(a+1) minor: pair a-1 opposite vertices as connected
branch sets and keep the remaining two vertices singly. All branch sets are
pairwise adjacent.

Thus one cannot use a bounded-treewidth theorem merely by pointing to bounded
failure-tree depth. This is a counterexample about ALL candidate structures,
not an existential obstruction: the same instance has the short witness 110.
It does not rule out a more careful logical interpretation or another symbolic
representation.

## 6. What was actually discharged

* All terminal witnesses have the exact first-return hierarchy, with depth <=k-1.
* Given a concrete reference and its full run, each layer is a completely defined
  finite automaton with exact acceptance and growth outputs.
* Shortest-endpoint and shortest-action/profile representative selection are
  false even at four and six states respectively.
* Concrete first-return residuals can form an infinite antichain, even at rank
  two on one fixed transition table.
* Failure depth alone does not give bounded width of the combined path graph.

What is NOT discharged: eliminating unknown references while preserving their
future shared-word dependencies. This is not a routine application of regular
language reachability: the automaton to be queried is built from the chosen
word itself. Bounded recursion depth does not make that infinite branching
finite or establish a uniform bound on reference lengths.

The recent negated-containment theorem is not invoked to fill this gap. Its
stated scope permits one not-contains predicate with regular constraints and
chain-free word equations. Our layered colour constraints are multiple linked
prefix-occurrence conditions depending on the same reference. No translation
into that restricted input language is proved here. Source: Havlena, Hecko,
Holik and Lengal, MFCS 2025, Theorems 28-29 and Section 8,
https://doi.org/10.4230/LIPIcs.MFCS.2025.56 .

Likewise no reduction into a pushdown, collapsible-stack or tree-automaton class
is asserted. A matching cursor into an unknown stored prefix and a bounded
failure-chain depth do not by themselves establish that model's permitted
operations or its acceptance correspondence. The original opposing undecidability
route remains live; neither an infinite antichain nor this failed quotient is
an undecidability proof.

## 7. Reproduction and evidence boundaries

    python3 experiments/check_prefix_rank_layers.py
    python3 experiments/run_experiments.py

The deterministic main check uses seed 2026091519 and records 32,767 binary
words for the pure rank identities; 458,753 literal border-chain comparisons;
101,392 milestone identities; 202,356 original-word predicate comparisons;
1,567 accepted terminal-rank checks; 192 WHOLE finite-language layer equivalences
via independent KMP/window product exhaustion; 262,142 raw family word checks;
1,392 parameterized continuation checks; both false-negative regressions; and
72 explicit complete-bipartite minor certificates. A deliberate cap is UNKNOWN.

These finite tests support the implementation. The quantified statements and
infinite families are proved above, not extrapolated from samples. Exact
all-length family proofs also establish the counterexamples' positive and
negative claims without relying on heuristic exhaustion.

The exploratory seeded search and minimization scripts are retained separately.
They found the rich collision at trial 10,354 with seed 2026091518 and reduced
it to the fixed six-state example. They are discovery artifacts, not negative
oracles. No minimal-state claim is made for either final counterexample.

The original border checker is unmodified. No full repository-wide CI, new Lean
proof, or independent mathematical reviewer is claimed. This note and the
additive patch are an unpublished checkpoint unless a successful remote commit
is explicitly reported. No unrestricted decision result has been obtained.
