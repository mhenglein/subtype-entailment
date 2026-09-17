# Exact elimination of one unknown reference

Date: 2026-09-15. Same baseline and exact semantics as the
[global rank attempt](2026-09-15-unrestricted-rank-attempt.md).

**Written proof plus native finite algorithm and independent graph/oracle
checks. Independent mathematical review pending; not Lean-checked.** This
repairs one failed quantifier-elimination step, not unrestricted composition
of all the reference-growth levels. No stable claim ID is allocated.

## 1. Exact question

Fix a binary terminal instance I with k states, and a concrete nonempty safe
reverse reference B of length m with its entire run r_0,...,r_m. Is there a
witness continuation requiring at most ONE additional first-return milestone?

The answer is decided below with no word-length or loop-count cutoff. More
explicitly, either complete directly without a new occurrence of B, or choose
ANY safe first-return extension C of B and complete without a new occurrence
of C. The choice of C is unbounded and existential, not a supplied string.

A return at the final endpoint still counts as a new milestone. The finish
mode here therefore REJECTS every full return of its current reference, even
when that endpoint's original state is the input start. A word ending at that
return may instead be accepted when it is explicitly counted as the promoted
reference. This convention is essential to the rank bound.

## 2. A grown reference has a fixed reset core

Let C be any first-return extension of B. For every m<=j<|C|,

    pi_C(j)<m,       and       pi_C(|C|)=m.

A proper border of length at least m at an earlier j would put a new B
occurrence no later than j, contradicting first-return minimality.

Now consider the finite matching graph for FINISHING after C. Its live nodes
are (q,j), where q is an original reverse-run state and 0<=j<|C| is the current
match length against C. A matching next letter advances j to j+1. A mismatching
letter first drops to pi_C(j) and follows failure links. For j>=m, all those
fallback indices are below m, so the final mismatch destination is at most m.

Therefore this graph has:

* a fixed core of nodes (q,j) for 0<=j<=m;
* one column of k nodes for each later pattern position;
* matching edges to the next column;
* every nonmatching edge back into the fixed core.

The word's reference-state colours at a new column are used for its flag test,
and its lower border chain is determined by pi_C(j) and the known B. All core
transitions below m are fixed by B. Outgoing transitions at column m are fixed
when the first new letter of C is read. No transition may leave a complete
C-match endpoint in the finishing graph.

Add one accepting sink A, reached without input from every live node with
q=s. A node at match length |C| is NOT live for this purpose: reaching the full
pattern would exceed the allowed milestone count. The finish question is
reachability of A from (r_|C|,m), since m is the longest proper border of C.

## 3. Exact finite-interface construction

Generate C, one labelled reverse edge at a time, using the fixed-reference
layer automaton for B. Its state (q,h) supplies:

* q, the current original reverse-run state;
* h=pi_C(j), below m until the final first return;
* the new bit and new original state for each proposed extension.

Alongside it, construct the matching graph of the growing pattern. Retain only
the reachability relation among:

    k*(m+1) fixed-core nodes,
    one accepting sink A,
    k nodes in the current frontier column.

Their total number is

    n = k*(m+2)+1.

When a new pattern position is appended, the old frontier becomes a proper
pattern prefix. Add its accepting-sink edge when q=s, its matching edges to a
new frontier, and all its mismatch edges to the fixed core. The guard on a
matching edge into new original state p tests the new reference colour and
all colours on the B-chain rooted at the new h. Mismatch guards use the
corresponding B-prefix chain. Diagonal and empty-suffix pairs are included.

Take reflexive transitive closure, then remove the old frontier and retain
the new one. A fresh frontier does not yet have an accepting edge: it may be
the complete final C. That edge is added only if another character later makes
it a proper prefix. Initially column m is in the retained fixed core, not a
forgettable frontier.

**Interface lemma.** This closure-and-projection operation preserves exactly
all reachability information that a future extension can use.

**Proof.** An old retired column has had all its outgoing transitions installed.
Every future mismatch edge ends in the fixed core; every future matching edge
ends in the next new column. Thus no future edge has an endpoint in a retired
column. Any future path through retired columns decomposes into paths between
retained nodes, already recorded in the closure. Conversely every recorded
relation has an actual path through the specific graph generated so far.
Replacing it by that path reconstructs any successful extended reachability
calculation. Induction proves the invariant after every appended character.
QED.

The summary contains a relation on a FIXED finite interface, rather than the
full transition action of the original word. The six-state counterexample in
the companion note is correctly distinguished by this larger, semantically
justified relation. Different pattern words are merged only when their actual
future graph-construction state agrees.

## 4. Complete search and reconstruction

A search state is (q,h,initial,R), with R the interface relation. The initial
flag distinguishes the first appended letter, when column m must be retained.
Transitions choose an actual labelled reverse edge accepted by the B-layer
machine and apply the exact interface update.

If the B-layer reaches its first full return, C is complete. Test whether
(r_|C|,m) reaches A in R. A successful relation gives an actual C from the stored
search predecessor path. Run the independent fixed-reference graph on that
literal C to reconstruct its finishing word. Check the full original word with
both existing witness predicates.

If the test fails, that completed first-return branch ends. Otherwise, before
the B return, identical finite search states may be merged. The interface
lemma proves that all future continuations have identical effects for the
ONE-promotion question; this is the exact justification missing from the
refuted action/profile heuristic.

There are at most

    V = 1 + k*m*2^(n^2)

reachable generator states (the initial flag occurs only at the single start).
Thus uncapped finite exhaustion is a complete negative answer to this scoped
question. A shortest retained generator path gives |C|<=m+V. A finishing path
uses at most k*|C| live states. A conservative full-word bound is

    (k+1)*(m+1+k*m*2^((k*(m+2)+1)^2)).

No performance optimality is claimed. The native implementation keeps relations
as integer bitsets. Its work and state caps return UNKNOWN, not negative.

## 5. Consequence and exact limit

Handle an empty witness directly. For a nonempty word the first milestone is
one letter with one of finitely many reversed terminal edges. Apply the above
one-promotion solver to each such reference (m=1). This decides existence of a
witness whose reversed border-chain depth is at most TWO, for an arbitrary
binary terminal input, without assuming a run/length or return-word bound.

The output NO_WITHIN_RANK_TWO is NOT unrestricted NO. In the prior modular
family with three periods (1,1,1), every witness is (1^a0)^3 for a>=1. Each has
maximum reversed border-chain depth three. The rank-two query is exactly
negative although 101010 is an original witness. The existing C046 family,
not a new construction, supplies this boundary regression.

For unrestricted existence the rank can be as large as k-1. It is NOT proved
that this elimination construction is closed under repeated reference growth.
At the next promotion, an entire unbounded C becomes the new fixed core; its
internal positions, not just the old interface, can be addressed by future
matches. The reachability relation above does not purport to preserve those
newly addressable positions. Reapplying it without a new argument would repeat
the earlier quotient error at a higher level.

Thus the valid result is exact elimination of ONE unknown pattern. An effective
higher-level summary or a different termination proof remains necessary. Neither
a generic string-solving theorem nor a named stack model is used to hide it.

## 6. Independent checks and prototype correction

    python3 experiments/check_one_promotion.py

The deterministic run uses seed 2026091520. It checks 180 acyclic instances
against their completely enumerated accepted languages (102 positive, 78
rank-two negative), 351 whole matching-graph summaries against independent
literal-transition/DFS reachability (107,350 boundary pairs), nine infinite
two-block modular positive oracles, and three positive-but-rank-three modular
oracles. Both earlier quotient failures and their equality-antichain variant
are solved positively. Explicit state/work caps return UNKNOWN.

The first prototype gave a complete-pattern return at the final endpoint a
free accepting transition. A dedicated unary-path audit found this would
incorrectly call the only word 000 depth-two, even though its depth is three.
The implementation was repaired before this saved result: full-hit frontiers
have no acceptance edge, and the fixed-reference finishing call forbids full
returns. Seven unary terminal paths now guard that boundary convention.
The earlier finite random sample had not exposed it; its success was not a
substitute for this audit. The final suites were rerun after the fix.

No complete higher-rank solver, full repository CI, independent mathematical
review, or Lean verification is claimed. This is a native finite procedure for
its stated quantifier, not an incomplete SMT backend dressed as a decider.
