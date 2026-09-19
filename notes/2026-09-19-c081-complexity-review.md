# C081: independent complexity and quantitative readback

Date: 2026-09-19. Session: `c081-complexity-20260919`.
Related work: post-C081 programme #53, A018/C080, issues #30, #34 and #37.
Base: `c946d86b9e65da2877e0df42c710abbdcb5a4037`.
Branch: `codex/c081-complexity-20260919`.
Owned path: this note only.

Status: **Conditional branch bound; pending independent accounting review.**
The direct terminal and C029 displays are explicit source-level envelopes under
the stated list model and the unintegrated `QB` dependency. They must not be
reported as an unconditional C081 runtime theorem. The historical evaluator
accounting later in this note is superseded and is retained only for provenance.

## Result and status

C081 supplies a total Boolean decision for finite expression input over bottom
and one covariant binary product, with arbitrary possibly-infinite
prefix-closed trees as the semantic values. The definitions are finite
recursions and finite list enumerations. This note gives an explicit resource
envelope for the two witness backends under a simple list cost model and a
conditional, unintegrated quantitative theorem. It does not yet give a complete
input-to-runtime theorem for normalization and summary construction.

The direct terminal route is intentionally simple: enumerate words up to the
released `Fhat` bound and run the original `witnessCheck` predicate. The C029
route uses its checked finite monitor carrier and an explicit BFS cost. These
formulas are not a useful practical complexity estimate, a PSPACE or EXPTIME
membership result, or a bound for Lean's compiled representation. The corrected
terminal clause-size estimate from the released C080 follow-up remains separate
from the C081 main checkpoint.

No lower bound currently in the repository has been transferred to the exact
C081 semantics. The closest candidate is the PSPACE-hard restricted theorem of
Niehren--Priesnitz, but its constructor signature and valuation map still need
an explicit polynomial reduction. The announced BPR19 2-EXPTIME result is
slide-level evidence for a different restriction and is not imported here.

## Checked objects being bounded

The final executable composition is in
[`EntailmentDecision.lean`](../lean/Subtail/EntailmentDecision.lean):

```text
entailsCheck
  -> normalizedEntailsCheck
  -> rawNormalizedEntailsCheck
  -> infiniteWitnessCheck I || terminalWitnessCheck (terminalize I).
```

The checked endpoints are:

* `EntailmentDecision.entailsCheck_correct` and
  `EntailmentDecision.entailsCheck_false_iff`;
* `InfiniteDecision.infiniteWitnessCheck_correct`, under the strong
  `Absorbing` property supplied by
  `SubtypeTerminalBridge.summary_absorbing`, which invokes
  `SummaryAutomaton.summary_absorbs`;
* `RankQueryDecision.terminalWitnessCheck_correct`, under
  `TerminalRank.TerminalFinals`, supplied after `terminalize`;
* `RankQueryDecision.rankDecisionStatement`, which uses the explicit
  finite query `promote (preimage I RankQueryCoverage.budget) ... (k-2)`.

The runtime definitions contain no classical choice. The proofs use ordinary
propositional classical reasoning in erased terms, but that does not provide
the algorithm. The resource argument below counts the actual finite searches
and their finite carriers.

## Quantitative C080 readback

The released C080 native follow-up has two different results that must remain
separate.

1. At proof-source checkpoint
   [`0b5d9de`](https://github.com/mhenglein/subtail/commit/0b5d9de57a36591f3fd7cb38940afde3c7f9500b),
   `RankQueryWeightCounterexample.terminal_counterexample` proves that the
   unchanged concrete preimage does not satisfy the old bundled contract
   with

   ```text
   U_k(T) = 64*k*T^(2*T+2).
   ```

   The five-state fixture emits a valid preimage clause of weight
   `12 + 30*2^175` from an input clause of weight `17`, while the old bound is
   strictly smaller. This refutes the old concrete `ClosureFor` conjunct for
   that map. It does not refute the existential `ClosureStatement`, the old
   witness-bound statement for another map, or qualitative C081.

2. The same released source proves a conservative pointwise envelope for the
   unchanged concrete compiler:

   ```text
   Uhat_k(T) = 64*k*T^(6*T^2+2).
   ```

   The source declarations are `compileValid_weight_le` and
   `preimage_clause_weight_le` in `RankQueryWeightBound.lean`. The released
   `RankQueryLengthBound.lean` then records the recurrence

   ```text
   T_0 = k + 10
   T_(j+1) = Uhat_k(T_j)
   Fhat(1) = 0
   Fhat(k) = 2*(k+1)*product_{j=1,...,k-2}(T_j+2),  k >= 2.
   ```

   Its endpoint is `terminal_witness_bound_iff` under
   `TerminalFinals`. This is a kernel-checked branch result with an explicit
   native audit, but it is still an unintegrated quantitative follow-up. It is
   a bound on the existence of one witness for a `k`-state terminal instance,
   not an input-size or runtime theorem. The old C080 `U` and `F` obligations
   therefore stay open in the canonical C081 state until the integrator has
   reconciled their exact status.

The corrected `Uhat` recurrence is used here only through the released `Fhat`
definition. If that follow-up is not accepted as an integrated dependency, the
direct terminal bound is not established; the qualitative C081 decision remains
unchanged.

## Conditional direct bounds from the released witness theorem

The earlier evaluator envelope below is retained as history, but it is too
dependent on an unreviewed cost model to serve as the current quantitative
claim. The cleanest explicit route currently available is conditional on the
quantitative branch at the exact proof-source checkpoint
[`0b5d9de`](https://github.com/mhenglein/subtail/commit/0b5d9de57a36591f3fd7cb38940afde3c7f9500b).
That checkpoint kernel-checks
`RankQueryLengthBound.terminal_witness_bound_iff`, but the module is not on the
C081 main checkpoint.

The sole additional assumption in this section is:

```text
QB(k): for every k-state terminal instance I,
  terminal witness exists iff some witness has length <= Fhat(k).
```

This is a statement about the terminal BorderAvoid instance only. It is not an
assumption about arbitrary trees, and it does not assert that the old
`ClosureFor`/`U` contract holds. The same source also proves a pointwise
clause-size bound `Uhat`; both quantitative declarations remain a separate
integration and review item.

### The conditional witness bound

Write

```text
Uhat_k(T) = 64*k*T^(6*T^2+2)
T_0 = k + 10
T_(j+1) = Uhat_k(T_j)
Fhat(1) = 0
Fhat(k) = 2*(k+1)*product_{j=1,...,k-2}(T_j+2),  k >= 2.
```

These are the definitions `improvedBound`, `weightBudget`, `growth` and
`witnessBound` in the released source, with `T_j = weightBudget k j`.

Define a separate reference evaluator, not a replacement for the current
checked `terminalWitnessCheck`:

```text
boundedTerminalCheck(I) =
  any (witnessCheck I w) over boundedLists([false,true], Fhat(k)).
```

The list contains exactly

```text
W(F) = sum_{ell=0..F} 2^ell = 2^(F+1)-1
```

candidate words. Combining `witnessCheck_correct`, `mem_boundedLists`, and
`QB(k)` gives the conditional correctness statement

```text
TerminalFinals(I) implies
  boundedTerminalCheck(I) = true iff exists w, Witness I w.
```

This wrapper is a straightforward consequence of the released declarations.
It has not been added to Lean or the production Boolean. It gives a simpler
resource target than materializing promoted query preimages.

### Direct terminal cost in a list model

Use this explicit reference model: a list cell, pattern match, Boolean
operation, and structural vector cell access costs one unit; an access to a
vector represented by a list costs at most `k+1` units. Natural arithmetic is
unit cost. This overcharges the array implementation but avoids assuming
random access.

For a word of length `ell`, `witnessCheck` checks `ell+1` cuts, one final cut,
and at most `(ell+1)(ell+2)/2` ordered `(i,j)` pairs. A cut recomputes `take`
and `runFrom`, costing at most `2*(ell+1)*(k+1)` units. Each pair performs two
`drop` operations and a prefix comparison, followed on agreement by at most two
more cuts and one nested flag lookup. A direct induction over the definitions
in `Basic.lean` therefore gives the deliberately loose source-level estimate

```text
cost(witnessCheck I w) <= 8*(k+1)^2*(ell+1)^4.
```

The fourth power absorbs list rebuilding, vector accesses, and the `range` and
`all` folds; the pair-and-cut part itself is cubic in `ell` under this model.
This is an operation count, not a measured Lean runtime theorem.

Constructing `boundedLists [false,true] F` costs at most
`4*(F+1)^2*2^(F+1)` list-cell and fold operations. Hence the conditional direct
terminal evaluator has the explicit envelope

```text
C_term_list(k) = 16*(k+1)^2*(Fhat(k)+1)^5*2^(Fhat(k)+1)
S_term_list(k) = k^2 + 4*(Fhat(k)+1)*2^(Fhat(k)+1)
```

for time and peak cells. The `k^2` term covers the transition, flag, bad and
final tables. `terminalize` adds only `O(k^2)` construction work. The space
bound includes materializing the current `boundedLists`; a streaming generator
would reduce the exponential word-list space to `O(k^2+Fhat(k))`, but that is a
new implementation and needs its own correctness check.

### The C029 finite-state BFS cost

The infinite-continuation branch does not use `Fhat`: its accepted prefix can be
unbounded. Its finite search is still bounded by the checked monitor carrier.
For a summary instance with `K` states, `InfiniteDecision.candidates` examines
at most

```text
A(K) = K*(2^(K+1)-1)
```

state/period pairs. A period of length `d` has at most

```text
H(K,d) = 2*K*d*(2^K)^d <= H(K) = 2*K^2*2^(K^2)
```

monitor states. In the same list model, one `successors` call costs at most

```text
S(K) = 16*(K+1)^4
```

for `d <= K`: `prepend` tries two letters for each of `K` predecessors,
`hasConflict` scans at most `d` phases, each phase comparison scans at most
`d` positions, and `flaggedIn` scans at most `K` states. This polynomial is
deliberately loose and follows the nested definitions in `PeriodicMonitor.lean`.

`FiniteSearch.saturate` makes at most `H(K)` rounds. A round examines at most
`H(K)` visited states and `2K` successor candidates; duplicate suppression scans
at most `H(K)` visited states. A structural equality test on two monitor states
costs at most `E_state(K)=4*(K+1)^2` cells because it compares all `d` buckets
of width `K`, with `d <= K`. Thus a finite BFS envelope is

```text
C_BFS(K) = 2*K*H(K)^2*(S(K) + H(K)*(E_state(K) + 1) + 1).
```

The cycle and seed checks are below `32*(K+1)^4` in this model, so a coarse
C029 branch envelope is

```text
C_infinite_list(K) = A(K)*(C_BFS(K) + 32*(K+1)^4).
```

`H(K)` bounds monitor rounds and storage, not the length of the original prefix
represented by an accepted monitor path. It does not provide a finite bound on
every infinite-branch witness word.

### Scope for the complete C081 input

For normalized input, the summary automaton has `K = 4^N` physical states.
Under `QB(K)`, the witness backends therefore have the explicit conditional
envelope

```text
C_branches(N) = C_infinite_list(4^N) + C_term_list(4^N).
```

The summary construction and normalization still need their own loop-level
accounting audit. The old `R_N/A_N`, diagram-enumerator `E`, query-materializing
`B_j`, and finite-table `Wtab` displays below are consequently historical
drafts, not part of the claimed envelope. A complete input-to-runtime theorem
needs an explicit `C_summary(N,V,r,n)` and acceptance of the `QB` branch as an
integrated dependency. Until then, `C_branches` is a useful conditional bound
on the two witness backends, not an unconditional C081 complexity theorem.

Under binary natural arithmetic, let `b` be the maximum bit length of `K`,
`Fhat(K)`, `H(K)` and the input indices. If each unit-cost operation costs at
most `O(b^2)` schoolbook bit operations, multiply the displayed counts by
`O(b^2)`. No standard complexity class follows: `N` may already be large under
the expression encoding, and `Fhat` is an enormous tower-like recurrence.

## Historical draft envelope (superseded; do not cite as a bound)

The following section records the earlier attempted evaluator accounting for
provenance. Its `R_N/A_N`, diagram and table exponents were not checked against
every loop and function representation. It remains useful as a list of audit
targets, but it is not an established resource theorem.

## Input and normalization size

Use a structural size first. Let `V` be the total number of expression
constructors in the two query expressions and every side of every premise:

```text
V = |s| + |t| + sum_{(l,r) in G} (|l| + |r|).
```

Let `n` be the variable-domain size and `r = |G|`. Every product constructor
contributes one entry to `Expr.pairs`, so the number `P` of collected product
occurrences in `naming G s t` satisfies `P <= V`. If `b` is the Boolean saying
that bottom occurs, then the normalized variable count is

```text
N = n + b + P <= n + V + 1.
```

The normalized constraint list contains one denial when bottom is used, two
constraints per product occurrence, and the original premises. Therefore

```text
M = |normalized G s t| <= 1 + 2*V + r.
```

These are bounds on data sizes, not on evaluation time. The `locate` calls,
list membership, expression traversals and vector construction add at most a
polynomial factor in `n+V+r` under a unit-cost list model. For binary encoded
indices and `n`, replace `n`, `V` and `r` by their numeric values; the
structural bound is the safer statement because unused variables can make `n`
large without adding expression constructors.

## Summary automaton and the C029 branch

For a normalized system with `N` variables, `SummaryAutomaton.states` contains
all ordered pairs of subsets of `Fin N`. Its physical state count is

```text
K = 4^N.
```

The summary instance stores `K` transitions, `K` bad/final bits and a `K by K`
flag matrix. Its explicit representation therefore already needs
`Omega(K^2)` Boolean cells. The `advance` operation recomputes two `nextSet`
values. `nextSet` scans a target state, a current subset and an intermediate
state, and calls `balancedCheck` for the finite push/pop system.

For a coarse evaluator bound, put

```text
R_N = 2^(4*N^2) * (N+1)^20
A_N = (N+1)^6 * (R_N+1).
```

`R_N` intentionally dominates the current powerset closure tests. There are
`N^2` possible control pairs and at most `2^(N^2)` candidate relations in a
`balancedCheck`; each closedness test has only polynomially many nested scans.
This is the cost of the current list-based implementation: every invocation
of `balancedCheck` re-enumerates those candidate relations, so the envelope
does not assume memoisation or a polynomial saturation engine. A separate
saturated-table implementation could lower this factor, but it would need an
independent correctness and cost argument.
The recursive `popCheck` on a word of length `d` is bounded by a factor
`(N^2+1)^d` over the same finite relation cost. The `R_N` envelope is large
enough for the empty and bounded words used while constructing the summary
instance and its guards. `A_N` bounds one two-letter summary transition after
including list scans and arithmetic overhead.

A construction of the whole summary instance can therefore be charged to

```text
C_summary(N) = K^2 * (A_N + R_N + 1).
```

This is a cost envelope, not a measured implementation bound. It includes the
repeated `satCheck C` calls in the vector fields and the dense flag matrix.

### Infinite continuation

`InfiniteDecision.candidates` enumerates every state `q` and every binary word
`c` of length at most `K`. Hence the candidate count is at most

```text
Cand(K) = K * (2^(K+1) - 1).
```

For a period of length `d`, the reverse monitor carrier has the proved bound

```text
H(K,d) = 2*K*d*(2^K)^d.
```

This is `InfiniteDecision.monitorCapacity`. The maximum for `d <= K` is

```text
H_K = 2*K^2*2^(K^2).
```

`prefixCheck` saturates a list of monitor states with this numeric fuel. A
monitor state has one current control, one phase, one matching bit, and `d`
bit-vectors of width `K`. Its successor list tests at most two letters for each
of `K` predecessor controls. Allowing for list membership, bucket comparisons,
phase comparisons, and the `hasConflict` scan, the deliberately generous
per-candidate envelope

```text
C_monitor(K) = (K+1)^5 * (H_K+1)^3
```

dominates the `H_K` saturation rounds and their finite successor scans. The
cycle checks also run the summary transition on every cut, so a combined
reference bound for the C029 branch is

```text
C_infinite(N) = C_summary(N)
  + Cand(K) * ((K+1)^2*(A_N+1) + C_monitor(K) + H_K + 1),
  where K = 4^N.
```

The monitor proof uses a finite carrier but does not bound the unknown witness
prefix. `H_K` is a bound on monitor search rounds, not a bound on the original
word prefix. This distinction is essential when describing the algorithm.

## Terminal branch: explicit finite query envelope

The terminal branch receives an instance with `q` states. In C081 this is
`q = K` after `terminalize` of the summary instance. The outer decision checks
two letters and `q^2` state pairs, then runs `safeReferenceCheck` and
`satCheck` on a graph with one letter and two prefix-graph vertices.

Let an input clause have weight `T`. The released corrected budget proof gives
the following safe bounds for diagrams satisfying the concrete budget:

```text
G = 2*T             groups
C = 7*T^2           core variables
P = 6*T             pieces per atom
J = 6*T^2            seam entries
S = 13*T^2           exclusive scalar bound
```

The constants are rounded upward from the checked coverage definitions:
`blockBound <= 3T`, `groupBound <= 2T`, `coreBound <= 7T^2`,
`perAtom <= 6T`, `seamEntries <= 6T^2`, and
`scalarBound <= 7T^2+10T+1 <= 13T^2` for `T >= 2`.

The finite alphabets used by `RankQueryEnumeration.diagrams` have these upper
bounds:

```text
|locations C G| <= 9*T^2
|pieces S| = 20*S^4
|seams S| = S^4
|colours q| = 12*q*2^q.
```

`boundedLists(X,m)` has at most `(X+1)^m` elements, and
`exactLists(X,m)` has exactly `|X|^m` elements. Consequently a conservative
upper bound for the complete diagram enumeration of one clause is

```text
E(q,T) = (G+1)*(C+1)*(9*T^2)^T*q^G*3^G*2*(12*q*2^q)
         *((20*S^4+1)^P)^T*(S^4+1)^J,
```

with `G,C,P,J,S` substituted from the preceding display. The factors are,
in order, groups, core variables, locations, state lists, next-bit lists,
the first bit, the old endpoint colour, the per-atom piece paths, and seam
lists. Filtering by `validDiagram` cannot increase this count. This is a
bound on the actual redundant enumerator in
`RankQueryEnumeration.diagrams`, not on a smaller normalized search.

Let

```text
T_0 = q + 10
T_(j+1) = 64*q*T_j^(6*T_j^2+2).
```

`T_0` is the checked `finishQuery` envelope. `T_j` bounds the maximum clause
weight at promotion level `j` if the released corrected C080 source lemma is
accepted. The query cardinality obeys

```text
Q_0 = q
Q_(j+1) = Q_j * (1 + E(q,T_j)).
```

The `1` is the retained old query in
`promote`; the second term is its concrete preimage. The query has depth
`h = q-2` (natural subtraction, so one-state and two-state cases are explicit
edge cases). Thus

```text
Q_h <= q * product_{j=0,...,h-1} (1+E(q,T_j)).
```

The definition of `promote` recomputes the previous level as the left operand
and again as the input to `preimage`. A safe construction-time recurrence is

```text
B_0 = q * L_0
B_(j+1) = 2*B_j
          + Q_j*E(q,T_j)*(Denc(q,T_j) + Wtab(q,T_j,L_(j+1))
                           + L_(j+1) + 1).
```

Here `B_j` is a reference cost for materializing the query, `Denc` is the
finite encoding length of one bounded diagram, and `L_j` is a full finite
encoding bound for one output clause. A generous choice is
`Denc(q,T)=(q+T+1)^12`; it charges every bounded list element, piece field and
seam field, plus the fixed-depth guard and compilation scans used by
`validDiagram` and `compileValid`. It is deliberately larger than the
polynomial diagram record. The exponent is an accounting choice for this
reference evaluator, not a kernel-checked theorem about Lean's evaluator.

`Wtab` is the additional work charged while evaluating one candidate diagram
and reifying its finite observer tables. For a deliberately large conditional
accounting convention, set

```text
Wtab(q,T,L) = (q+T+1)^16
                * (Obs(q,T+1) + (T+1)*Pred(q) + L + 1).
```

The factor charges inherited table reads, table-entry construction, colour
and mask operations, and compilation scans in addition to the output length
`L`. This formula is **conditional and pending review**: the current note has
not proved that exponent 16 dominates every concrete `compileValid` loop or
the actual representation of function fields. Until that accounting audit is
completed, the recurrence for `B_j` is a proposed reference model rather than
an accepted runtime theorem.

The weight `T_j` alone does not bound a raw clause's `tests`, `equal` and
`unequal` list lengths, nor the representation of observer functions. Any
honest runtime theorem must charge those fields. The following table model
does so. Let `Col(q)=12*q*2^q`. A table encoding of an observer with at most
`s` controls has at most

```text
Obs(q,s) = 4*s^2*Col(q)^2 + s*Col(q) + 2*s
```

Boolean table cells, covering `move`, `allows`, initial controls and final
controls. Let `Pred(q)=Col(q)` charge one arbitrary colour predicate. Set
`L_0 = 1 + 3 + 1 + 2 + Obs(q,2) + Obs(q,q) + Pred(q)` per finish clause. The
two observer terms charge the `oneEdge .F` observer of size 2 and the
`finishObserver I q` observer of size `q`; both are present in every clause.
For the output
of one valid diagram, the checked piece estimates give at most `6*T^2` piece
occurrences and `12*T^3` active interval observations. The recurrence

```text
L_(j+1) = (L_j + 20*(T_j+1)^2 + 10*T_j + 1)
          * (Obs(q,T_(j+1)) + (T_(j+1)+1)*Pred(q)
             + q + T_(j+1) + 1)
```

is a deliberately loose envelope for list elements, indices, inherited tests,
core pairs, generated atoms, the colour predicates on those tests and the
finite tables of every generated observer. It is not a theorem about the
Lean closure representation; it is a precise finite-table accounting
convention for the reference evaluator.

For a two-vertex prefix graph, define a coarse table-interpreter cost

```text
Reach(q,T) = (2*T+1)^4 * (q+T+1)^2 * (Obs(q,T)+Pred(q)+1)
Sat(q,Q,T,L) = Q * 2^T * (L + T*Reach(q,T))
                 * (Col(q)+Obs(q,T)+1).
```

`2^T` enumerates every assignment to a clause with at most `T` variables;
`Reach` dominates the finite observer-node saturation for a two-vertex graph;
`L` charges tests and equality lists; and the last factor charges finite table
lookups. This is intentionally larger than the actual one-letter graph cost.
The terminal branch is bounded by

```text
C_terminal(q) = B_(q-2)
  + 2*q^2 * (L_(q-2) + Sat(q,Q_(q-2),T_(q-2),L_(q-2)) + 1).
```

For the C081 summary instance, use `q=K=4^N`. The combined reference
evaluator bound is therefore

```text
C_C081(N,V,r,n) = C_summary(N) + C_infinite(N) + C_terminal(4^N)
                  + poly(n+V+r),
```

with the terminal expression evaluated using the displayed `T`, `E`, `Q`,
`L` and `B` recurrences. The terminal term dominates almost immediately, but
retaining the three terms records which checked branch creates each resource
cost.

## Space and arithmetic accounting

The list definitions materialize intermediate lists. A streaming evaluator can
reduce the diagram-enumeration factor, but that would be a new implementation
and needs a correctness proof. For the current list-based reference evaluator,
a safe peak-space envelope is the maximum of:

```text
K^2;
H_K;
max_j Q_j*E(q,T_j)*(Denc(q,T_j)+Wtab(q,T_j,L_(j+1))+L_(j+1));
max_j Q_j*L_j;
```

plus the finite table cells charged by `Obs`. The first term is the summary
flag matrix, the second is the largest C029 monitor carrier, the third is a
materialized preimage round, and the fourth is the promoted query.

The displays use unit-cost natural arithmetic. For a concrete binary model,
let `bitlen(0)=1` and let `b` be the maximum bit length of the input numerals
and of every displayed intermediate (`K`, `H_K`, `E`, `Q_j`, `T_j`, `L_j`,
`B_j`, and `Wtab`). Under schoolbook arithmetic, addition and comparison cost
`O(b)`, while multiplication, division and remainder cost `O(b^2)`; list and
table indexing is charged at most `O(b)` and is absorbed by `O(b^2)`. Thus a
sufficient bit-operation envelope for the unit-cost count `C` is `O(C*b^2)`,
provided the conditional `Wtab` accounting is first validated. This explicitly
includes arithmetic and encoding costs; a tighter bound would need a different
representation and arithmetic model. No standard complexity class is claimed:
even with binary input encoding, `N` can be exponential in the declared
variable-index bit size, and the promotion recurrence iterates a rapidly
growing function `q-2` times.
At the finite-code level all displayed operations are primitive recursive;
that is the appropriate qualitative classification for this envelope, not a
practical algorithmic estimate.

## Lower-bound transfer audit

The following results are relevant but do not currently yield a lower bound for
C081.

| Source | Reported result | Transfer status |
|---|---|---|
| Niehren--Priesnitz 1999, Proposition 1 and Theorem 14, [primary record](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment:99.html) | PSPACE hardness/completeness for a restricted grammar over an ambient bottom/top/binary-product domain, for finite and all possibly-infinite trees | **Candidate only.** A transfer needs a polynomial map into `Expr`, a map for the ambient greatest tree, equality-to-two-inequality encoding, and preservation of satisfiability and query entailment in both directions. The source's semantic top is not an explicit Subtail constructor, but that observation alone does not prove the maps. |
| Niehren--Priesnitz 2002/03, [journal record](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment:02.html) | Automata/cap characterizations with shared continuation words and finite/regular/infinite tree distinctions | **No lower-bound transfer.** It supplies a close structural comparison, not a reduction to the exact C081 input language or a complexity theorem for the new finite evaluator. |
| Breuvart--Penelle--Rehof 2019, [author slides](https://lipn.univ-paris13.fr/~breuvart/articles/NSSA_journee.pdf) | Announced 2-EXPTIME restriction for a subtype fragment | **Unverified and different scope.** The available source is slides, and it changes constructor restrictions and quotient assumptions. It cannot establish a C081 lower bound. |
| Diekert--Gutiérrez--Hagenah 2001, [primary preprint](https://arxiv.org/abs/cs/0103018) | PSPACE-completeness for existential word equations with rational constraints | **Backend only.** A word-equation solver could support a restricted terminal proof; no reduction from C081 to the source in the hardness direction is present. |
| Barceló--Figueira--Romero 2019, [primary preprint](https://arxiv.org/abs/1904.00850) | ExpSpace-completeness for boundedness of conjunctive regular path queries | **Object mismatch.** Standard path atoms do not share one generated physical extension as C080 requires, and no graph inverse-image transfer has been proved. |

C067's written one-source result is a PSPACE upper-bound route, not a lower
bound. The withdrawn Schubert 2021 argument is a warning about preserving a
whole conjunction under substitution, not a hardness result. A bounded search,
nonregular witness language, or failure of the old U bound gives no lower
bound.

The first useful lower-bound task is therefore concrete: formalize the NP99
restricted grammar and its arbitrary-tree semantics, define the polynomial
translation to `Expr (Fin n)` and expression constraints, and prove both
directions for satisfiability and the queried inequality. Until that is done,
the canonical status should remain “no transferred lower bound.”

## Independent review and limitations

This is a read-only mathematical review of the C081 definitions and the
released C080 source statements. It does not change Lean code, run the huge
diagram enumerator, or claim a full native runtime benchmark. The C080 source
was read at its exact proof checkpoint and its ordinary counting argument was
separated from the old refuted bound. The direct terminal and C029 formulas
are source-level operation counts under the explicitly stated list model; they
are conditional on `QB` and have not been kernel-instrumented or benchmarked.
The historical `R_N/A_N`, `E`, `B_j` and `Wtab` displays above are superseded
and must not be promoted to `Established`. A complete review still needs to
check the summary construction, normalization, binary arithmetic, and the
exact integration status of the quantitative branch.

The remaining discriminating questions are:

1. Can `QB` and the direct `boundedTerminalCheck` wrapper be accepted as an
   integrated quantitative dependency without changing the C081 theorem?
2. Can the summary construction and normalization receive the same explicit
   loop-level accounting, yielding a complete input-to-runtime bound?
3. Can the NP99 restricted theorem be transferred exactly, yielding at least
   PSPACE-hardness for C081?
4. Can the bounded terminal search be streamed while preserving the checked
   `Witness` semantics, and what proof cost does that introduce?

The current answer to all four is open. Qualitative decidability is complete;
the practical and standard-complexity story is not.
