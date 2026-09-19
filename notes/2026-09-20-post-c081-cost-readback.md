# Post-C081 cost accounting readback

Date: 2026-09-20
Reviewer: independent successor accounting review for issue #53
Scope: the conditional terminal and C029 backend envelopes only

## Evidence and boundary

I read the complexity note at
[`6ec3163`](https://github.com/mhenglein/subtail/commit/6ec31634ab6279ddd7d977ddaf11bc0353d393eb),
which is unchanged at parent revision
[`cfb46f5`](https://github.com/mhenglein/subtail/commit/cfb46f516b4da8aacfc01eac14653d11368b84bd),
and compared its current formulas with the source at `c946d86`:
`Basic.lean`, `PeriodicMonitor.lean`, `InfiniteDecision.lean`, and
`FiniteSearch.lean`. I also read the quantitative branch statements from
[`0b5d9de`](https://github.com/mhenglein/subtail/commit/0b5d9de57a36591f3fd7cb38940afde3c7f9500b)
and the handoff in [issue #48](https://github.com/mhenglein/subtail/issues/48),
including `RankQueryWeightBound.weightBudget`, `improvedBound`,
`RankQueryLengthBound.growth`, and `witnessBound`.

This is a source-level accounting review. I did not run Lean, enumerate the
large searches, or promote the C080 branch into C081. Summary construction,
normalization, and the remaining `QB` integration are outside this note.
The old `R_N/A_N`, diagram-enumerator, `Wtab`, and materialized-query displays
in the complexity note are superseded and are not used below.

## What survives the review

The following are justified as conditional reference-model statements.

* For a `K`-state C029 instance, the candidate generator examines at most
  `A(K) = K(2^(K+1)-1)` state/word pairs. This follows directly from
  `finRange K` and `boundedLists bools K`.
* A period of length `d` has at most
  `H(K,d) = 2*K*d*2^(K*d)` monitor states. This is the source definition
  `monitorCapacity` and the checked `allStates_length_le` bound. For
  `d <= K`, `H(K) = 2*K^2*2^(K^2)` is a valid uniform carrier bound.
* `FiniteSearch.reachesAnyWithFuel` uses the carrier bound as fuel. It does
  not materialize `allStates` at runtime; that list occurs in the correctness
  theorem. The runtime saturation still performs the source's `close`, list
  membership, list equality, and successor loops.
* The branch-#48 recurrence and endpoint are correctly stated as a separate
  conditional dependency:

  ```text
  T_0 = K + 10
  T_(j+1) = 64*K*T_j^(6*T_j^2+2)
  Fhat(1) = 0
  Fhat(K) = 2*(K+1)*product_{j=1,...,K-2}(T_j+2), K >= 2.
  ```

  `Fhat` bounds a terminal BorderAvoid witness under the checked branch
  theorem. It is not an input-size or runtime bound for complete C081.

The direct per-word estimate and the C029 BFS estimate can remain useful as
deliberately loose source-level bounds, but only after fixing the accounting
items below and stating the data representation explicitly.

## Gaps in the current displays

The current note has four accounting gaps.

1. `S_term_list = k^2 + ...` names the dense flag matrix but does not charge
   the transition vector, bad/final vectors, initial state, or the temporary
   word/list cells separately. The `k^2` term asymptotically dominates them
   for `k >= 1`, but the displayed expression is not an explicit encoding
   bound.
2. The direct formula charges enumeration up to `Fhat(K)` but does not charge
   computing `Fhat`. This matters because the literal `growth` definition
   recomputes `weightBudget K j` recursively for each factor, and each
   `improvedBound` contains a huge recursive exponentiation.
3. The C029 formula charges the monitor carrier's number of states but does
   not state the cost of computing `monitorCapacity`, candidate-list
   construction, or the payload cells of each monitor state. The source
   saturation can hold up to `2K` successor candidates per visited state.
4. `E_state(K)=4(K+1)^2` is safe for structural vector equality under a
   flat-cell encoding, but it is not justified under the note's separate
   statement that vector access scans a list. The corrected bound below uses a
   larger `E_state` that covers either implementation. The source loop shapes
   fit the resulting exponents.

These are repairs to the reference accounting, not counterexamples to the
qualitative decision theorem.

## Explicit reference encoding

Use the following conservative list model.

* A list spine cell, Boolean, finite-index value, option tag, pair, and natural
  arithmetic operation costs one unit. A vector of length `n` is encoded as an
  `n`-cell list; indexed access costs at most `n+1` units.
* Structural equality of a monitor state is charged by the larger bound
  `E_state(K)=8*(K+1)^3`. This overcharges the `d*K` bucket bits for `d<=K`
  and also covers nested list lookups and representation tags.
* A binary word of length `ell` occupies at most `ell+1` list cells. Natural
  exponentiation is charged by its source recursion: `a^e` uses at most
  `2e+2` unit steps. This explicitly charges the large exponents in
  `improvedBound` and `monitorCapacity`.

For the input instance, the following explicit cell bound charges every field:

```text
I_cells(k) = 2*k^2 + 9*k + 1 <= 4*(k+1)^2.
```

The first term covers the nested flag table; the linear terms cover its list
spines, transitions, bad/final vectors, option fields, and initial state.
The exact constant is deliberately generous. A binary encoding replaces each
finite index/natural cell by its bit length; the operation counts below are
then multiplied by `O(B^2)`, where `B` is the maximum bit length of all
intermediate numerals, including `K`, `Fhat(K)`, `H(K)`, and the `T_j`.

## Corrected direct terminal envelope

Let `m=max(K-2,0)`, and let `T_j` be the branch-#48 sequence above. Define
`e_j=6*T_j^2+2`. The literal source definitions recompute lower budgets inside
each call to `growth`; therefore a safe unit-operation charge for computing the
bound is

```text
C_F(K) = 32*(K+1)^2 + sum_{j=0,...,m-1} (m-j)*(4*e_j + 32).
```

The summand charges one `weightBudget` call, including all recursively rebuilt
lower `T_i`, the `e_j` exponentiation, the constant multiplications, and the
growth/product operations. A memoized implementation can be cheaper; this
formula covers the current definitions. Let `F=Fhat(K)`.

The number of candidate words is

```text
W(F) = sum_{ell=0..F} 2^ell = 2^(F+1)-1.
```

The source-level list construction and direct `witnessCheck` loops are covered
by the following repaired conditional envelope:

```text
C_term_list(K) = C_F(K) + 64*(K+1)^2*(F+1)^5*2^(F+1)
S_term_list(K) = 2*I_cells(K) + 4*(K+1) + 8*(F+2)*2^(F+1).
```

The time term includes `terminalize`, `boundedLists`, the `W(F)` words, and a
loose per-word bound for `witnessCheck`; the extra factor `(F+1)^2` absorbs
`take`, `drop`, prefix comparison, the two cut ranges, and repeated `runFrom`
calls under list vector access. The space term includes both input/output
instances, the bound-computation stack, all word cells retained by the
materialized `boundedLists`, and the list spines. If `Fhat(K)` is supplied as
an external parameter rather than computed, omit `C_F(K)` and the corresponding
four-cell stack term; the enumeration term remains.

This is conditional on the branch-#48 witness theorem (`QB` in the complexity
note) and is a bound on a separate `boundedTerminalCheck` wrapper. It is not a
claim about the existing promoted-query implementation.

## Corrected C029 envelope

Set

```text
W_K = 2^(K+1)-1
A_K = K*W_K
H_K = 2*K^2*2^(K^2)
S_succ(K) = 64*(K+1)^4
E_state(K) = 8*(K+1)^3.
```

The `S_succ` exponent accounts for the `K` predecessor states, two letters,
`prepend`, nested `hasConflict` scans over phases and flagged states, vector
access, and construction of the returned monitor states. The exact constant is
not material; 64 is a fixed overestimate for the stated encoding.

For a visited list of at most `H_K` states, one saturation round costs at most
`H_K*S_succ` for `flatMap successors`, `2*K*H_K^2*E_state` for
`addNew` membership and state equality, and `H_K*E_state` for the fixed-point
list comparison. With at most `H_K` rounds, a safe BFS bound is

```text
C_BFS(K) = H_K^2*(S_succ(K)+1)
           + 2*K*H_K^3*(E_state(K)+1)
           + H_K^2*(E_state(K)+1)
           + H_K.
```

This includes the actual `FiniteSearch.saturate` recursion and duplicate
suppression. It does not charge a conceptual `allStates` list because
`reachesAnyWithFuel` does not evaluate that theorem argument.

Candidate filtering and capacity arithmetic add

```text
C_cycle(K) = 64*(K+1)^4
C_cap(K) = 16*(K+1)
C_words(K) = 8*(K+1)^2*W_K.
```

`C_cycle` covers `cycleCheck` and all `safeRunCheck` cuts for a word of length
at most `K`; `C_words` covers construction of the bounded word list and its
pair list. `C_cap` charges the two `Nat.pow` calls in `monitorCapacity` and
the arithmetic around them under the explicit unit-cost recursion.

Thus a corrected conditional time envelope for the complete C029 backend is

```text
C_infinite_list(K) = C_words(K)
  + A_K*(C_cycle(K) + C_cap(K) + C_BFS(K) + 8*(K+1)).
```

For space, a monitor state with `d<=K` occupies at most
`State_cells(K)=4+2*K*(K+1)` cells under the nested-vector encoding. The
successor list can contain at most `2*K*H_K` state values before duplicate
suppression. A safe peak bound is therefore

```text
S_infinite_list(K) = 2*I_cells(K) + 2*A_K
  + 8*(K+2)*W_K
  + (2*K*H_K + H_K + 1)*State_cells(K) + 4*K*H_K.
```

The first terms retain the input and candidate lists; the final terms charge
the visited and successor state payloads and their list spines. This repairs
the earlier `H_K`-only space display, which counted monitor cardinality but not
the data stored in each state.

## Combined status and limits

Given a `K`-state terminalized summary instance, the repaired conditional
backend envelope is

```text
C_backend(K) = C_term_list(K) + C_infinite_list(K)
S_backend(K) = max(S_term_list(K), S_infinite_list(K)).
```

For normalized C081 input one may substitute `K=4^N`, but this remains only a
backend substitution. It does not charge normalization, summary construction,
or QB integration, so it is not a complete C081 input-to-runtime theorem.
The qualitative decider remains independent of this quantitative branch.

Under binary arithmetic, multiply the displayed unit-operation counts by
`O(B^2)` and add `O(B)` bits per live numeric field. The giant `Fhat` and
monitor exponents are now charged both through their recursive source loops and
through the bit length of their intermediate numerals.

## Review conclusion

The cardinal formulas, the conditional status, and the separation from the
qualitative C081 theorem are sound. The earlier time displays were close as
loose asymptotic envelopes, but the space and construction accounting was
incomplete. The repaired formulas above are suitable as an explicit reference
model after integration review; they are not Lean-verified runtime theorems.
No lower bound is transferred, and no C080 or C081 claim is promoted.

Status: `READY_FOR_INTEGRATION` after this note-only review. The existing
complexity note and all source, Lean, paper, and ledger files remain read-only.
