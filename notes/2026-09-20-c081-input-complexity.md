# Complete original-input resource bound for a C081 reference algorithm

Date: 2026-09-20
Reviewer: independent input-complexity analyst for issue #53
Status: `READY_FOR_INTEGRATION` after a note-only derivation

## Scope and evidence

This note gives one deliberately loose, complete resource bound for a
reference implementation of the qualitative C081 decision. It charges the
original finite syntax, normalization, the finite summary tables, the C029
infinite-continuation search, the terminal witness enumeration, arithmetic for
the reviewed `Fhat`, and peak storage. It is an ordinary mathematical
accounting result, not a new Lean theorem or a claim about the current native
runtime.

The current main documentation checkpoint is
[`29cda9a`](https://github.com/mhenglein/subtail/commit/29cda9a89f56a3f0a2fffb5001b773f3c08a21fb).
I read the exact definitions in `ExpressionNormalization.lean`,
`StackSummary.lean`, `SummaryAutomaton.lean`, `CanonicalReachability.lean`,
`InfiniteDecision.lean`, `FiniteSearch.lean`, and `RankQueryDecision.lean`.
The source hashes read back from this checkout are:

```text
ExpressionNormalization.lean  6e69fa21ebf0a0ffa65f78c976eb6681a85e9c9778cf96e57d16fb86b1285b82
StackSummary.lean             345b4b1719f31b3963ca5ccc50b2fc861fc19864fe891cd9fcd547121acbe1fc
SummaryAutomaton.lean         68832af44bc8907e99dd2889968c699245aff70d40bf5690539f3f9edd8ca37b
CanonicalReachability.lean    6400b93753493a13b9a4cc1cb391e3ca5ad8b7b45623824877e2ad1d78e72403
InfiniteDecision.lean         d9679db4b52062a707f74c4a7198137f608660930e3f4a2d868ab4efac40228d
FiniteSearch.lean             10583fb950420ccfb3ae88c906a0e3f004d72fcb8a3aac53a24b4281800a4057
RankQueryDecision.lean        51fef747bb443d313559e57d8fb8e3c1ce68b804eb4883a7d504e2945da5bd8a
```

The quantitative terminal endpoint is the independently reviewed PR #48
proof source [`0b5d9de`](https://github.com/mhenglein/subtail/commit/0b5d9de57a36591f3fd7cb38940afde3c7f9500b),
especially `RankQueryLengthBound.terminal_witness_bound_iff`, with the
corrected `Uhat`/`Fhat` recurrence described in the C080 readback
[`2026-09-20-c080-quantitative-independent-readback.md`](2026-09-20-c080-quantitative-independent-readback.md).
That branch is not part of current main. I use its endpoint as an explicit
mathematical dependency and keep its repository integration and fresh combined
validation pending.

I did not run a Lean build, materialize the large tables, enumerate the C029
carrier, or benchmark this derivation. The earlier conditional backend
accounting in [`2026-09-20-post-c081-cost-readback.md`](2026-09-20-post-c081-cost-readback.md)
is used only after its stated source-level repairs.

## Original input encoding

The typed Lean input is a natural number `n`, a list `G` of expression pairs,
and two expressions `s,t : Expr n`. For a bit-level reference format, encode
`n` in unsigned binary, then encode the list delimiters and each expression as
tagged abstract-syntax-tree nodes:

```text
var(i)       -- the binary index i, checked against i < n
bot
prod(e1,e2)
```

The encoding also contains the length or delimiters for `G` and the two query
expressions. Let `B` be its total bit length, including tags and delimiters.
Malformed encodings are rejected after parsing; the bound below concerns the
well-formed typed input. Parsing costs at most `8B^2` unit steps and stores at
most `2B` cells.

For an expression `e`, let `|e|` be its number of AST nodes, and set

```text
L = |s| + |t| + sum_{(u,v) in G} (|u| + |v|),
g = |G|,
D = 1 + n + g + L.
```

The reference algorithm deliberately does **not** silently discard unused
variables. `ExpressionNormalization.naming` retains all `n` old variables,
so the cost of a large encoded `n` is visible. Since every constructor, list
delimiter, and expression occurrence uses input bits, `L+g <= B` up to the
fixed tag convention. Since `n < 2^B`,

```text
D <= 1 + 2^B + 2B <= 2^(B+2) =: D_B       (B >= 1).
```

This is the explicit encoded-`n` overhead. If a future front end first densely
renames only variables occurring in the syntax, its support table has at most
`L` entries and the semantic reindexing proof can replace `n` by that support
size. That optimization is not used here, because the raw source definitions
already give the exact checked object and do not need a new renaming theorem.

## Reference algorithm and its correctness contract

The reference algorithm uses dense finite tables for values of all finite
functions. A table entry is the same value returned by the corresponding Lean
definition; the table is an extensional representation, not a change of
semantics.

1. Parse `(n,G,s,t)` and compute `R = naming G s t` and
   `C = normalized G s t`. Let `a = R.ref s` and `b = R.ref t`.
2. Construct `I = summaryInstance C a b`. First tabulate `systemOf C`, the
   balanced relation used by `StackSummary.balancedCheck`, the subset-pair
   state list `states k`, and every transition, bad bit, final bit, and flag
   bit of `I`, where `k = R.total`.
3. Run the existing `InfiniteDecision.infiniteWitnessCheck I`. If it returns
   true, report non-entailment.
4. Construct `J = AbsorbingTerminal.terminalize I`. Let `q` be its state count
   (here `q = I`'s state count). Compute the reviewed terminal bound
   `Fhat(q)`. Enumerate every binary word of length at most `Fhat(q)` and run
   the existing `witnessCheck J` on each word. Report non-entailment exactly
   when one succeeds; otherwise report entailment.
5. Return the negation of the two witness branches, as in
   `EntailmentDecision.rawNormalizedEntailsCheck`, with the separately proved
   cheap cases optionally placed before this complete fallback.

The table construction computes the same finite objects as the checked source:
`systemOf` is tabulated by its four constraint scans; `states` uses the exact
`StackSummary.subsets` order and the Cartesian pair construction; `encode` and
`decode` use the same state list; `advancePair`, `advance`, and every field of
`summaryInstance` are evaluated extensionally. Structural induction over a
word proves that table lookup agrees with the source function. The same
argument applies to `terminalize`; its transition and final tables are the
source definitions `terminalStep` and `terminalFinal` evaluated on the already
tabulated instance.

For correctness, `ExpressionNormalization.normalize_entails_iff` transfers
the original expression problem to `C`. The summary bridge gives
`not_entails_iff_witness`; `summary_absorbing` supplies the absorption premise
for `InfiniteDecision.infiniteWitnessCheck_correct`. The checked split
`SubtypeTerminalBridge.not_entails_iff_infinite_or_terminal` leaves the
terminal branch on `J`. `AbsorbingTerminal.terminalize_terminal` supplies
`TerminalFinals J`. The reviewed PR #48 theorem then gives the bounded
terminal witness equivalence, and `Basic.witnessCheck_correct` turns each
finite enumeration result into the exact `Witness` predicate. Therefore the
reference algorithm has the same Boolean answer as the checked qualitative
composition, assuming the reviewed endpoint is integrated with this wrapper.

The last implication is a proposed composition proof. Current main has the
qualitative `terminalWitnessCheck`; it does not yet contain this bounded
enumerator or a combined theorem using `terminal_witness_bound_iff`.

## Cost model

The primary count is a list-and-table cell model:

* a list spine cell, Boolean, finite-index value, option tag, pair, and natural
  unit operation costs one unit;
* a vector of length `r` is stored as `r` cells, and a reference list lookup
  costs at most `r+1`; the formulas below therefore remain safe if the
  evaluator uses lists instead of constant-time arrays;
* a binary word of length `ell` occupies at most `ell+1` cells;
* structural equality of an expression or table entry is charged by the
  number of fields it inspects;
* natural exponentiation is charged by its source recursion. If the displayed
  unit operations use binary arithmetic, each arithmetic operation on a
  `b`-bit natural costs at most `1+b^2` bit operations. The maximum bit length
  `b_*` of all live naturals is defined explicitly below, so no giant exponent
  is hidden in a unit-cost symbol.

All bounds use generous constants. They are intended to make every loop and
carrier visible, not to estimate practical performance.

## Normalization cost

`Expr.pairs` visits every product node and `forest` contains the two query
roots plus both sides of every premise. Thus, with `p` the length of
`R.pairs`,

```text
p <= L,
botUsed <= 1,
k = R.total = n + p + botUsed <= D,
|C| = g + 2p + botUsed <= 3D.
```

The equality `|C| = g + 2p + botUsed` is the checked
`ExpressionNormalizationAudit.normalized_length` statement. It includes both
upper and lower definitions for every product occurrence, including duplicate
occurrences.

Use a direct recursive AST traversal. A structural expression comparison costs
at most `L+1` cells. Building all occurrence lists, including the list
appends in the source `pairs` definition, costs at most `8(L+1)^2` steps.
There are at most `8D+4` references in the definitions and premise clauses.
Each `Naming.ref` lookup scans at most `p` pairs and compares two stored
subexpressions, so all lookups cost at most `16(D+1)^3` steps. Constructing
the definition and premise lists, `Fin` indices, and the input parse is then
covered by

```text
C_norm(D,B) = 8B^2 + 64(D+1)^4,
S_norm(D,B) = 2B + 32(D+1)^2.
```

The space term stores the input AST, the occurrence table, the naming table,
and the normalized list. It intentionally allows a quadratic amount for
materialized subexpression references. A pointer-sharing implementation is
smaller but is not needed for this upper bound.

## Exact summary construction

Let `k = R.total`, `m = |C|`, and define

```text
Q0(k) = 2^(k^2).
```

`StackSummary.pairs k` has `k^2` entries and
`subsets (pairs k)` has exactly `Q0(k)` candidate relation tables. A candidate
relation has at most `k^2` pairs. The four closure checks in
`StackSummary.closedCheck` inspect at most `k^4` tuples and list-membership
tests of length at most `k^2`; the five conjuncts and list construction are
covered by `32(k+1)^6` steps. Therefore one complete `balancedCheck` costs at
most

```text
B_bal(k) = 64(k+1)^6 Q0(k)
```

and its temporary relation lists occupy at most

```text
S_bal(k) = 8(k^2+1) Q0(k)
```

cells. This explicitly charges the powerset enumeration; it does not replace
the checked least-closure definition by an assumed polynomial saturation.

For later uses of `popCheck`, define the safe recurrence envelope

```text
P(k,ell) = (k^2+1)^(ell+1) (B_bal(k)+1).
```

The source recursion branches over at most `k^2` intermediate controls per
input letter and calls `balancedCheck` at the empty word, so induction on
`ell` gives `popCheck` cost at most `P(k,ell)`. The initial summary uses only
`ell=0`; `dangerCheck` and `satCheck` also use empty words.

For a subset `S` of controls, `SummaryAutomaton.nextSet` scans at most `k`
targets, `k` source members, and `k` intermediate controls, calling one
`balancedCheck` per triple. Set

```text
C_next(k) = 16(k+1)^3 (B_bal(k)+1).
```

The control-path test used by `dangerCheck` and `safeCheck` enumerates the
`2^k` subsets of `Fin k`. One invariant check scans at most `k^2` control
pairs; each `controlEdge` uses one balanced lookup and two table lookups. A
safe envelope is

```text
C_path(k) = 8(k+1)^3 2^k (B_bal(k)+1),
C_danger(k,m) = 8(k+1)(m + C_path(k)).
```

`forcedList` scans `k` controls and `k^2` possible lower-constraint endpoints.
`safeCheck` then tests at most `k` forced seeds for each denied control, and
`controlReachCheck` scans at most `k` intermediate controls. Thus the complete
scalar satisfiability test has the explicit envelope

```text
C_sat(k,m) = 16(k+1)^4 (m + B_bal(k) + C_path(k) + 1).
```

This includes the forced-list construction, all `controlReachCheck` calls, the
empty-word `popCheck`, and the denial membership scans.

The exact summary state list has

```text
q = |states k| = 4^k
```

states, each containing two subsets of at most `k` controls. Let

```text
C_states(k) = 16(k+1) q,
C_system(k,m) = 16(k+1)^3(m+1),
C_encode(k,q) = 16(k+1) q.
```

`C_system` tabulates all epsilon, push, and pop entries by scanning the
normalized constraint list. `C_encode` covers a worst-case scan of the state
list when an `encode` operation locates a newly computed pair.

The exact source definition of `summaryInstance` has the following remaining
loops:

* its initial state uses two empty-word `popSet` calls, at most `2kB_bal(k)`;
  include this in `C_initial(k,q) = 16(k+1)(q+B_bal(k))`;
* each of the `q` bad bits may recompute `satCheck`, scan a list lookup for
  its decoded state, and scan up to `k` controls with `dangerCheck`, giving
  `C_bad(k,m,q) = q*(C_sat(k,m) + q + k*(m+C_danger(k,m)))`;
* each final bit scans a decoded-state lookup and, for each of at most `k`
  controls, searches `k^2` possible lower-constraint endpoints and the `m`
  constraint list, giving
  `C_final(k,m,q) = q*(q + k^3*(m+1))`;
* each ordered flag entry scans two decoded-state lookups and at most `k^2`
  subset-membership pairs, giving
  `C_flags(k,q) = 8q^2(q+k+1)^2`;
* two letters and two summary components require four `nextSet` calls per
  state, plus state-list encoding, giving
  `C_trans(k,q) = 4q*(C_next(k)+2*C_encode(k,q))`.

The complete finite-summary construction is therefore bounded by the explicit
sum

```text
C_summary(k,m) = C_states(k) + C_system(k,m) + C_initial(k,q)
  + C_bad(k,m,q) + C_final(k,m,q) + C_flags(k,q) + C_trans(k,q),
```

where `q=4^k` and every term on the right is displayed above. This charges
the dense transition table, bad/final vectors, the `q` by `q` flag matrix,
the exact state carrier, all balanced powersets, and the scalar satisfiability
and danger tests. No lazy function or unresolved "summary construction cost"
remains in this reference model.

For peak cells, use

```text
I_cells(q) = 2q^2 + 9q + 1,
S_summary(k,m) = 4*I_cells(q) + 16(k+1)q + S_bal(k) + 8(m+k^2+1).
```

The first term stores the summary instance, including the dense flag matrix;
the second stores the state list and its list spines; the third covers a live
balanced relation enumeration; the last retains the normalized constraints
and system table. This is a peak-safe sum rather than an attempt to exploit
garbage collection.

## Terminalization and the reviewed terminal bound

`AbsorbingTerminal.terminalize` scans every state and both letters, tests
`safeState`, and builds a new transition and final table while retaining bad
and flag fields. In the same cell model,

```text
C_terminalize(q) = 32(q+1)^2,
S_terminalize(q) = 2*I_cells(q).
```

The reviewed endpoint defines

```text
T_0 = q + 10,
T_(j+1) = 64*q*T_j^(6*T_j^2+2),
G_0 = 1,
G_(h+1) = (T_(h+1)+2)*G_h,

Fhat(1) = 0,
Fhat(q) = 2*(q+1)*G_(q-2)       (q >= 2).
```

This is the `Uhat`/`Fhat` replacement from PR #48; it is not the original
C080 `64*q*T^(2T+2)` recurrence. Let `r=max(q-2,0)` and
`e_j=6*T_j^2+2`. The literal recursive source recomputes lower budgets inside
each `growth` call, so a safe arithmetic charge is

```text
C_F(q) = 32(q+1)^2 + sum_{j=0,...,r-1} (r-j)*(4*e_j + 32).
```

The first term covers base cases, `Nat` comparisons, and products; the sum
charges every recursively rebuilt `T_j`, its exponentiation, and the growth
products. Memoization can reduce this cost but is not assumed.

Let

```text
W_F(q) = 2^(Fhat(q)+1)-1.
```

The reference terminal checker materializes `boundedLists bools Fhat(q)` and
calls `witnessCheck` on each word. Charging all `take`, `drop`, prefix,
`runFrom`, state, and flag loops gives the conservative conditional envelope

```text
C_terminal_search(q) = C_F(q)
  + 64(q+1)^2 (Fhat(q)+1)^5 2^(Fhat(q)+1),

S_terminal_search(q) = 2*I_cells(q) + 4(q+1)
  + 8(Fhat(q)+2) 2^(Fhat(q)+1).
```

The second line stores the terminal instance, bound-computation stack, all
materialized candidate words, and list spines. It deliberately charges the
whole list rather than treating enumeration as a constant-space iterator.

The mathematical QB step is exact at the reviewed theorem statement:
`RankQueryLengthBound.terminal_witness_bound_iff` says, for every
`TerminalFinals J`,

```text
(exists w, Witness J w)
  iff (exists w, Witness J w and length(w) <= Fhat(q)).
```

`boundedLists` contains every binary word of length at most `Fhat(q)`, and
`witnessCheck_correct` recognizes `Witness J w`. Consequently the bounded
enumerator has the same terminal answer as `terminalWitnessCheck` whenever
the reviewed theorem is available. This discharges the mathematical QB
obligation without assuming the old `ClosureFor`, the old `U/F`, or a caller
supplied witness bound. The repository still lacks the wrapper and a fresh
combined Lean/kernel validation, so QB is an integrated dependency still
pending in main.

## Existing C029 infinite-continuation cost

For the `q`-state summary instance, use the repaired source-level envelope
from the independent C029 accounting review. Define

```text
W_q = 2^(q+1)-1,
A_q = q*W_q,
H_q = 2*q^2*2^(q^2),
S_succ(q) = 64(q+1)^4,
E_state(q) = 8(q+1)^3,
```

where `A_q` is the exact upper bound for state/period candidates and `H_q` is
the monitor carrier bound for periods of length at most `q`. The actual
`FiniteSearch.saturate` loops are charged by

```text
C_BFS(q) = H_q^2*(S_succ(q)+1)
  + 2*q*H_q^3*(E_state(q)+1)
  + H_q^2*(E_state(q)+1) + H_q.
```

Candidate construction, cycle checking, capacity arithmetic, and word-list
cells are charged by

```text
C_cycle(q) = 64(q+1)^4,
C_cap(q) = 16(q+1),
C_words(q) = 8(q+1)^2 W_q.
```

Thus the complete C029 time envelope is

```text
C_infinite(q) = C_words(q)
  + A_q*(C_cycle(q) + C_cap(q) + C_BFS(q) + 8(q+1)).
```

The corresponding peak storage, including monitor-state payloads rather than
only their cardinality, is

```text
State_cells(q) = 4 + 2*q*(q+1),
S_infinite(q) = 2*I_cells(q) + 2*A_q + 8(q+2)W_q
  + (2*q*H_q + H_q + 1)*State_cells(q) + 4*q*H_q.
```

The `allStates` list used in the correctness theorem is not evaluated by
`reachesAnyWithFuel`; the carrier bound is computed arithmetically. The
formula nevertheless charges the runtime saturation, successor lists,
duplicate suppression, state equality, candidate list, and capacity powers.

## Complete input-to-resource bound

For a well-formed input of bit length `B`, set

```text
D = D_B = 2^(B+2),
k = D,
m = 3D,
q = 4^k.
```

These are safe substitutions for the actual `n`, normalized variable count,
and normalized clause count. The reference algorithm's total cell-step bound
is the explicit function

```text
T_cells(B) = C_norm(D,B) + C_summary(k,m)
  + C_terminalize(q) + C_infinite(q) + C_terminal_search(q).
```

Its peak cell storage is bounded by

```text
S_cells(B) = S_norm(D,B) + S_summary(k,m)
  + S_infinite(q) + S_terminalize(q) + S_terminal_search(q).
```

The sums are intentionally additive across phases, so they remain valid for
an implementation that retains old tables longer than necessary. They also
make every setup cost visible: parsing, occurrence lookup, dense constraint
tables, the `4^k` summary carrier, the `2^(k^2)` balanced-table powerset, the
`q^2` flag matrix, terminalization, `Fhat` arithmetic, C029 monitor search,
and all bounded witness words are included. `T_cells` is total recursive and
finite for every `B`; no timeout or unproved cutoff supplies an answer.

For binary arithmetic, define the explicit maximum live numeral width

```text
b_*(B) = 1 + max(
  B, D, k, q, W_q, Q0(k), Fhat(q), W_F(q),
  max_{0 <= j <= q-2} T_j, H_q, 2^(q^2)
)
```

where the maximum over an empty index range is zero. This is a value bound;
the corresponding bit length is `ell_*(B)=ceil(log2(b_*(B)+1))`. A fully
binary implementation therefore satisfies the conservative bounds

```text
T_bits(B) <= (1 + ell_*(B)^2) * T_cells(B),
S_bits(B) <= (1 + ell_*(B)) * S_cells(B).
```

The displayed `C_F`, `C_cap`, and `C_summary` terms already count recursive
exponentiation steps; the multiplier charges their actual binary arithmetic
cost. The candidate-word and table terms count physical cells, so the huge
`Fhat` and `q` effects remain explicit rather than disappearing into a unit
cost for a natural number.

This bound is deliberately far larger than the syntax size. It is a complete
resource upper bound for the stated reference algorithm under the reviewed
terminal theorem, not a polynomial, elementary, or practical complexity
classification.

## Status, assumptions, and next check

Discharged by this derivation:

* the original input representation and encoded-`n` overhead are explicit;
* normalization, product-occurrence naming, and normalized-list size are
  charged;
* the exact finite summary carrier, balanced closure powerset, dense tables,
  transition construction, bad/final/flag matrices, and temporary tables are
  charged;
* C029 candidate generation, monitor capacity, saturation, state payloads,
  and peak storage are charged;
* terminalization, `Fhat` computation, bounded word enumeration, witness
  checks, arithmetic width, and peak storage are charged;
* the reviewed `terminal_witness_bound_iff` discharges the mathematical QB
  needed to replace the promoted terminal query by finite witness enumeration.

Still pending:

* PR #48's corrected quantitative modules are not merged into current main;
* the bounded terminal wrapper and the combined C081 theorem are not Lean
  declarations;
* fresh combined build, kernel replay, and resource benchmark are not run;
* no exact lower bound is established or transferred here;
* the bottom-free NP99 upper-bound transfer is a separate restricted result and
  does not turn this deliberately loose envelope into a complexity class for
  full C081;
* dense variable renaming could improve the encoded-`n` term, but its semantic
  reindexing theorem is outside this note.

The correct next validation is a small, isolated reference wrapper that first
checks `terminal_witness_bound_iff` on a few tiny terminal instances, then
compares its Boolean with `terminalWitnessCheck` and the existing
`entailsCheck` on the same normalized inputs. That validation should preserve
timeouts as `UNKNOWN` and must not promote the resource formulas to a Lean
complexity theorem until the combined source and runtime audit passes.

All Lean, source, workflow, ledger, parent-note, and main files remained
read-only for this task. Only this new note is owned.
