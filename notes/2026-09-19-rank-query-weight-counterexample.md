# C080 quantitative review: the concrete Lean compiler exceeds the proposed U bound

> **September 20 integration note.** Historical discovery and ordinary replacement proof. The counterexample and
> corrected larger bound are now Lean-checked as C082; see [the quantitative
> integration and dependency audit](2026-09-20-post-c081-quantitative-integration.md).
> The original F alone and a smaller existential compiler remain unresolved.
> The pending-review statements below retain their original checkpoint scope.

Date: 2026-09-19. Workstreams: A017/A018; quantitative issue #30, proof tracker #34, coordination #37.
Reviewer/session: ChatGPT `rank-weight-publication-20260919`, publishing the completed independent advisory investigation at the repository owner's request.

**Result: a hypothesis-preserving counterexample to the old clause-weight bound for the current concrete Lean preimage, plus a conservative sufficient replacement with an ordinary counting proof. NOT a new Lean-checked theorem.** The qualitative terminal decision is unaffected. Separate mathematical review and native Lean verification of this new finding remain outstanding.

## 1. Provenance, exact target and scope

Mathematical inspection was pinned to `064fc7306b679bf607b91e7d8de259823f200c62` (2026-09-19 13:22:38 UTC, "Record checked subtype bridge and remaining infinite branch (#31, #37)"). Publication is based on `e1e8f635f0374d5c8112c8ee25c4220fc10198be`, tree `127c7fb006adb38e0075d32f91aa42ed605085b1`. GitHub comparison showed that the intervening changes are confined to `notes/prior-work/**`; the mathematical sources and compiler record used here are unchanged.

Read: C080 in [claims](../research/claims.md#c080), the [rank-query route](2026-09-15-rank-query-route.md), [candidate record](../research/RANK_QUERY_CANDIDATE.md), [compiler record](../research/RANK_QUERY_COMPILER.md), [written closure and quantitative proof](2026-09-17-rank-query-closure-audit.md), current query/compiler/enumeration/coverage sources, their readbacks, conditional unwind, and the [terminal-decision source](../lean/Subtail/RankQueryDecision.lean). This was source inspection, not a fresh replay of the repository's Lean proofs.

Key inspected Git blob identities (unchanged at publication base):

| Path under `lean/Subtail/` | Git blob SHA |
|---|---|
| `Basic.lean` | `953f04e48ea6d3b737ac93471f2d3d6e42163ae5` |
| `RankQuery.lean` | `6ee81d85c058a8f17342e4c341f8227e3a963731` |
| `RankQueryCompiler.lean` | `32e034ba4e6dac48f639b3ca688b0ec561c6baaa` |
| `RankQueryEnumeration.lean` | `a4e6349919c0cca9670dce7465ba2105bbcdde7f` |
| `RankQueryCoverage.lean` | `347ca0806a0d9f0822dc308a198b8be97a97dbbc` |
| `RankQueryDecision.lean` | `8889fb4b0ac25b316797f8f9453de23e5d0d84e2` |
| `RankQueryUnwind.lean` | `e4e605b1c19197e2af6cb7084d642c973ff385f1` |

The exact compiler is `RankQueryEnumeration.preimage I RankQueryCoverage.budget`. The relevant obligation is the SECOND conjunct of `RankQuery.ClosureFor I pre`:

```lean
forall phi : Query k, forall c in pre phi,
  clauseWeight c <= closureBound k (weight phi)
```

The displayed ASCII pseudocode spells the existing quantifiers; it is not a replacement declaration. In the source the first conjunct separately gives, for every safe reference B, semantic equivalence between `Sat (prefixGraph I B) (pre phi)` and the existence of a safe first-return extension satisfying phi.

The weight conjunct has NO satisfaction or safe-reference premise. It bounds every emitted clause, including redundant or unsatisfiable ones. This review nevertheless supplies a satisfiable counterexample with a safe base and safe extension, and a terminal original automaton.

No Lean definition, proof interface, implementation, toolchain, workflow or shared checkout is changed. In particular, do not make `terminalWitnessCheck_correct` depend on this quantitative work. Its source proves correctness under `TerminalFinals I` without U, F or a clause-weight premise.

## 2. What is counted

In `RankQuery.lean`:

```text
sumSizes c    = sum of a.observer.size over atom OCCURRENCES a in c.atoms
clauseWeight c = max(2, 1 + c.vars + c.atoms.length + sumSizes c)
weight phi     = maximum clauseWeight in phi (0 for the empty query)
closureBound k T = 64*k*T^(2*T+2)
```

Let v be the declared variable count, a the number of atom occurrences, s_i the declared observer size for occurrence i, and S=sum_i s_i. Thus T=max(2,1+v+a+S).

Repeated atom occurrences count separately. Unused declared variables count. Unary-test/equality/disequality list lengths, transition-table lengths, nested captured observer descriptions, and the number of query disjuncts do not count. This is not a runtime, memory, bit-length, or fully tabulated representation bound.

For a diagram with n groups and n_c core variables, `compileValid` declares exactly 2+n+n_c variables. It emits two mandatory two-state base atoms; the atoms emitted by each piece; and one interval atom per consecutive pair of groups. `compilePiece` behaves as follows:

| Piece | Counted contribution |
|---|---|
| core | One path atom of unchanged observer size s_i; slicing and recolouring change no state count |
| positive forward | One active observer occurrence in every physical interval crossed |
| zero-length forward | Unary test only; no active coordinate |
| enter or wrap | Unary tests/equalities only |
| F exit | Unary test/equality only |
| mismatch K exit | One two-state edge atom; the captured portal observer does not enlarge its declared `size` |

`itemsAt` retains active occurrences as a list, without deduplication. For b active occurrences in one interval, the exact declared state count is

```text
6*k*product_{j=1..b}(s_j).
```

There is ONE generator state (factor k), ONE next-marker choice (factor 3), and ONE positive-length bit (factor 2) per physical interval. Every repeated traversal contributes a distinct observer coordinate. This preserves a common generated word; it is not a product of independent word-existence claims. Even with no active observations, the interval size is 6k, using the empty product 1.

## 3. Enumeration choices and the actual budget

`RankQueryCoverage` defines its own indexed `sumSizes`, extensionally the same sum S over atom occurrences. Its current budget is:

```text
B = blockBound  = 3*a + 2*S
G = groupBound  = 2 + v + 2*a + 2*S
H = coreBound   = v + 2*a*B
P = perAtom     = 2*B
E = seamEntries = B*G
d = scalar     = H + G + 2*B + a + S + 1.
```

`RankQueryEnumeration.Bounded` permits 1<=n<=G groups, 0<=n_c<=H core variables, one piece list per input atom of length at most P, and at most E seam entries. Each scalar field of a piece and each seam coordinate is strictly below d. It does not require product-simple paths or a per-observer excursion bound.

At fixed n,n_c, the raw finite choices are:

- (n+n_c)^v variable-location lists;
- k^n original-state lists and 3^n next-marker lists;
- two first bits and 12*k*2^k full old-end colours;
- a lists of pieces from an alphabet of size 20*d^4 (five kinds, four labels, four scalar fields), each list of length at most P;
- one seam list from an alphabet of size d^4, of length at most E.

Equivalently the raw diagram count is

```text
sum_{n=1..G} sum_{n_c=0..H}
 (n+n_c)^v * k^n * 3^n * 2 * (12*k*2^k)
 * (sum_{l=0..P}(20*d^4)^l)^a
 * (sum_{l=0..E}(d^4)^l).
```

The usual empty-list and zero-exponent conventions apply. Validation filters the raw alternatives afterwards. It forces the last next marker to END, earlier markers to bits, and the old-end flags to their required values, among other guards. Redundant labels, unused seam entries, repeated list entries and alternative presentations can survive the envelope. These increase enumeration work or the number of disjuncts, not the weight of a single clause, except where retained piece occurrences or declared variables directly enter that clause.

`mem_diagrams` and `mem_preimageClause` identify membership exactly with `Bounded` and successful `compileDiagram`. It is therefore sufficient to exhibit one bounded, valid oversized diagram; enumerating the huge union is unnecessary.

## 4. The failed implication

The written proof first selects product-simple paths. Atom i then has at most s_i+1 fresh excursions, giving a small total number of observer coordinates per interval (the written 2T envelope). This is an EXISTENTIAL normal form: some such diagram witnesses any positive extension.

The current Lean enumeration grants the GLOBAL allowance P=2*(3a+2S) independently to EVERY atom and accepts valid diagrams with repeated excursions. `validDiagram` checks local consistency, not that the piece sequence came from a product-simple path. The compiler preserves the resulting coordinate multiplicity.

Consequently, existence of a small normal-form diagram does not bound EVERY diagram emitted by the oversized enumeration. The 2T coordinate estimate cannot be used for this concrete `preimage`.

The Python `path_shapes` enumeration is different: it controls excursion recursion with the INDIVIDUAL observer size. The [Lean coverage readback](2026-09-19-lean-rank-coverage.md) explicitly says its budget need not match Python's. The example below belongs to Lean's enumeration; no claim is made that it belongs to Python's `iter_diagrams`. Python's `Query.weight` also omits Lean's `max 2` floor, relevant for degenerate clauses.

This is a representation/enumeration failure, not a counterexample to semantic reconstruction, terminal decidability, or the existence of another preimage satisfying the original `ClosureStatement`.

## 5. Hypothesis-preserving counterexample

### 5.1 Original terminal instance and safe references

Use five states 0..4, initial 4, final set {0}, no Bad states and no flags. The ONLY transitions are:

```text
4 --1--> 3 --0--> 2 --1--> 1 --0--> 0.
```

All other transitions are undefined, so accepting state 0 is terminal. The original word 1010 is a witness.

Take reversed references B=01 with labels (0,1,2), and C=0101 with labels (0,1,2,3,4). Each reverse-run equation holds. Safety, diagonal and border-mask checks hold because Bad and flags are empty. B need not end at the original initial state. C extends B and its labels; the first later occurrence of B ends at position 4, not 3. Thus B is safe and C is a safe first-return extension under the exact source definitions.

### 5.2 Clause

Let O have two controls 0,1, initial and final sets both {0}, all colours allowed, and all four control-to-control transitions for each of F,S,K0,K1. Both controls are usable.

Take one variable x, no tests/equalities/disequalities, and FIVE OCCURRENCES of `Path_O(x,x)`. Duplicate atoms are permitted by the grammar. Hence

```text
v=1, a=5, S=10, T=17.
```

### 5.3 Diagram and premise checklist

```text
groups   = 2
coreVars = 0
loc      = [fresh 0]
states   = [3,4]
nextBits = [some 1, END]
firstBit = 0
oldEnd   = (state=2, mask=all false, next=END, root=false, isEnd=true)
seams    = [].
```

Let P be a forward piece from fresh group 0 to fresh group 1, with controls 0 to 0. Let R be a wrap from fresh group 1 to fresh group 0, labelled K0, again controls 0 to 0. For each input atom choose the piece list `(P R)^35`, length 70.

The exact budget is B=35, G=33, H=351, P=70, E=1155, d=470. All Bounded premises hold: the positive group count and both size caps; variable, state, next and piece-list lengths; valid locations; each piece-list length; scalar values only 0 or 1; and an empty seam list.

All `validDiagram` premises hold: the correct next-marker/old-end shape; safe first emission delta(3,0)=2; no Bad or diagonal flag; empty test/pair obligations; and a valid path for every atom. Each atom starts and ends at fresh group 0 in an initial/final control; adjacent piece locations and controls agree. Each forward crosses exactly one interval, so no internal seam is needed. Each wrap uses the last group, first group and required K(firstBit) label. No product-simplicity guard exists.

By exact enumeration membership, compiling this D emits a clause c' in `preimage I budget [c]`.

### 5.4 Exact weight and strict violation

There is one physical interval and 5*35=175 active observer coordinates, each of size 2. The wraps emit 175 unary predicates, not atoms. Thus the output has four variables, three path atoms, and observer-size sum 2+2+30*2^175:

```text
clauseWeight c' = 12 + 30*2^175
               = 1436714569561770804710950337953414859642567927047127052
U_5(17)        = 320*17^36
               = 63286510177916475148846592658733814121868185920.
```

The exact symbolic comparison is immediate from 17^2<2^9:

```text
64*k*17^36 < k*2^168 < 6*k*2^175 < 12+6*k*2^175.
```

No logarithm approximation, finite-corpus extrapolation or huge state materialization is needed.

### 5.5 This emitted clause is satisfiable

On P(B), assign END=2, INITIAL=0, z_0=1, z_1=2. The base edges are `2 --F--> 0 --K0--> 1`; the shared interval is the SINGLE step `1 --K1--> 2`. Its original reverse state changes from 3 to 4, satisfying delta(4,1)=3. The positive-length bit changes from 0 to 1; all 175 observer coordinates stay at 0 and accept simultaneously.

The corresponding fresh edges on P(C) are `3 --S--> 4 --K0--> 3`. Every repeated forward/wrap pair is realized on this SAME extension C. The model meets the origin End/non-End checks, old-end equality, masks, colours, and wrap predicates.

The counterexample is not an artifact of impossible colours, absent finals, nonterminal acceptance, zero-state observers, undefined transitions being accepted, independent interval words or an unsatisfiable emitted branch. Its redundancy is legal syntax which the actual weight contract universally quantifies over.

## 6. Conservative replacement for the UNCHANGED compiler

Define, without changing any source declaration,

```text
Uhat_k(T) = 64*k*T^(6*T^2+2).
```

**Ordinary counting theorem.** For an Instance I, clause c and diagram D, if `Bounded c (budget c) D` and `validDiagram I c D = true`, then

```text
clauseWeight (compileValid I c D) <= Uhat_k(clauseWeight c).
```

### Proof

Put T=clauseWeight c. An Instance contains an initial Fin k, so k>=1. We have T>=2 and v+a+S<=T-1.

Let M=2a(3a+2S), the total piece-occurrence upper bound, since each of a atom lists has length at most 2(3a+2S). Then M<=6T^2. Also G=2+v+2a+2S<=2T and H=v+M.

Variables: `vars'=2+n+n_c <= 2+2T+T+6T^2 <= 8T^2` for T>=2. This counts unused declarations as required.

Path atoms: each piece emits at most one non-interval atom. Adding the two mandatory atoms and n-1 intervals gives `a'<=2+M+n-1<=1+6T^2+2T<=8T^2`.

Non-interval observer states: core/slice observers retain size at most T; mismatch-edge observers have size 2<=T. The mandatory two atoms contribute four states. Thus `S_noninterval<=4+MT<=4+6T^3`.

Interval states: for a fixed interval, `forwardActive` emits at most one observation from each piece occurrence (its range visits each crossed interval once). There are at most M occurrences, and every contributed observer has size at most T. Hence each interval has at most `6*k*T^M<=6*k*T^(6*T^2)` states. There are at most 2T intervals, so `S_interval<=12*k*T^(6*T^2+1)`.

Combining, the raw sum defining clause weight is at most

```text
5+16T^2+6T^3+12kT^(6T^2+1)
 <= 15T^3+12kT^(6T^2+1)
 <= 27kT^(6T^2+1)
 <= 64kT^(6T^2+2).
```

The right side is also >=2, covering the max floor. The first inequality holds for T>=2 (16T^2<=8T^3 and 5<=T^3); the next uses k>=1 and 6T^2+1>=3. This proves the claim.

For a full query, each input clause weight is at most `weight phi`, and Uhat is monotone there. Exact preimage membership therefore gives the corrected bound for EVERY emitted clause, not just a chosen satisfiable subfamily. No number-of-disjuncts factor occurs.

### Edge cases and what the theorem is not

Empty query: the concrete preimage is empty, so the bound is vacuous. One-group diagram: no interval atoms. No active observations: product=1, interval size=6k. Zero-length forward pieces: tests only. A zero-state input observer cannot satisfy `atomValid`, hence no valid diagram for that clause. Atom-free clauses and unused variables are included in the estimates. k=0 admits no Instance because it has no initial Fin 0.

Arbitrarily long test/equality lists and transition tables are not bounded by T. Therefore Uhat, like the original U, is not a fully expanded storage or time bound. Shared generator correctness is not traded away: coordinates are counted with multiplicity, and a generator is counted once per physical interval.

The constant and exponent are deliberately loose. This theorem does not claim the optimal growth rate or repair the old fixed `ClosureFor` declaration in Lean.

## 7. Implications for the witness-length recurrence

### What is invalidated

`RankQueryUnwind.weight_promote_finish_le` is a valid CONDITIONAL theorem taking the original `ClosureFor` as a premise. That premise cannot hold for this concrete oversized enumeration. Thus the old recurrence cannot be obtained by that particular instantiation.

This is NOT a counterexample to the old numerical F(k) witness statement itself: the counterexample instance has a length-four witness. Nor is it a refutation of `ClosureStatement`, which existentially permits a different preimage. A smaller covered enumeration could still satisfy the old U contract.

### Corrected query-weight recurrence

For the unchanged compiler, set

```text
That_0 = k+10
That_(j+1) = Uhat_k(That_j).
```

Finishing clauses have weight k+8, below the initial budget. Uhat is monotone and dominates T for k>=1,T>=2, and union takes the maximum clause weight. Induction therefore bounds all clauses after j promotions by That_j. This is an ordinary consequence of Section 6; no conditional Lean theorem is silently re-instantiated with a changed definition.

### Length reconstruction, not semantic equivalence alone

Fix a satisfying compiled clause of weight W on a base graph with N vertices, including its vertex assignment and boundary controls. An interval observer of size s admits a shortest accepting path in a product with Ns vertices, with fewer than Ns edges. The positive-length bit is part of the product control, so shortening preserves required positivity. All active observations remain coordinates of the same product; no independent interval words are substituted.

Summing lengths over interval atoms gives at most NW. Add the first emission: the reconstructed reference has at most `N+1+NW <= N(W+2)` vertices. Core/portal conditions remain fixed at the shared marks and colours. The explicit reconstruction in [RankQuerySound](../lean/Subtail/RankQuerySound.lean), as described in its [readback](2026-09-18-lean-rank-compiler.md), supplies the safe extension and reassembles the original query paths; the conclusion does not follow from an arbitrary semantic equivalence with no length accounting.

Starting at a one-letter reference (two vertices), unwind at most k-2 promotions using the decreasing That budgets. The final k-state finishing observer can also use a shortest product path; a final reference with N vertices gives total witness length at most (k+1)N. Thus the same ordinary reconstruction yields the sufficient replacement

```text
Fhat(1) = 0
Fhat(k) = 2*(k+1)*product_{j=1..k-2}(That_j+2), k>=2.
```

The empty product is 1. For k=1 terminality permits only an empty witness. The reconstruction and Fhat claim are ordinary mathematics, not newly Lean-checked declarations. A native quantitative reconstruction theorem is still needed before assigning formal status.

k counts states of the SUPPLIED TERMINAL INSTANCE, not subtype variables, constraints, or finite-expression syntax nodes. A bound in original subtype-input size requires its own effective translation and state-cardinality analysis. Neither this review nor the terminal bound assumes the remaining infinite-branch/syntax-normalization/executable-composition reduction. Current STATE remains the authority on those other tasks.

## 8. Reproduction and evidence ledger

- [Standalone fixture checker](../experiments/check_rank_query_weight_counterexample.py).
- [Deterministic result](../results/rank-query-weight-counterexample.json).

Run from the repository root, with ordinary Python assertion checking enabled (not `python -O`):

```sh
python3 experiments/check_rank_query_weight_counterexample.py > /tmp/rank-query-weight-counterexample.json
cmp results/rank-query-weight-counterexample.json /tmp/rank-query-weight-counterexample.json
```

The checker is a MANUAL SOURCE TRANSCRIPTION of the used Lean constructors and guards. It verifies this single fixed instance, boundedness/validity conditions, emission counts, strict arithmetic inequality, literal small base/extension graph facts, and the original witness. It does not import or execute the Lean compiler or enumerate the full query union. It cannot detect every possible transcription error; the source-level proof and separate native verification remain important.

Publication replay: Python 3.13.5 at `/usr/bin/python3`, Linux 6.18.44 x86_64, glibc 2.41. No random seed: deterministic fixture. CPU limit 5 seconds, address-space limit 256 MiB, wall timeout 10 seconds. Exit 0; all assertions passed; stdout byte-for-byte equal to the preserved result. Observed wall time about 0.029 seconds, not a compiler performance measurement. A second ordinary replay under a 20-second wall timeout also passed.

The capped successful invocation was a `subprocess.run(['/usr/bin/python3', script], capture_output=True, text=True, timeout=10, preexec_fn=limits)` where `limits` sets `resource.RLIMIT_CPU=(5,5)` and `resource.RLIMIT_AS=(268435456,268435456)`.

Preserved failed attempt: the first capped run using `/opt/pyvenv/bin/python3` exited -9 (signal 9) with no stdout/stderr under the same limits. The cause was not determined; it is not a mathematical negative and was not relabelled as a pass. Replaying with the system interpreter under the same limits produced the successful result above.

SHA-256:

```text
checker: 1ff0d2aad5b604c3ab6026e64b38caa9585858cae6a67088bba01653c7bcc845
result:  c23399b1835e47cbd8f96b7eb1182a9620cc2d2d0d7fc921e38dd0db01f1b33d
```

NOT RUN by this reviewer: Lean build/kernel replay; native Lean counterexample evaluation; complete preimage enumeration; enormous interval-product materialization; full repository experiments/index suite. Existing repository proof results were inspected, not recertified. The universal sufficient bound is justified by the ordinary counting proof, not by this finite replay. This new finding and corrected proof await a separate review; the reviewer is not claiming a blind replication or a human referee.

## 9. Integrator handoff and bounded follow-up contracts

This contribution leaves all Lean code/interfaces unchanged and proposes a dated notice in the compiler record. It does not overwrite shared STATE/claims/approach ledgers while another integrator owns them. Suggested canonical wording, to reconcile against CURRENT records at integration:

> Quantitative C080 update: a source-level, hypothesis-preserving counterexample at 064fc730 shows that `preimage I RankQueryCoverage.budget` does not satisfy the old `64*k*T^(2*T+2)` clause-weight conjunct. The semantic closure and checked terminal decider are unaffected. The old F(k) statement is not itself refuted. An ordinary proof supplies the conservative replacement `64*k*T^(6*T^2+2)` and corresponding larger recurrence; independent/native Lean verification remains pending. See the dated quantitative review and deterministic fixture.

Apply that distinction to C080, STATE, A017/A018 histories/next-step navigation and the experiment registry as appropriate, without marking all of C080 false or deleting historical audits. No new C/E identifier has been allocated here. Reconcile navigation/index checks in the same integration episode. Main integration and fresh CI results are not claimed by this note.

Recommended next tasks, in order; these are proposals, not assignments or running workers:

1. **Native regression and independent readback.** In an agreed isolated Lean file, define the five-state instance, clause and diagram. Prove Bounded, validDiagram=true, exact interval size and the strict weight inequality, then derive preimage membership through `mem_preimageClause`. Do NOT evaluate the full enumerator or filter the astronomical interval state list. Use symbolic size projections/counting. Acceptance: pinned build, kernel replay, dependency audit, and nonauthor statement review against this note.
2. **Choose the quantitative target explicitly.** The low-interface-risk path is a separate theorem for the unchanged compiler with Uhat, keeping old conditional theorems intact. Prove emission-length bounds and per-interval coordinate bounds, then the corrected all-emitted-clause theorem. Alternatively investigate a DISTINCT tighter enumerator with per-observer excursion caps and prove semantic coverage plus the old U bound for that new construction; do not silently assume it equals the current one. Preserve the counterexample whichever route is chosen.
3. **Then formalize bounded reconstruction and Fhat.** First fix marks/boundary controls, shorten each shared interval product path, sum the lengths, and reconstruct the safe extension with the input clause still satisfied. Only then instantiate the promotion/finishing product recurrence. Keep automaton-state size distinct from original subtype-input size and keep this lane off the qualitative terminal-decider dependency path.

A generic deduplication of observer coordinates is not automatically sound: two occurrences can carry different entering/leaving controls. Any later representation optimization needs an exact equivalence proof. The immediate issue is the mismatch between existential normal-form coverage and a universal bound over the emitted envelope, not evidence that terminal decision or the arbitrary-tree research route fails.
