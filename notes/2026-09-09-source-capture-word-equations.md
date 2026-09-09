# Terminal source capture: a single-source decision and bounded-source compilation

Date: 2026-09-09. Base main: `05b20ee73841d0e7105a44beb761e553a7081a8d`.
Workstreams: A017 (primary), A011 (opposing-route implication), A012.

**Status: WRITTEN PROOF + REPRO; independent mathematical review pending; no
Lean formalization.** The argument below decides the **single-source terminal
subclass**, including a source that is not initial and may recur. Its polynomial
reduction gives a PSPACE upper bound for that subclass. It also decides existence
with a supplied bound on flagged-source visits. It does **not** decide general
terminal BorderAvoid or unrestricted Problem 1.7. The practical implementation
compiles the exact formulas; optional Z3 calls are not a complete implementation
of the theoretical constrained-word-equation decision algorithm.

This route bypasses the root-pumping argument rather than repairing it. The
key observation is prefix-free **acceptance from a fixed target state**, not
regularity of the witness language and not bounded witness length.

## 1. Exact setting and end-to-end outline

Let `I=(Q,Sigma,delta,q0,F,Bad,G)` where `Q={0,...,k-1}`, `Sigma={0,1}`,
`delta:Q x Sigma -> Q` is partial, `q0 in Q`, `F,Bad subseteq Q`, and
`G subseteq Q x Q` is an ordered forbidden relation. Every `f in F` is
**terminal**: `delta(f,a)` is undefined for both letters. There are no epsilon
transitions. A path is safe when every state, including its initial state,
avoids `Bad`. Undefined transitions reject. Words are arbitrary finite binary
strings, not bounded-length strings or infinite type trees.

For a defined safe run `c(0),...,c(N)` on `w`, admissibility means `c(N) in F`.
The existing exact witness condition is

```text
for every 0 <= i <= j <= N,
    w[j:] is a prefix of w[i:]  implies  (c(i),c(j)) not in G.
```

The diagonal and empty suffix are included. See
[the executable independent predicates](../experiments/border_lab.py) and
[the binary Lean definition](../lean/Subtail/Basic.lean).

The complete single-source route is:

```text
terminal acceptance makes each target's continuation language prefix-free
  -> at most one accepted prefix per target, from a fixed source position
  -> a finite positive existential word-equation formula for that position
  -> a single-source witness can be normalized to visit its source at most once
  -> a polynomial-size existential formula for single-source existence
  -> a decision, by the free-monoid theorem stated precisely in Section 5.
```

No missing pumping, global word-length, primitive-root, or profile-preservation
hypothesis occurs in this subclass argument. The extension to multiple
recurring sources is a separate obligation (Section 8), not assumed here.

## 2. Explicit regular languages and unique capture

For states `p,t`, define languages using the original safe transition system:

```text
L_t = {v : the safe run from t on v is defined and ends in F},
A_t = Sigma* minus (L_t Sigma*),
D_(p,not t) = {u : the safe run from p on u is defined and ends outside {t}}.
```

All are finite-automaton languages, constructed effectively from `I`.

For `L_t`, use state set `Q`, alphabet `Sigma`, initial state `t`, accepting
set `F \ Bad`, and delete every transition whose source or destination is in
`Bad`. A Bad initial state is nonaccepting with no outgoing transitions.
For `D_(p,not t)`, use the same table, initial state `p`, and accepting set
`Q \ (Bad union {t})`. Both automata remain partial; undefined transitions
reject.

For `A_t`, use `Q union {hit,miss}` and total transitions. `hit` and `miss`
are absorbing. Initialize to `miss` when `t in Bad`, to `hit` when
`t in F \ Bad`, and to `t` otherwise. From a safe nonfinal simulation state,
map an undefined transition or a transition into Bad to `miss`, a transition
into `F \ Bad` to `hit`, and any other transition to its original target.
For completeness, original Bad states transition to `miss`, original final
states to `hit`; those copies are unreachable under the initialization and
transition convention. Every state except `hit` is accepting. The invariant
is: `hit` means some prefix has been safely accepted from `t`; `miss` means
the simulated run died before any acceptance; other states represent its
current safe nonfinal state. Thus this DFA recognizes exactly `A_t`, including
its empty-word case. It has `k+2` states; no subset construction is needed.

**Lemma 1 (prefix-free capture).** `L_t` is prefix-free. Consequently any word
`W` has at most one prefix in `L_t`.

*Proof.* If `v in L_t`, its run has reached a terminal state. No nonempty
extension of `v` has a defined run from the same initial state `t`, so cannot
belong to `L_t`. Any two prefixes of one word are comparable by prefix order.
This proves uniqueness. It includes `L_t={epsilon}` when `t` is a safe final
state. QED.

We call that unique prefix `V` the **capture from t**, when it exists.
Crucially, prefix-free does not mean suffix-free: there may be arbitrarily
many suffixes of one word accepted from `t`. We do not bound those suffixes.

## 3. Eliminate every target cut for one fixed source position

Fix a word `W` admissible from state `p`. We ask whether there is a cut `j`
with state `t` for which `W[j:]` is a prefix of `W`. This is the single
forbidden pair `(p,t)` at **source position zero**, not all occurrences of
state `p` throughout the run.

For words `V,W` with `|V|<=|W|`, define an existential mismatch formula:

```text
MismatchSuffix(V,W) :=
  OR over distinct letters a,b in Sigma:
    exists R,S,Z: V = R a Z and W = S b Z.
```

All variables range over `Sigma*`; juxtaposition is concatenation. There is
no length predicate in this formula.

**Lemma 2.** Under `|V|<=|W|`, the formula holds iff `V` is not a suffix of `W`.

*Proof.* A displayed factorization gives unequal letters at the same distance
from the right end. Conversely, if `V` is not a suffix, take the longest common
suffix `Z` of `V,W`. It is shorter than `V`, and also shorter than `W` because
`|V|<=|W|`. The immediately preceding letters exist and differ, giving `R,S`.
If `V=epsilon`, it is a suffix and the displayed formula has no solution. QED.

Now define the positive existential formula

```text
Phi_(p,t)(W) :=
  W in A_t
  OR
  exists V,X:
    W = V X AND V in L_t AND
    (MismatchSuffix(V,W)
     OR exists U: W = U V AND U in D_(p,not t)).
```

The equation `W=VX` supplies the length precondition of Lemma 2 automatically.
There are no negated variable-dependent membership tests, substring functions,
universal quantifiers, or arbitrary length constraints hidden in this formula.
All auxiliary variables are fresh for this pair, except the intentionally
shared `W`.

**Theorem 3 (exact capture clause).** For `W` admissible from `p`,
`Phi_(p,t)(W)` holds iff there is no forbidden suffix agreement from source
position zero to a cut carrying state `t`.

*Proof, both directions.* Any such agreement uses `V=W[j:]`. This `V` is
accepted from `t` because it is the remainder of the safe accepted run, and
is a prefix of `W`. Therefore it must be the unique capture of Lemma 1.
In that event `W notin A_t`, `MismatchSuffix(V,W)` is false, and the unique
factorization `W=UV` has `U=W[:j]` ending at `t`; hence its wrong-state clause
is false. No alternative capture can make the formula true.

Conversely, if `W in A_t`, no violation can supply an accepted prefix from
`t`. Otherwise the unique capture exists. If it is not a suffix, no target
cut can use it, and the mismatch branch is true. If it is a suffix, there is
exactly one corresponding cut `j=|W|-|V|`. Its prefix `U` is defined and safe
because `W` is. If its state is not `t`, the wrong-state branch holds and no
violation exists. If its state is `t`, the captured suffix is a forbidden
agreement and all formula branches fail. These cases exhaust the possibilities.
QED.

In particular this proof includes overlapping occurrences: it never assumes
`W=V middle V` with disjoint copies. When `t=p`, the diagonal is detected.
When `t in F`, the capture is empty; the wrong-state branch checks whether
the actual final state is `t`. Thus multiple final states and empty-suffix
flags are handled exactly. Bad states are excluded in each language.

For a target set `T`, conjoin `Phi_(p,t)(W)` over `t in T`, keeping one shared
word `W`. This is still a positive existential formula of polynomial size.
Different targets may not choose different candidate words.

## 4. Single-source existence, including an interior or recurrent source

Assume every flag leaves one state `p`; the start need not be `p`, and incoming
transitions or returns to `p` are allowed. Empty `G` is ordinary regular
nonemptiness and is handled separately.

**Lemma 4 (one-visit normalization).** If a single-source witness exists,
there is one visiting `p` at most once.

*Proof.* Let `w` be a witness visiting `p`, with first visit `a` and last visit
`b`. Set `v=w[:a]w[b:]`. Splicing two equal states preserves the defined safe
accepted run. The prefix strictly before the splice contains no source state.
The suffix at and after the splice is the unchanged suffix at the last visit
of `p` in `w`, and has no subsequent `p`. Every flagged comparison in `v`
therefore corresponds to a comparison starting at `b` in `w`, with identical
suffixes and states. It cannot be forbidden. If `a=b`, nothing is changed.
Witnesses avoiding `p` require no transformation. QED.

Construct three more regular languages:

```text
Avoid_p = safe accepted words from q0 that never visit p;
Entry_p = safe paths from q0 to their first visit of p;
Tail_p  = safe accepted words from p with no positive return to p.
```

For `Avoid_p`, remove `p` as well as Bad from the path DFA and use start `q0`,
finals `F`; when `q0=p` the language is empty. For `Entry_p`, delete outgoing
transitions of `p`, use start `q0`, and accept only `p` (unless Bad).
For `Tail_p`, delete transitions into `p`, start at `p`, and accept `F \ Bad`.
The initial state is counted, so `Entry_p={epsilon}` when `q0=p` and `p` is
safe. A terminal `p` permits the empty tail. These are explicit O(k)-state
partial DFAs, using the same binary alphabet.

A formula for single-source witness existence is

```text
exists W:
  W in Avoid_p
  OR
  exists E,Z:
    W = E Z AND E in Entry_p AND Z in Tail_p
    AND every Phi_(p,t)(Z), for (p,t) in G.
```

**Theorem 5.** This formula is satisfiable iff the original single-source
terminal instance has a witness.

*Proof.* A model in the first branch avoids every flagged source. A model in
the second branch is safe and accepted, has exactly one source position, and
Theorem 3 excludes all its forbidden target cuts. Hence its `W` is a witness.
For the other direction normalize any witness using Lemma 4. If it avoids the
source it belongs to `Avoid_p`; otherwise split it at its sole visit. The
prefix and tail belong to `Entry_p,Tail_p`, and each capture clause is true
by Theorem 3. QED.

The formula recognizes **one-visit witness normal forms**, not every witness
of the original language. Pinning `W` to a particular witness with repeated
source visits may therefore be UNSAT. This is intended and does not contradict
the existence equivalence. The source-sequence construction below, in contrast,
checks the supplied exact sequence without deleting visits.

## 5. Exact external theorem and complexity transfer

The external result used is **Theorem 4**, page 8 of the 2001 preprint by
Volker Diekert, Claudio Gutierrez and Christian Hagenah,
*The existential theory of equations with rational constraints in free groups
is PSPACE-complete*, [arXiv:cs/0103018](https://arxiv.org/abs/cs/0103018).
Despite the paper's title, Theorem 4 is specifically about **free monoids with
involution**, not free groups. It decides closed existential propositional
formulas built from word equations and regular constraints supplied by finite
automata, in polynomial space.

Our transfer uses its involution-free special case. Constants are binary
letters; variables are finite words; the only operations in terms are
concatenation and constants. All regular constraints above have explicitly
constructed finite automata. Conjunctions, disjunctions and existential
quantifiers are exactly the permitted formula operations. If the ambient
involution alphabet is extended, constrain every variable to `{0,1}*`; there
is no free cancellation or identification of letters with their inverses.
Fresh auxiliary variables can be pulled to the front because each is bound
only in its own branch and the word domain is nonempty.

There are O(|G|) capture clauses and auxiliary variables in Theorem 5, each
using O(k)-state DFA atoms and a constant number of binary mismatch branches.
Entry, tail and avoidance automata also have O(k) states. Thus the reduction
is polynomial in the explicitly encoded input. **Single-source binary terminal
BorderAvoid is in PSPACE, and in particular is decidable.** No PSPACE lower
bound for this subclass is claimed. The general constrained-equation theorem's
hardness does not automatically transfer to this particular formula shape.

The implementation's optional DFA-to-regex state elimination and SMT solver
are not the theoretical polynomial reduction or a proven complete solver.
The polynomial statement concerns the direct formula with DFA atoms. An SMT
`unknown` or time limit remains UNKNOWN. Returned SAT words are checked against
both existing witness predicates; returned UNSAT answers retain the backend
trust boundary and are not formal proof certificates.

## 6. Bounded source visits: exact multi-source compilation

Let `S={p : exists t, (p,t) in G}`. A source visit counts a **position** in a
run, including position zero and terminal position when in S; it is not merely
a distinct state label. Fix a finite sequence `s1,...,sm` of states in S.

Introduce segments `B0,...,Bm` and suffix variables `Z1,...,Zm`, with

```text
W = B0 B1 ... Bm,
Zj = Bj ... Bm               (1 <= j <= m).
```

Require `B0` to run safely from `q0` to its first source, `s1`. For `1<=j<m`,
require `Bj` to be a **positive-length** safe path from `sj` to its next source,
`s(j+1)`, with no source at an interior position. Require `Bm` to run safely
from `sm` to F with no later source visit; it may be empty. All are regular
path languages. Conjoin `Phi_(sj,t)(Zj)` for every outgoing flag `(sj,t)`.
When `m=0`, require just a safe accepted path avoiding S.

The segment DFAs are explicit. The first segment removes every source except
`s1`, and stops on `s1`. For an intermediate segment use a fresh initial copy
of `sj`; every original source state has no outgoing transitions, the only
accepting state is `s(j+1)`, and transitions into any other source are removed.
The initial copy has the original safe outgoing transitions. This ensures
positive length even if successive sequence entries are equal. For the final
segment, use start `sm`, accept F, and remove every transition into S. Always
remove Bad states/transitions as before. There are at most `k+1` states per
segment automaton.

**Theorem 6.** The displayed existential formula has a solution iff there is a
witness with exactly the supplied source-visit sequence.

*Proof.* The segment constraints identify every source position, in order,
without omitting an occurrence or counting one twice. Their concatenation
produces a single safe accepted run. Each `Zj` is its actual suffix at the
corresponding source, not an independently chosen continuation. Theorem 3
therefore excludes exactly every forbidden comparison of the entire word.
Conversely, split any such witness at its source visits to satisfy the same
regular constraints, suffix equations and capture clauses. QED.

For supplied R, enumerate all sequences of length at most R and apply the
external decision theorem. This decides existence of a witness using at most
R source positions. With R in unary, a sequence can be guessed in polynomial
space and its polynomial-size formula solved in PSPACE; this yields a PSPACE
upper bound in input size plus R. Unbounded unflagged path lengths require no
word-length, marker-count, homogeneous-run or exponent bound.

**Corollary 6a (source-acyclic productive graphs).** Compute the safe productive
subgraph (reachable from q0 and able to reach F). If no directed cycle contains
a source state in this graph, every accepted run visits each source at most
once. Take `R=|S|`. Theorem 6 gives a decision even when unflagged components
are arbitrarily recurrent and nonflat. This condition is effectively checkable
by strongly connected components. The current code supplies the sequence
compiler; it does not implement a complete constrained-equation backend or
claim a practical all-sequences solver.

**Corollary 6b (exact source-wise pruning).** In a general instance, restrict
flags to those leaving p and change the start to p. Decide this single-source
instance by Theorem 5. If it has no witness, no global witness can visit p:
the suffix of a global witness at such a visit would witness that restricted
instance. Therefore p may be added to Bad. This removes the forward-closed
restriction of the earlier local viability test at the theoretical level.
Positive source-wise answers still do not compose (C042). Repeated pruning
terminates but is not a complete general decision method.

## 7. Adversarial counterexamples and executed checks

**Terminality cannot be dropped from first-capture reasoning.** Take start 0,
finals `{1,2}`, flag `(0,1)`, table `0:(1,1), 1:(1,2), 2:(-,-)`. This is not
terminal-final because accepting state 1 has outgoing edges. On `W=11`, the
capture algorithm stops at the empty accepted prefix from 1; that prefix
occurs at the final cut, carrying state 2, so its wrong-state clause passes.
But the longer accepted prefix `1` is also the actual suffix at cut 1 with
state 1, giving a real violation. The API rejects this nonterminal input.

**First-to-last deletion does not extend source by source.** Take start 0,
terminal final 4, no Bad states, flags `{(0,1),(2,0)}`, and table:

| State | 0 | 1 |
|---|---:|---:|
| 0 | 1 | 2 |
| 1 | 4 | 1 |
| 2 | 3 | 2 |
| 3 | 1 | 0 |
| 4 | undefined | undefined |

`110010` is a witness. Its run is `0,2,2,3,1,1,4`. Deleting the loop between
the first and last occurrence of source 2 gives `10010`, still accepted, with
run `0,2,3,1,1,4`. Its suffix `10` at cut 3 equals its prefix `10`, and the
pair at cuts `(0,3)` is flagged `(0,1)`. The earlier source acquired a new
violation. The second flag is not structurally vacuous: accepted word `101010`
has an actual `(2,0)` violation. This refutes that local sequential-compression
rule, **not** an existential bound or every possible normalization; this
instance also has other witnesses.

Reproduce the deterministic standard-library checks:

```sh
python3 experiments/check_source_capture.py
```

The saved [result](../results/source-capture.json) records all 256 binary
three-state tables with final state 2 terminal, every Bad subset and every
initial state, and words through length 6. On admissible cases this gives
8,568 target-clause comparisons, including 320 cases where the wrong-state
branch is essential. Another 1,800 accepted recurrent paths on 300 generated
3--9-state automata reach length 88 and give 10,848 further target comparisons.
The independent oracle checks actual cuts, not the capture optimization.

A separate 240-instance sample checks 122,640 words through length 8 against
both original witness predicates; its 201 witnesses include seven strict
one-source normalizations. Two hundred multi-source samples check actual
source-segment reconstruction on 635 accepted words. Boundary cases include
empty witnesses, diagonal flags, undefined paths, multiple final states and
Bad states. Both counterexamples above are fixed regressions, independent of
their exploratory searches.

Optional unbounded formula probes:

```sh
python3 experiments/check_source_capture.py --with-smt
```

The local native Z3 4.13.3.0 run returned 34 SAT and 17 UNSAT across 51 probes, zero
UNKNOWN in that run. They include the recorded five-/six-state single-source
fixtures, fixed good/bad words, exact multi-source visit sequences and 36
additional fixed accepted-word probes. Every SAT word passes both original
witness predicates. These observations validate that backend on the probes;
they do not prove completeness of Z3 or the all-length theorem. Solver models
may vary across versions; the optional output is not a byte-for-byte CI oracle.
The deterministic non-SMT results are the reproducibility artifact.

## 8. What remains for general SEP, and the opposing route

The missing quantifier is now exposed differently. A sufficient target is a
total computable function `R(k)` such that **every positive k-state terminal
instance has some witness visiting flagged sources at most R(k) times**.
Theorem 6 would turn that bound into a complete decision. It need not bound
visits on every accepted word, preserve every profile, or make all witnesses
regular. No such bound is proved here. More general finite symbolic covers
could avoid a literal bound on visits.

Conversely, if general binary terminal witness existence were decidable, a
computable source-visit bound could be obtained: for each k, enumerate the
finitely many labelled k-state instances, use the decider to select positive
ones, enumerate a witness for each, and take the maximum visit count (zero if
none). This is an equivalence with decidability, not independent evidence that
the bound exists. Transferring back to arbitrary-tree SEP uses C030/C031 and
their existing written/audited status; this note does not re-prove that bridge
or identify single-source automata with an already named full subtype class.

The opposing investigation gains a concrete restriction. An undecidability
reduction into the single-source terminal subclass would contradict Theorem 5.
More generally, an effective encoding together with a computable source-visit
bound for its positive outputs would make the encoded existence problem
decidable by Theorem 6. Thus a genuine negative construction must escape that
bounded-source framework, not merely produce nonregular copied blocks.
This is a barrier to a specified encoding class, not an undecidability proof
and not an impossibility theorem about all encoding ideas.

The next constructive question is whether repeated sources admit a finite
symbolic summary retaining **one shared word** across earlier obligations.
The displayed two-source counterexample is the first regression for any such
summary. Independent review should first audit unique capture, empty/diagonal
cases, first-to-last normalization, and the precise free-monoid transfer.
No independent mathematical reviewer or Lean check has yet certified this note.

## Concurrent integration and claim identity

This argument was developed from `05b20ee` and integrated onto concurrent main
`00b09066e4ca620f91a308cf55c77b7720c28882`. Its canonical IDs are C067/C068 and E043.
Concurrent C065 supplies a different one-flag counting decision with an explicit
witness-length bound; C066 refutes naive two-target incidence subtraction.
The source-capture formula treats all targets on the same word and therefore
does not use that subtraction. It does not supply the counting method's explicit
bound. The guarded-order solver and its terminal-anchor obstruction are also
retained; no independent re-certification of those proofs is claimed here.
See [one-flag counting](../research/ONE_FLAG_COUNTING.md) and
[the parallel order-cover route](../research/ORDER_COVER_ROUTE.md).
