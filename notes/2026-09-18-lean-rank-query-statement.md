# Lean: the rank-query grammar, literal prefix graphs, decidable satisfaction, and the pinned Closure Lemma

Date: 2026-09-18. Workstream A018 supporting A017 (C080, stage 4a; issue #27).
Base main: `d1fdcfb`. Author: Claude (Claude Code session), instructed by the
repository owner. Module: [RankQuery.lean](../lean/Subtail/RankQuery.lean).

**Status: definitions and a kernel-checked decision procedure for finite query
satisfaction; the Closure Lemma itself is PINNED AS A `Prop` AND NOT PROVED.
No `sorry`, no custom axiom. Nothing here changes the CANDIDATE status of C080
or of Problem 1.7.** The statement readback below is by the module's author,
not an independent human review.

## 1. What is defined, read back into ordinary mathematics

All words are finite binary lists. `Instance k`, `step`, `Witness` and
`TerminalFinals` are the existing core definitions; `borderLengths`,
`failureParent`, `maxNat` and `FirstReturn` are the kernel-checked stage-1/2
definitions of `TerminalRank`/`RankMilestones`. Nothing is redefined.

**Colours.** `Colour k = (state : Fin k, mask : Vector Bool k, next : Option Bool,
root, isEnd : Bool)`. `next = none` is the compiler's `END`. A colour never
contains a numeric position. `DecidableEq` is derived, so colours form a finite
alphabet with decidable equality.

**Labels.** `F`, `S`, `K a` for `a : Bool` (the compiler's `K0`, `K1`). All edges
are directed; there is no inverse label.

**Graphs.** `Graph k = (size, colour : Fin size → Colour k, edge : Fin size → Label → Option (Fin size))`.
Edges are functional per label; `S` may be absent (`none`).

**Observers.** `Observer k = (size, initial final : List (Fin size), allows : Fin size → Colour k → Bool, move : Fin size → Colour k → Label → Colour k → List (Fin size))`.
Because `Colour k` is finite, `allows` and `move` are finite tables; this is the
"arbitrary finite Boolean colour predicates" convention of the closure note,
Section 1, and it covers every observer kind of `rank_preimage_core.py`
(`table`, `slice`, `core`, `edge`, `interval`, `finish`) after tabulation.

**Runs and path atoms.** On the product `Node G O = Fin G.size × Fin O.size`,
`Allowed x` means `O.allows x.2 (G.colour x.1)`; `Step x y` means some label `l`
with `G.edge x.1 l = some y.1`, `y.2 ∈ O.move x.2 (colour x.1) l (colour y.1)` and
`Allowed y`; `Run x y` is the reflexive-transitive closure starting from an
allowed node; `Accepts G O u v` is `∃ q ∈ initial, ∃ p ∈ final, Run (u,q) (v,p)`.
This is exactly the acceptance condition of `rank_preimage_core.path`.

**Clauses and queries.** `Clause k = (vars, tests : List (Fin vars × (Colour k → Bool)), equal, unequal : List (Fin vars × Fin vars), atoms : List (Atom k vars))`
with `Atom = (observer, source, target)`. `SatClause G c` is the existence of an
assignment `σ : Fin vars → Fin G.size` satisfying all tests, equalities,
disequalities and path atoms. `Query k = List (Clause k)` is a finite union and
`Sat G φ = ∃ c ∈ φ, SatClause G c`. There is no negated reachability, no
path-label equality, no set quantification and no string variable in the
grammar: the only atoms are unary colour tests, `=`/`≠` between variables and
directed `Path` atoms.

**Weights.** `clauseWeight c = max 2 (1 + vars + #atoms + Σ observer sizes)`,
`weight φ = maxNat (map clauseWeight φ)`, `closureBound k T = 64 k T^(2T+2)`.
These are the compiler's `Query.weight` and the closure note's `T` and `U_k`.

**Labelled references and literal prefix graphs.** `Reference k = (word : Word, label : Nat → Fin k)`
is a reversed reference `rho = b_0..b_(m-1)` with cut states `r_0..r_m`; labels
beyond `m` are irrelevant. `mask I B j` is the vector `p ↦ ∃ border h of rho[:j], (p, r_h) ∈ G`,
over the literal border list including `0` and `j`. `advance w j a` is the
literal longest prefix of `w` of length at most `|w|` that is a suffix of
`w[:j] ++ [a]` (a finite maximum, so at `j = |w|` it is the full-pattern
fallback). `prefixGraph I B` has vertices `0..m`, colour
`(r_j, mask j, w[j]?, j = 0, j = m)`, `F(j) = failureParent (w[:j])`,
`S(j) = j+1` for `j < m`, `K_a(j) = advance w j a`. This matches
`rank_query_graphs.literal_graph`, not the surgery recurrence; the stage-3
branch proves that its surgery construction equals such a literal graph.

**Safe references and first-return extensions.** `SafeReference I B` bundles:
`m ≥ 1`; `r_0` accepting; `step I (r_(j+1)) b_j = some (r_j)`; no `r_j ∈ Bad`;
and `mask I B j` clear at `r_j` for every `j ≤ m` (diagonal pairs and the empty
border included). `FirstReturnExt I B C` bundles: `SafeReference I C`;
`B.word` is a prefix of `C.word`; labels agree on `0..m`; and
`FirstReturn C.word m |C.word|`, i.e. `B.word` reoccurs as a suffix of `C.word`
and does not reoccur ending strictly earlier. Overlapping returns and `L = 1`
are included. Terminality of the instance is NOT part of these predicates;
it is a hypothesis of the pinned statement.

## 2. What is proved

`satCheck G φ` is an executable Boolean, and

    satCheck_correct : satCheck G φ = true ↔ Sat G φ

gives `instance : Decidable (Sat G φ)` on every finite graph. The proof
saturates the product `(vertex, control)` from the seed node: `iter n` applies
`close` (append all unseen allowed successors) `n` times, with
`n = length (allNodes)`. Soundness (`run_of_mem_iter`) is by induction on the
rounds. Completeness uses no path surgery: `closed_or_grow` shows each round
either reaches a successor-closed set or strictly grows a nodup list; a nodup
list of nodes has length at most `length allNodes`
(`List.Nodup.length_le_of_subset`), so after that many rounds the set is
closed (`isClosed_reachable`), and a closed set containing the seed contains
every run target (`mem_of_run_closed`). Assignments are enumerated as lists of
length `vars` (`allLists`, `mem_allLists`) and read back as functions (`toFun`,
`toFun_ofFn`). The axiom audit of all 65 defs/theorems shows only `propext`,
`Quot.sound` and, in theorems, `Classical.choice`; no runtime definition uses
classical choice.

## 3. The pinned statements (not proved)

```text
ClosureFor I pre :=
  (∀ φ B, SafeReference I B →
     (Sat (prefixGraph I B) (pre φ) ↔ ∃ C, FirstReturnExt I B C ∧ Sat (prefixGraph I C) φ))
  ∧ ∀ φ, ∀ c ∈ pre φ, clauseWeight c ≤ closureBound k (weight φ)

ClosureStatement I := TerminalFinals I → ∃ pre : Query k → Query k, ClosureFor I pre
```

`ClosureFor` is deliberately separated so that stages 4b/4c can instantiate
`pre` with an executable compiler and prove the two directions as two theorems
about that specific function. The bare `∃ pre` is a Prop-level existential and
does not itself record effectiveness; an executable instantiation does.

Also pinned, against the original `Witness` predicate, as the stage-4/5 target
the candidate's Section 8 asks for:

```text
finishQuery I     -- one clause per state q: e is End with state q; F edge e→f;
                  -- finishing observer f→x (k controls, forbids End, checks
                  -- Bad/diagonal/mask on K_a moves, accepts at the initial state)
promote pre φ h   -- Φ_0 = φ, Φ_(h+1) = Φ_h ++ pre Φ_h
RankDecisionStatement I pre :=
  (∃ w, Witness I w) ↔ Witness I [] ∨ ∃ a f p, SafeReference I (oneLetter a f p) ∧
     Sat (prefixGraph I (oneLetter a f p)) (promote pre (finishQuery I) (k-2))
```

`finishQuery` has weight `k + 8` (`#guard` checks `9` on the one-state toy),
matching the closure note's `T_0 = k + 10` slack.

## 4. Executed evidence

Local Lean 4.33.1: `lake build +Subtail.RankQuery`, `lake env leanchecker Subtail.RankQuery`,
`#print axioms` for all 65 defs/theorems (no `sorryAx`, no native axiom, no
runtime `Classical.choice`), `python3 scripts/check_lean.py` with
`results/lean-checks.json` unchanged. The module is NOT added to the import
aggregator `lean/Subtail.lean` (owned by the stage-3 formalizer); the dedicated
[workflow](../.github/workflows/lean-rank-query.yml) builds it as an explicit
target and repeats these audits on the runner.

[check_lean_rank_query.py](../experiments/check_lean_rank_query.py) (seed
`2026091801`, `--lean`) translates fixtures to Lean literals and evaluates them
natively: 16 literal prefix graphs of safe references of six random terminal
instances and the one-state toy agree colour-by-colour and edge-by-edge with
`literal_graph`; `satCheck` agrees with `rank_preimage_core.model` and with the
frontier oracle's `explicit_query_truth` on 64 random unions (88 clauses, 43
satisfiable) and with `finish_queries` on all 16 references. Saved:
[results/lean-rank-query.json](../results/lean-rank-query.json). These are
translation/semantics regressions; they say nothing about the Closure Lemma.

`#guard`s in the module reproduce the compiler audit's four one-atom facts on
`P("0")` (`F` reaches the root; `S`, `K0` do not; `K1` does) and the literal
edges of `P("010")` at its endpoint.

## 5. Limits and handoff

* Nothing about `ClosureStatement`, `RankDecisionStatement` or `C080` is proved.
* `pre` is an existential; stage 4b/4c should define an executable `preimage`
  mirroring `iter_diagrams`/`compile_diagram` and prove `ClosureFor I preimage`.
  The forward direction needs product-simple paths and the mark bound; the
  reverse direction needs reconstruction of ONE extension from interval atoms.
  Both should be stated as theorems about `prefixGraph`, using the stage-3
  surgery theorem only as a lemma about that literal graph.
* `SafeReference` uses literal borders; identification with the compiler's
  cursor-based safety is the stage-3 `generator_first_hit_iff` route.
* The differential covers `table` observers with colour-independent moves and
  field/clear/and/not tests; interval/core/edge observers are exercised only
  through the Python checkers, not translated to Lean.
* Binary alphabet only; arbitrary-tree semantics remain outside this module.
