# Lean stage 4b: diagram coverage and the forward Closure direction (issue #28)

Date: 2026-09-19. Author: Claude (Claude Code session), the author of
`RankQueryCompiler.lean` and `RankQuerySound.lean`; this readback is by the
module's author, not an independent reviewer. Workstream A018 supporting
A017/C080. Module: [RankQueryCoverage.lean](../lean/Subtail/RankQueryCoverage.lean)
(439 declarations, no `sorry`, no custom axiom). Enumerator (imported
unchanged from `lean/diagram-enumeration-2026-09-18`):
[RankQueryEnumeration.lean](../lean/Subtail/RankQueryEnumeration.lean) with
its [readback](2026-09-18-rank-query-enumeration.md).

## Exact statements

```text
budget      : Clause k → Limits                          -- computable, RankQueryCoverage.budget
coverage    : ∀ (I : Instance k), DiagramCoverage I budget
closure_iff : ∀ I B, SafeReference I B → ∀ φ,
              Sat (prefixGraph I B) (preimage I budget φ) ↔
              ∃ C, FirstReturnExt I B C ∧ Sat (prefixGraph I C) φ
```

`DiagramCoverage I budget` (defined in `RankQueryEnumeration`) says: for every
safe `B`, every first-return extension `C` of `B` and every clause `c` with
`SatClause (prefixGraph I C) c`, there is a diagram `D` with
`Bounded c (budget c) D`, `validDiagram I c D = true` and
`SatClause (prefixGraph I B) (compileValid I c D)`. `closure_iff` is
`preimage_iff_of_coverage I budget (coverage I)`; its `←` half is the earlier
`closure_reverse`. Together they are the first conjunct of
`ClosureFor I (preimage I budget)` for the concrete executable `preimage` of
the enumerator. The second conjunct (the clause-weight bound, stage 5, #30) is
NOT proved here, and `ClosureStatement`/`RankDecisionStatement` remain open.

The budget, with `V = c.vars`, `A = c.atoms.length`, `S = Σ_i (obsAt c i).size`:

```text
blockBound  = 3A + 2S              groupBound  = 2 + V + 2A + 2S
coreBound   = V + A·blockBound·2   perAtom     = 2·blockBound
seamEntries = blockBound·groupBound
scalar      = coreBound + groupBound + 2·blockBound + A + S + 1
```

This is deliberately loose (Lemma 3's `v + 2 + 2Σ(s_i+1)` marks is the group
bound; everything else is derived from it). It only has to be finite and
computable; the enumerator does the rest.

## Construction (readback of Lemma 3/4 of the candidate proof)

Fix a safe `B` with `m = |B.word|`, a first-return extension `C` and a model
`τ` of `c` in `prefixGraph I C`. Through `exists_ext` (the stage-3 trace
representation: `C.word = B.word ++ trace`, labels agree at every position),
`prefixGraph I C = prefixGraph I (extRef B ((a,p)::rest))`, so all colour and
edge facts of the extension graph are the `colC_*`/`edgeC_*` identities already
proved in `RankQuerySound`. Positions `≤ m` are old, positions `m+1..N` fresh.

1. **Chains.** For every atom, `accepts_bounded_visits` gives a repetition-free
   accepting chain of `(position, control)` nodes visiting `m+1` at most
   `size` times (`chain_exists`; nodes are carried as `Nat × Nat`, `NNode`).
2. **Blocks.** A chain is cut (`segments`) at every step that is not
   `compat`: old→old, or fresh→fresh with position `+1`. Blocks are maximal old
   blocks and maximal physically consecutive fresh blocks. Every fresh block
   after the first starts at `m+1` (`fresh_break_target`, from
   `fresh_edge_shape`), so `freshCount ≤ 1 + visits(m+1) ≤ 1 + size`
   (`freshCount_le_visits`) and `#blocks ≤ 2·freshCount + 1`
   (`length_segments_le`).
3. **Marks.** `rawMarks = [m+1, N] ++ fresh variable positions ++ both
   endpoints of every fresh block`; `M = marksOf N rawMarks` is the sorted
   nodup list of these positions, `n = |M| ≤ |rawMarks| ≤ groupBound`
   (`Nodup.length_le_of_subset`, `raw_length_le`). Group `g` has position
   `pos g`; `idx p` is the group of mark `p`. `pos 0 = m+1`, `pos (n-1) = N`.
4. **Diagram** `X.D`: `groups = n`; `coreVars = V + A·K·2` with
   `K = Σ_i #blocks_i ≤ blockBound`, core variable `cix ai si side` for the head
   (`side 0`) and last (`side 1`) node of block `si` of atom `ai`; `loc v =
   fresh (idx τv)` or `core v`; `states = M.map C.label`, `nextBits = M.map
   (C.word[·]?)`, `firstBit = a`, `oldEnd = colB I B m`; pieces of atom `ai`
   alternate block pieces (even index: `core` for an old block with head/last
   core indices, `forward` for a fresh block with the groups of its endpoints
   and its two controls) and transition pieces (odd index: `enter` for
   old→fresh with target group 0, `wrap` for an endpoint wrap `N → m+1`, `exit`
   for fresh→old), with the label of a transition recomputed from the step
   (`stepLabel`, `labelOK`); seams `(ai, 2·si, g, ctlAt blk (pos g))` for every
   group strictly inside a fresh block.
5. **Assignment** `σ` on the compiled clause: `END ↦ m`, `INITIAL ↦
   failureParent B.word`, `z_g ↦ cursor(pos g)` (the KMP cursor of the
   stage-3 walk, `Ext.cur`), core variable `x ↦ min(corePos x, m)` where
   `corePos` decodes `cix` and reads the head/last position of the block, or
   `τ v` for a clause variable.

Then `Cov.valid : validDiagram I c X.D = true` (`atomValid_all`, seam
lookups, first-source/last-target checks), `Cov.sat : SatClause (prefixGraph I
B) (compileValid I c X.D)` (per-piece facts `PieceOK` for every piece kind:
old-block runs transported to the base graph (`old_block_run`), portal tests
for `enter`/`exit`/`wrap` from `edgeC_*`, equalities between adjacent core
indices, the shared-interval product run `interval_accepts` built from the
chains' controls at every position of `[pos g, pos (g+1)]` with the mixed-radix
encoder `encodeI`/`decodeI_encodeI`, and the fresh-variable tests/equalities),
and `Cov.bounded : Bounded c (budget c) X.D`. `coverage` assembles the `Cov`
structure from `exists_ext`, `chain_exists` and `Classical.axiomOfChoice`
(a theorem, so choice is allowed) and returns `⟨X.D, bounded, valid, sat⟩`.

## What this does and does not establish

- Proved (kernel-checked): the forward semantic direction of the Closure Lemma
  for the concrete executable preimage of the enumerator, i.e. the first
  conjunct of `ClosureFor I (preimage I budget)` for every `I`.
- Not proved: the clause-weight conjunct of `ClosureFor` (stage 5, #30);
  `F(k)` and finishing correctness; the stage-6 entailment decision (#31).
  `ClosureStatement` and `RankDecisionStatement` are therefore still open and
  C080 remains a CANDIDATE.
- The budget is a sufficient cap for coverage; it is not claimed to be tight,
  nor to match the Python `iter_diagrams` caps. The Python compiler's coverage
  is unaffected by this theorem (the Lean `preimage` is the executable of
  record for the closure claim).
- Author readback only. The compiler, its soundness proof and this coverage
  proof share one author; the #32 fixtures and the compiler differential are
  the only independent checks of the compiler's reading of the paper. A
  cross-session readback of `DiagramCoverage`, `Bounded`, `budget` and
  `closure_iff` is the #33 lane.

## Evidence

Lean 4.33.1 (pinned): `lake build Subtail` (whole library including the
enumeration modules and `RankQueryCoverage`, now default imports),
`lake env leanchecker Subtail.RankQueryCoverage`, `#print axioms` of all 439
declarations of the module: theorems use at most `propext`, `Classical.choice`,
`Quot.sound`; every `def`/`abbrev`/`structure` uses at most `propext` and
`Quot.sound` (no classical choice in definitions; `inodeAt` takes its two
bound proofs as arguments for exactly this reason). The consolidated
[Lean workflow](../.github/workflows/lean.yml) builds, replays and audits the
enumeration and coverage modules and runs the enumerator's independent syntax
census; the former isolated `lean-rank-enumeration.yml` is folded into it.
The existing differentials (`results/lean-rank-query.json`,
`results/lean-rank-compiler.json`) and `results/lean-checks.json` are unchanged.

## Failed or discarded attempts (kept for reuse)

- A first bound for the number of groups through `N` (the extension length)
  was rejected: it is not a function of the clause. The count goes through
  `visits(m+1)` instead (`freshCount_le_visits`).
- `omega` repeatedly failed on goals mixing `X.n`, `X.D.groups` and
  `(X.segs ai).length`; these are different atoms for it and need `rfl`
  equations or `unfold` first. Dependent `Fin` rewrites (`rw` motive errors)
  were replaced by `Fin.ext`/`Prod.ext`/`show`.
- `inode` originally derived its `Fin` bounds inside the definition, which
  pulled `Classical.choice` into a `def` through `xI_ok`/`encodeI_lt`; the
  bounds are now hypotheses of `inodeAt` and separate theorems.

## Next question

Stage 5 (#30): the clause-weight conjunct of `ClosureFor I (preimage I
budget)`, i.e. `weightBound` for `compileValid` under `Bounded c (budget c)`,
then `F(k)` and finishing correctness; then the stage-6 composition (#31).
