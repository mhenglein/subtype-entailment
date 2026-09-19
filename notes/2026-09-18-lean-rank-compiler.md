# Lean: the executable diagram compiler and the reverse direction of the Closure Lemma

Date: 2026-09-18. Workstream A018 supporting A017 (C080, stage 4c; issue #29,
tracker #34). Base main: `a033844` (merged with `2120e15` before integration).
Author: Claude (Claude Code session), instructed by the repository owner.
Modules: [RankQueryCompiler.lean](../lean/Subtail/RankQueryCompiler.lean) (57
declarations) and [RankQuerySound.lean](../lean/Subtail/RankQuerySound.lean)
(195 declarations). Differential:
[check_lean_rank_compiler.py](../experiments/check_lean_rank_compiler.py),
[lean-rank-compiler.json](../results/lean-rank-compiler.json).

**Status: the reverse direction of the Closure Lemma is PROVED in Lean for the
executable diagram compiler, for every diagram enumeration. The forward
direction (stage 4b: every safe first-return extension is covered by some
enumerated diagram) and the weight bound (stage 5) are NOT proved, so
`ClosureFor` itself remains unproved and C080 remains a CANDIDATE. No `sorry`,
no custom axiom, no `opaque`.** The readback below is by the modules' author,
not an independent human review.

## 1. Question and exact scope

The pinned Closure Lemma (`RankQuery.ClosureFor I pre`) asks, for a preimage
map `pre : Query k → Query k` and every safe reference `B`,

```text
Sat (prefixGraph I B) (pre φ) ↔ ∃ C, FirstReturnExt I B C ∧ Sat (prefixGraph I C) φ
```

plus a weight bound. Stage 4c is the `←`-to-`→` reading of the biconditional
from the compiled side: a base model of `pre φ` must produce one safe
first-return extension modelling `φ`. This note records an executable `pre`
over supplied diagram lists and the proof of that half.

## 2. What is defined (RankQueryCompiler.lean)

`Diagram k` is the bounded portal diagram of `rank_preimage.compile_diagram`:
ordered mark groups `0 .. groups-1` (group `0` the first fresh vertex,
`groups-1` the new endpoint), core variables, one location per clause variable
(`Loc.core x` or `Loc.fresh g`), the actual reverse state and next bit at each
group, the first emitted bit, the guessed colour of the old endpoint, one piece
list per atom (`core`, `forward`, `enter`, `exit`, `wrap` pieces with controls
`lc`/`rc` and a label), and shared seam controls.

The compiler is split into a Boolean guard `validDiagram I c D` (the
`InvalidDiagram` raises of the Python compiler) and a TOTAL construction
`compileValid I c D : Clause k`; `compileDiagram I c D = if validDiagram then
some compileValid else none`. Variables: `END = 0`, `INITIAL = 1`, origins
`z_g = 2 + g`, core variables after. The compiled clause has: the old-endpoint
colour test, `¬End` tests on every origin but the last, the pulled-back unary
tests (`queryTest`), the core-core equalities (`corePairs`) and the
`z_{n-1} = END` equality, the core-core disequalities, the two base atoms
`END --F--> INITIAL` and `INITIAL --K_a--> z_0` (with mask and End guards), one
shared-interval product atom `intervalObs` per internal interval (controls
`(state, next, seen, t_1 .. t_b)` in `radix_encode` order), and the emitted
tests/equalities/atoms of every piece (`compilePiece`). `preimageOver I c Ds`
is the clause preimage over a supplied list of diagrams; `preimageQuery I
diagrams φ` (in RankQuerySound) is the clause-wise union. No diagram
enumerator (`iter_diagrams`) is defined in Lean.

**Differential.** `check_lean_rank_compiler.py --lean` (seed 2026091841) runs
Lean `compileDiagram` + `satCheck` against Python `compile_diagram` + `model`
on 37 certificate diagrams (brute-force first-return extensions of a toy and two
random terminal instances) and 100 mutants, over several bases: 733
comparisons, 326 rejections, 218 satisfiable, 189 unsatisfiable, no mismatch.
The compiler did not change after that run.

## 3. What is proved (RankQuerySound.lean)

Main theorems, all for `hB : SafeReference I B` and WITHOUT `TerminalFinals`:

```text
compile_sound   : compileDiagram I c D = some P → SatClause (prefixGraph I B) P →
                  ∃ C, FirstReturnExt I B C ∧ SatClause (prefixGraph I C) c
preimage_sound  : Sat (prefixGraph I B) (preimageOver I c Ds) →
                  ∃ C, FirstReturnExt I B C ∧ SatClause (prefixGraph I C) c
closure_reverse : Sat (prefixGraph I B) (preimageQuery I diagrams φ) →
                  ∃ C, FirstReturnExt I B C ∧ Sat (prefixGraph I C) φ
```

`closure_reverse` is exactly the `→` half of the first conjunct of `ClosureFor I
(preimageQuery I diagrams)` for every `diagrams`.

**Route (readback).** A base model `σ` of the compiled clause is turned into
reconstruction data `Recon` (`exists_recon`): the old endpoint (`END` test),
the failure parent (`F` atom), the first emission (`K_a` atom with its mask/End
guard), and, for each internal interval, a generator trace `Gen` extracted from
the accepted run of the shared-interval product (`run_gen`): each step emits the
pending bit along the base `K_b` edge, every active observer moves by `S` or
`K_b` between the same two fresh colours, and the `seen` bit forces positive
length. The traces concatenate to `ext`; `extRef B ext` is the literal
extension (word `B.word ++ letters`, labels = reverse states).

*Single generator (`compiled_extension`).* `cursor_eq_walk` identifies the
stage-3 generator cursor with the literal walk on `P(B)`; the `¬End` tests on
`z_0 .. z_{n-2}` and the `z_{n-1} = END` equality give no intermediate hit and a
final hit, so `FirstReturnGraph.generator_first_hit_iff` yields the literal
first return (`extRef_firstReturn`); reverse-run consistency, `Bad`, the
diagonal flag and the mask guard give `SafeReference` through
`fresh_clear_iff`/`mask_get_eq` (`extRef_safe`).

*Reassembly (`compile_sound`).* Colours and edges of `prefixGraph I (extRef B
ext)` are read through stage 3's surgery identification: old vertices carry
`coreMap a` of their base colour (`colC_core`, `colC_end`), the mark of group
`g` carries `freshMap I (state g) (next g)` of the origin's base colour
(`colC_pos`), old `F`/`S` edges are unchanged, old `K` edges are unchanged
except the endpoint's `K_a` edge which now enters the first fresh vertex
(`edge_into_first`), and fresh `F`/`K` edges land where the compiler's portal
guards say (`edge_F_mark`, `edge_K_mark`). Every piece of every atom then yields
a run of the ORIGINAL observer between its placed endpoints (`piece_run`):
core pieces by transporting the slice run over old vertices
(`coreObs_run_transport`), forward pieces by chaining the interval runs with the
seam controls (`forward_chain`, `interval_run`), portal pieces by the emitted
`portalTest` and the actual edge (`portal_run`). Pieces glue at their seams
(`chain_run`), the atom's initial/final guards give `Accepts` (`atom_accepts`),
and the assignment `assign` (core variable ↦ its base vertex, fresh group ↦ its
mark, junk locations clamped) satisfies the pulled-back tests, the core
equalities and all disequalities (`test_sound`, `equal_sound`, `unequal_sound`;
fresh-fresh disequalities use strict monotonicity of mark positions, mixed ones
use old ≤ |B| < mark).

## 4. Validation

Local Lean 4.33.1: `lake build Subtail` (all modules, including the merged
stage-5 `RankQueryUnwind`), `lake env leanchecker Subtail.RankQuerySound` and
`... RankQueryCompiler`, `#print axioms` of all 334 public declarations of
`RankQuery`, `RankQueryPaths`, `RankQueryCompiler`, `RankQuerySound`
(theorems ⊆ {`propext`, `Quot.sound`, `Classical.choice`}; definitions use no
`Classical.choice`), and the differential replay. The
[workflow](../.github/workflows/lean.yml) (formerly `lean-rank-query.yml`) repeats all of this.

## 5. Result and limitations

Established: for every diagram enumeration, the compiled preimage is SOUND for
promotion, i.e. every base model of it certifies a safe first-return extension
modelling the query. Because `Sat` and `SatClause` on literal prefix graphs are
decidable (stage 4a), `closure_reverse` is a kernel-checked certificate
extractor: a model of the compiled query produces the extension.

Not established: (i) the forward direction, that every safe first-return
extension with `P(C) ⊨ φ` is captured by some enumerated diagram (this needs
the bounded-visits normal form of #28 and an explicit `iter_diagrams`
enumerator with its termination and coverage); (ii) the weight bound
`clauseWeight ≤ closureBound k (weight φ)`; (iii) any statement about the
Python enumerator's completeness. `compile_sound` needs only `SafeReference I
B`; `TerminalFinals` is not used. Independent review of this readback has not
happened; the module author wrote both the compiler and the proof, so a shared
misreading of the paper compiler would not be caught here, only by the
differential and the fixtures of #32.

A concurrent support branch (`lean/portal-transport-support-2026-09-18`,
`RankQueryPortalTransport.lean`) proved similar portal-edge constructors; it is
not imported here, `RankQuerySound` is self-contained over `RankQuery`,
`RankQueryFirstReturn` and `RankQueryCompiler`.

## 6. Next step

Stage 4b: define `enumDiagrams I φ : Clause k → List (Diagram k)` in Lean
mirroring `iter_diagrams`, prove coverage (`SatClause (prefixGraph I C) c` for a
safe first-return extension `C` of `B` gives a valid diagram `D ∈ enumDiagrams`
with `SatClause (prefixGraph I B) (compileValid I c D)`) via
`accepts_bounded_visits`, and then the weight bound; together with
`closure_reverse` this discharges `ClosureFor I (preimageQuery I enumDiagrams)`.
