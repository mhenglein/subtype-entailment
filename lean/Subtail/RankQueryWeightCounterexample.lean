import Subtail.RankQueryCoverage

/-!
# A native counterexample to the old concrete clause-weight contract

C080 / A017-A018, issue #30. This module is additive: no compiler, weight,
enumeration, semantic interface or terminal decision is changed.

The finite facts below use kernel reduction, never compiled proof oracles.
Only structural size projections are reduced. In particular the full diagram
enumerator and the interval observer's enormous control lists are not evaluated.
The semantic satisfiability fixture is described separately in PR #47; the
universal weight conjunct already fails on syntactically emitted clauses.
-/
namespace Subtail.RankQueryWeightCounterexample

open RankQuery RankQueryCompiler RankQueryEnumeration

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A terminal five-state chain accepting 1010. -/
def inst : Instance 5 where
  initial := 4
  transitions := #v[(none, none), (some 0, none), (none, some 1),
                    (some 2, none), (none, some 3)]
  bad := #v[false, false, false, false, false]
  final := #v[true, false, false, false, false]
  flags := Vector.replicate 5 (Vector.replicate 5 false)

/-- Every labelled move is permitted; both controls are genuine declared states. -/
def obs : Observer 5 where
  size := 2
  initial := [0]
  final := [0]
  allows := fun _ _ => true
  move := fun _ _ _ _ => [0, 1]

/-- Five atom occurrences are intentionally retained by the list grammar. -/
def input : Clause 5 where
  vars := 1
  tests := []
  equal := []
  unequal := []
  atoms := List.replicate 5 ⟨obs, 0, 0⟩

def forward : Piece := ⟨.forward, 0, 1, 0, 0, .F⟩
def wrap : Piece := ⟨.wrap, 1, 0, 0, 0, .K false⟩
def pathPieces : List Piece := (List.replicate 35 [forward, wrap]).flatten

def diagram : Diagram 5 where
  groups := 2
  coreVars := 0
  loc := [.fresh 0]
  states := [3, 4]
  nextBits := [some true, none]
  firstBit := false
  oldEnd := ⟨2, Vector.replicate 5 false, none, false, true⟩
  pieces := List.replicate 5 pathPieces
  seams := []

def output : Clause 5 := compileValid inst input diagram

/-- The example preserves terminality; this is not the nonterminal toy. -/
theorem terminal : TerminalRank.TerminalFinals inst := by
  decide +kernel

theorem original_witness : Witness inst [true, false, true, false] := by
  apply (witnessCheck_correct inst _).mp
  decide +kernel

theorem input_weight : clauseWeight input = 17 := by
  decide +kernel

theorem singleton_weight : weight [input] = 17 := by
  decide +kernel

theorem exact_budget : RankQueryCoverage.budget input =
    { groups := 33, core := 351, perAtom := 70,
      seamEntries := 1155, scalar := 470 } := by
  rfl

/-- All enumeration premises are checked against the unchanged Bounded. -/
theorem diagram_bounded : Bounded input (RankQueryCoverage.budget input) diagram := by
  unfold Bounded
  decide +kernel

/-- All compileDiagram guards pass, including seams and endpoint controls. -/
theorem diagram_valid : validDiagram inst input diagram = true := by
  decide +kernel

theorem active_count : (itemsAt inst input diagram 0).length = 175 := by
  decide +kernel

theorem interval_size : (intervalAtom inst input diagram 0).observer.size =
    30 * 2 ^ 175 := by
  decide +kernel

theorem output_vars : output.vars = 4 := by rfl

theorem output_atoms : output.atoms.length = 3 := by
  decide +kernel

theorem output_weight : clauseWeight output = 12 + 30 * 2 ^ 175 := by
  decide +kernel

/-- Exact membership is proved by the membership theorem, not enumeration. -/
theorem output_mem : output ∈ preimage inst RankQueryCoverage.budget [input] := by
  simp only [preimage, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  apply (mem_preimageClause inst input (RankQueryCoverage.budget input) output).mpr
  refine ⟨diagram, diagram_bounded, ?_⟩
  simp only [compileDiagram, diagram_valid, Bool.true_eq, if_true, output]

/-- A strict exact integer comparison, with no floating-point estimates. -/
theorem exceeds_old_bound : closureBound 5 (weight [input]) < clauseWeight output := by
  rw [singleton_weight, output_weight]
  decide +kernel

/-- The concrete compiler cannot satisfy the original bundled contract. -/
theorem not_closureFor : ¬ ClosureFor inst (preimage inst RankQueryCoverage.budget) := by
  intro h
  exact (Nat.not_le_of_lt exceeds_old_bound) (h.2 [input] output output_mem)

/-- A terminal instance refutes the universal claim about this concrete map.
This does not refute ClosureStatement, which existentially chooses a map. -/
theorem terminal_counterexample :
    ∃ I : Instance 5, TerminalRank.TerminalFinals I ∧
      ¬ ClosureFor I (preimage I RankQueryCoverage.budget) :=
  ⟨inst, terminal, not_closureFor⟩

end Subtail.RankQueryWeightCounterexample
