import Subtail.RankQueryEnumeration

/-! Checked boundary fixtures for the finite syntax enumerator (#28).
No bounded search result here is a general negative BorderAvoid answer. -/
namespace Subtail
namespace RankQueryEnumerationAudit
open RankQuery RankQueryCompiler RankQueryEnumeration

/-- Empty alphabets still have the one empty list. -/
theorem empty_alphabet_zero : exactLists ([] : List Nat) 0 = [[]] := rfl

theorem empty_alphabet_positive (n : Nat) :
    exactLists ([] : List Nat) (n + 1) = [] := rfl

/-- Duplicates are permitted; enumeration is not a quotient. -/
theorem duplicates_preserved : (exactLists [0, 0] 2).length = 4 := by decide

theorem piece_zero : pieces 0 = [] := rfl

theorem piece_one_count : (pieces 1).length = 20 := by decide

theorem seam_one_count : (seams 1).length = 1 := by decide

theorem masks_two_count : (masks 2).length = 4 := by decide

theorem colours_one_count : (colours 1).length = 24 := by decide

/-- Zero marks exclude every diagram, whatever all other budgets are. -/
theorem zero_groups_impossible (c : Clause k) (b : Limits) (h : b.groups = 0)
    (D : Diagram k) : ¬ D ∈ diagrams c b := by
  intro hD
  have hb := (mem_diagrams c b D).mp hD
  have hp := hb.1
  have hu := hb.2.1
  omega

/-- Out-of-range source/control fields cannot silently use compiler fallbacks. -/
theorem out_of_range_piece (n : Nat) (p : Piece) (h : n <= p.lc) :
    ¬ p ∈ pieces n := by
  intro hp
  have hb := (mem_pieces n p).mp hp
  have hl := hb.2.2.1
  omega

/-- An atom count mismatch is outside the explicit structural contract. -/
theorem wrong_atom_count (c : Clause k) (b : Limits) (D : Diagram k)
    (h : D.pieces.length ≠ c.atoms.length) : ¬ D ∈ diagrams c b := by
  intro hD
  have hb := (mem_diagrams c b D).mp hD
  exact h hb.2.2.2.2.2.2.2.1

end RankQueryEnumerationAudit
end Subtail
