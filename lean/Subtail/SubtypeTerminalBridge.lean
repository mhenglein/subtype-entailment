import Subtail.SummaryAutomaton
import Subtail.AbsorbingTerminal
import Subtail.RankQueryDecision

/-!
# The exact remaining decision boundary for normalized subtype entailment

This file connects independently checked components. It supplies no
infinite-continuation decision or finite-expression normalization assumption.
-/
namespace Subtail.SubtypeTerminalBridge

open TreeSemantics SummaryAutomaton AbsorbingTerminal RankQueryDecision

variable {n : Nat}

/-- The constructed instance meets the strong, all-state absorption contract. -/
theorem summary_absorbing (C : List (Constraint n)) (a b : Fin n) :
    Absorbing (summaryInstance C a b) := by
  intro f hf x q hq
  rw [summary_step] at hq
  have he := Option.some.inj hq
  subst q
  exact summary_absorbs C a b f x hf

/-- The safe terminal branch can already be decided with no further hypothesis. -/
theorem terminal_summary_check (C : List (Constraint n)) (a b : Fin n) :
    terminalWitnessCheck (terminalize (summaryInstance C a b)) = true ↔
      ∃ w, Witness (terminalize (summaryInstance C a b)) w :=
  terminalWitnessCheck_correct _ (terminalize_terminal _)

/-- Exact normalized entailment boundary. The infinite branch is still a Prop,
not an assumed or noncomputable decision procedure. -/
theorem not_entails_iff_infinite_or_terminal (C : List (Constraint n)) (a b : Fin n) :
    ¬ Entails C a b ↔
      InfWitness (summaryInstance C a b) ∨
        terminalWitnessCheck (terminalize (summaryInstance C a b)) = true := by
  rw [not_entails_iff_witness, c031 _ (summary_absorbing C a b), terminal_summary_check]

end Subtail.SubtypeTerminalBridge

