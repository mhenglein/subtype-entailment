import Subtail.TerminalRealizationModel

/-! Kernel-visible statements and adversarial fixtures for the direct proof. -/
#print axioms Subtail.TerminalRealization.constraints
#print axioms Subtail.TerminalRealization.separation_implies_witness
#print axioms Subtail.TerminalRealization.realization_satisfiable
#print axioms Subtail.TerminalRealization.witness_iff_separating
#print axioms Subtail.TerminalRealization.not_entails_iff_witness

#check Subtail.TerminalRealization.realization_satisfiable
#check Subtail.TerminalRealization.witness_iff_separating
#check Subtail.TerminalRealization.not_entails_iff_witness

namespace Subtail.TerminalRealization.Audit
open TreeSemantics

def lone (accept bad flag : Bool) : Instance 1 where
  initial := 0
  transitions := Vector.ofFn (fun _ => (none, none))
  bad := Vector.ofFn (fun _ => bad)
  final := Vector.ofFn (fun _ => accept)
  flags := Vector.ofFn (fun _ => Vector.ofFn (fun _ => flag))

theorem empty_yes : Witness (lone true false false) [] :=
  (witnessCheck_correct _ _).mp (by decide)

theorem no_of_check (I : Instance k) (w : Word) (h : witnessCheck I w = false) :
    ¬ Witness I w := by
  intro hw
  have hh := (witnessCheck_correct I w).mpr hw
  simp [h] at hh

theorem nonfinal_sink_no : ¬ Witness (lone false false false) [] :=
  no_of_check _ _ (by decide)
theorem bad_initial_no : ¬ Witness (lone true true false) [] :=
  no_of_check _ _ (by decide)
theorem diagonal_no : ¬ Witness (lone true false true) [] :=
  no_of_check _ _ (by decide)

theorem empty_separation : ∃ rho,
    Models (constraints (lone true false false)) rho ∧
    (rho (a (0 : Fin 1))).nodes [] ∧ ¬ (rho (v (0 : Fin 1))).nodes [] :=
  (witness_iff_separating _ (by unfold TerminalFinal; decide) []).mp empty_yes

theorem nonfinal_sink_clauses : constraints (lone false false false) =
    ([.denial 2, .upper 0 2 2, .lower 2 2 1] : List (Constraint 3)) := by decide

/-- Reversing the one flag must change the word test. -/
def edge (backward : Bool) : Instance 2 where
  initial := 0
  transitions := Vector.ofFn (fun q => if q.val == 0 then (some 1, none) else (none, none))
  bad := Vector.ofFn (fun _ => false)
  final := Vector.ofFn (fun q => q.val == 1)
  flags := Vector.ofFn (fun p => Vector.ofFn (fun q =>
    if backward then p.val == 1 && q.val == 0 else p.val == 0 && q.val == 1))

theorem reverse_flag_yes : Witness (edge true) [false] :=
  (witnessCheck_correct _ _).mp (by decide)
theorem forward_flag_no : ¬ Witness (edge false) [false] :=
  no_of_check _ _ (by decide)
theorem undefined_transition_no : ¬ Witness (edge true) [true, false] :=
  no_of_check _ _ (by decide)

theorem reverse_flag_separation : ∃ rho,
    Models (constraints (edge true)) rho ∧
    (rho (a (0 : Fin 2))).nodes [false] ∧ ¬ (rho (v (0 : Fin 2))).nodes [false] :=
  (witness_iff_separating _ (by unfold TerminalFinal; decide) [false]).mp reverse_flag_yes

theorem forward_flag_no_separation : ¬ ∃ rho,
    Models (constraints (edge false)) rho ∧
    (rho (a (0 : Fin 2))).nodes [false] ∧ ¬ (rho (v (0 : Fin 2))).nodes [false] := by
  intro h
  exact forward_flag_no ((witness_iff_separating _
    (by unfold TerminalFinal; decide) [false]).mpr h)

theorem reverse_flag_clauses : constraints (edge true) =
    ([.denial 4, .upper 0 1 4, .lower 3 4 2, .upper 1 4 4, .leq 1 2] :
      List (Constraint 5)) := by decide

/-- The source state loops on 0, and 1 exits to the accepting terminal. -/
def spine : Instance 2 where
  initial := 0
  transitions := Vector.ofFn (fun q => if q.val == 0 then (some 0, some 1) else (none, none))
  bad := Vector.ofFn (fun _ => false)
  final := Vector.ofFn (fun q => q.val == 1)
  flags := Vector.ofFn (fun _ => Vector.ofFn (fun _ => false))

theorem spine_terminal : TerminalFinal spine := by unfold TerminalFinal; decide
theorem spine_witness : Witness spine [false, false, false, true] :=
  (witnessCheck_correct _ _).mp (by decide)
theorem spine_satisfiable : Satisfiable (constraints spine) :=
  realization_satisfiable spine spine_terminal

/-- Every model, not just our baseline model, has an unbounded lower 0-spine. -/
theorem spine_forced (rho : Valuation 5) (hm : Models (constraints spine) rho)
    (N : Nat) : (rho (v (0 : Fin 2))).nodes (List.replicate N false) := by
  have h := (models_iff_laws spine rho).mp hm
  induction N with
  | zero => exact (h.2 0).2.1 (by decide) [] (product_root _ _)
  | succ N ih =>
    have hs : step spine 0 false = some 0 := by decide
    have hc : (rho (child v (step spine 0 false))).nodes (List.replicate N false) := by
      simpa [child, hs] using ih
    simpa [List.replicate_succ] using lower_letter h 0 (by decide) false _ hc

theorem spine_unbounded (rho : Valuation 5) (hm : Models (constraints spine) rho)
    (N : Nat) : ∃ w, (rho (v (0 : Fin 2))).nodes w ∧ N < w.length := by
  exact ⟨List.replicate (N + 1) false, spine_forced rho hm (N + 1), by simp⟩

end Subtail.TerminalRealization.Audit
