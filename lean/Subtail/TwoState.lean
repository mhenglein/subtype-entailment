import Subtail.Boundary

/-!
# Exact witness search for at most two states

For a two-state partial DFA, a safe accepting run can be shortened to the
empty word or to a single letter chosen from the run. This file turns that observation into an
executable decision procedure for the direct `Witness` predicate.
-/

namespace Subtail

/-- If a run reaches a different target and there are at most two states,
some one-letter run from the same start also reaches that target. -/
theorem one_step_to_target_of_two_states
    (I : Instance k) (hk : k ≤ 2) {q f : Fin k} (hq : q ≠ f)
    (xs : Word) (hxs : runFrom I q xs = some f) :
    ∃ a : Bool, runFrom I q [a] = some f := by
  induction xs generalizing q with
  | nil =>
      simp [runFrom] at hxs
      exact False.elim (hq hxs)
  | cons a xs ih =>
      cases hstep : step I q a with
      | none =>
          simp [runFrom, hstep] at hxs
      | some r =>
          have htail : runFrom I r xs = some f := by
            simpa [runFrom, hstep] using hxs
          by_cases hrf : r = f
          · refine ⟨a, ?_⟩
            simp [runFrom, hstep, hrf]
          · have hrq : r = q := by
              apply Fin.ext
              have hqv : q.val < k := q.isLt
              have hrv : r.val < k := r.isLt
              have hfv : f.val < k := f.isLt
              omega
            subst r
            exact ih hq htail

/-- Every witness for an instance with at most two states has a witness of
length at most one. -/
theorem exists_short_witness_two_states
    (I : Instance k) (hk : k ≤ 2) :
    (∃ w, Witness I w) → ∃ w, w.length ≤ 1 ∧ Witness I w := by
  rintro ⟨w, hw⟩
  rcases (witness_iff_finalSlice_proper I w).mp hw with
    ⟨⟨f, hsafe, hend, hfinal⟩, _⟩
  by_cases hqf : I.initial = f
  · have hboundary : BoundaryCondition I [] := by
      apply (boundary_iff_finalSlice I []).mpr
      refine ⟨f, ?_, ?_, hfinal⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst i
        simpa [stateAt, runFrom, hqf] using hsafe 0 (by omega)
      · simp [stateAt, runFrom, hqf]
    exact ⟨[], by decide, boundary_witness_of_length_le_one I [] (by decide)
      hboundary⟩
  · have hrun : runFrom I I.initial (w.take w.length) = some f := by
      simpa [stateAt] using hend
    rcases one_step_to_target_of_two_states I hk hqf (w.take w.length) hrun with
      ⟨a, ha⟩
    have hsafe_initial : safeInFinalSlice I f (some I.initial) = true := by
      simpa [stateAt, runFrom] using hsafe 0 (by omega)
    have hsafe_final : safeInFinalSlice I f (some f) = true := by
      have h := hsafe w.length (by omega)
      rw [hend] at h
      exact h
    have hone : FinalSlice I [a] f := by
      refine ⟨?_, ?_, hfinal⟩
      · intro i hi
        have hi' : i = 0 ∨ i = 1 := by
          simp at hi
          omega
        rcases hi' with rfl | rfl
        · simpa [stateAt, runFrom] using hsafe_initial
        · have hone_state : stateAt I [a] 1 = some f := by
            simpa [stateAt] using ha
          rw [hone_state]
          exact hsafe_final
      · simpa [stateAt] using ha
    have hboundary : BoundaryCondition I [a] :=
      (boundary_iff_finalSlice I [a]).mpr ⟨f, hone⟩
    exact ⟨[a], by simp,
      boundary_witness_of_length_le_one I [a] (by simp) hboundary⟩

/-- Executable exact decision procedure for witness existence when `k ≤ 2`.
The correctness theorem below supplies the state-count condition. -/
def twoStateWitnessCheck (I : Instance k) : Bool :=
  witnessCheck I [] || witnessCheck I [false] || witnessCheck I [true]

theorem twoStateWitnessCheck_correct
    (I : Instance k) (hk : k ≤ 2) :
    twoStateWitnessCheck I = true ↔ ∃ w, Witness I w := by
  constructor
  · intro h
    have h' : (witnessCheck I [] = true ∨
        witnessCheck I [false] = true) ∨ witnessCheck I [true] = true := by
      change ((witnessCheck I [] || witnessCheck I [false]) ||
        witnessCheck I [true]) = true at h
      rw [Bool.or_eq_true, Bool.or_eq_true] at h
      exact h
    rcases h' with h | h
    · rcases h with h | h
      · exact ⟨[], (witnessCheck_correct I []).mp h⟩
      · exact ⟨[false], (witnessCheck_correct I [false]).mp h⟩
    · exact ⟨[true], (witnessCheck_correct I [true]).mp h⟩
  · rintro ⟨w, hw⟩
    rcases exists_short_witness_two_states I hk ⟨w, hw⟩ with
      ⟨v, hvlen, hv⟩
    cases v with
    | nil =>
        have h := (witnessCheck_correct I []).mpr hv
        simp [twoStateWitnessCheck, h]
    | cons a t =>
        have ht : t = [] := by
          cases t with
          | nil => rfl
          | cons b u =>
              simp at hvlen
        subst t
        cases a
        · have h := (witnessCheck_correct I [false]).mpr hv
          simp [twoStateWitnessCheck, h]
        · have h := (witnessCheck_correct I [true]).mpr hv
          simp [twoStateWitnessCheck, h]

end Subtail
