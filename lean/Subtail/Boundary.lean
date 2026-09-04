import Subtail.Basic
import Subtail.SandwichPredicates

namespace Subtail

/-- The empty and full borders, together with the defined safe run and endpoint. -/
def BoundaryCondition (I : Instance k) (w : Word) : Prop :=
  (∀ i, i ≤ w.length → safeCheck I (stateAt I w i) = true) ∧
  finalCheck I (stateAt I w w.length) = true ∧
  ∀ i, i ≤ w.length →
    unflaggedCheck I (stateAt I w i) (stateAt I w i) = true ∧
    unflaggedCheck I (stateAt I w i) (stateAt I w w.length) = true

/-- Only proper nonempty suffix agreements remain after the boundary checks. -/
def ProperCondition (I : Instance k) (w : Word) : Prop :=
  ∀ j, j < w.length → ∀ i, i < j → Agrees w i j →
    unflaggedCheck I (stateAt I w i) (stateAt I w j) = true

def boundaryCheck (I : Instance k) (w : Word) : Bool :=
  (List.range (w.length + 1)).all (fun i => safeCheck I (stateAt I w i)) &&
  finalCheck I (stateAt I w w.length) &&
  (List.range (w.length + 1)).all (fun i =>
    unflaggedCheck I (stateAt I w i) (stateAt I w i) &&
    unflaggedCheck I (stateAt I w i) (stateAt I w w.length))

theorem boundaryCheck_correct (I : Instance k) (w : Word) :
    boundaryCheck I w = true ↔ BoundaryCondition I w := by
  simp [boundaryCheck, BoundaryCondition, List.all_eq_true, List.mem_range,
    Nat.lt_succ_iff, and_assoc]

theorem witness_iff_boundary_proper (I : Instance k) (w : Word) :
    Witness I w ↔ BoundaryCondition I w ∧ ProperCondition I w := by
  constructor
  · intro hw
    refine ⟨⟨hw.1, hw.2.1, ?_⟩, ?_⟩
    · intro i hi
      exact ⟨hw.2.2 i hi i (by omega) (List.prefix_refl _),
        hw.2.2 w.length (by omega) i hi (by simp [Agrees])⟩
    · intro j hj i hi ha
      exact hw.2.2 j (by omega) i (by omega) ha
  · rintro ⟨hb, hp⟩
    refine ⟨hb.1, hb.2.1, ?_⟩
    intro j hj i hi ha
    by_cases he : j = w.length
    · subst j
      exact (hb.2.2 i hi).2
    · by_cases hd : i = j
      · subst i
        exact (hb.2.2 j hj).1
      · exact hp j (by omega) i (by omega) ha

/-- Fixing the final state turns every boundary flag into a forbidden state. -/
def safeInFinalSlice (I : Instance k) (f : Fin k) (q : Option (Fin k)) : Bool :=
  safeCheck I q && unflaggedCheck I q q && unflaggedCheck I q (some f)

def FinalSlice (I : Instance k) (w : Word) (f : Fin k) : Prop :=
  (∀ i, i ≤ w.length → safeInFinalSlice I f (stateAt I w i) = true) ∧
  stateAt I w w.length = some f ∧ I.final.get f = true

theorem safeInFinalSlice_some (I : Instance k) (f q : Fin k) :
    safeInFinalSlice I f (some q) = true ↔
      I.bad.get q = false ∧ (I.flags.get q).get q = false ∧
        (I.flags.get q).get f = false := by
  simp [safeInFinalSlice, safeCheck, unflaggedCheck, and_assoc]

theorem boundary_iff_finalSlice (I : Instance k) (w : Word) :
    BoundaryCondition I w ↔ ∃ f, FinalSlice I w f := by
  constructor
  · intro hb
    cases he : stateAt I w w.length with
    | none =>
      have hf := hb.2.1
      simp [he, finalCheck] at hf
    | some f =>
      refine ⟨f, ?_, he, ?_⟩
      · intro i hi
        have hs := hb.1 i hi
        have hflags := hb.2.2 i hi
        simp [safeInFinalSlice, ← he, hs, hflags.1, hflags.2]
      · simpa [he, finalCheck] using hb.2.1
  · rintro ⟨f, hs, he, hf⟩
    have hparts : ∀ i, i ≤ w.length →
        safeCheck I (stateAt I w i) = true ∧
        unflaggedCheck I (stateAt I w i) (stateAt I w i) = true ∧
        unflaggedCheck I (stateAt I w i) (stateAt I w w.length) = true := by
      intro i hi
      simpa [safeInFinalSlice, ← he, and_assoc] using hs i hi
    exact ⟨fun i hi => (hparts i hi).1,
      by simpa [he, finalCheck] using hf,
      fun i hi => (hparts i hi).2⟩

theorem witness_iff_finalSlice_proper (I : Instance k) (w : Word) :
    Witness I w ↔ (∃ f, FinalSlice I w f) ∧ ProperCondition I w := by
  rw [witness_iff_boundary_proper, boundary_iff_finalSlice]

theorem boundary_witness_of_length_le_one (I : Instance k) (w : Word)
    (hn : w.length ≤ 1) (hb : BoundaryCondition I w) : Witness I w := by
  apply (witness_iff_boundary_proper I w).mpr
  refine ⟨hb, ?_⟩
  intro j hj i hi
  omega

theorem necessary_zero_iff_boundary (I : Instance k) (w : Word) :
    Necessary I w 0 0 ↔ BoundaryCondition I w := by
  constructor
  · intro hn
    refine ⟨hn.1.1, hn.1.2, ?_⟩
    intro i hi
    exact ⟨hn.2 i hi i (by omega) (List.prefix_refl _) (by omega),
      hn.2 w.length (by omega) i hi (by simp [Agrees]) (by omega)⟩
  · intro hb
    refine ⟨⟨hb.1, hb.2.1⟩, ?_⟩
    intro j hj i hi _ hzero
    rcases hzero with he | hd
    · have h : j = w.length := by omega
      subst j
      exact (hb.2.2 i hi).2
    · have h : i = j := by omega
      subst i
      exact (hb.2.2 j hj).1

end Subtail
