import Subtail.PeriodicRotation

/-! Exact prepend recurrences for the periodic-prefix witness predicate. -/
namespace Subtail.PeriodicGood
open AbsorbingTerminal PeriodicRun PeriodicRotation
variable {k : Nat}

/-- A suffix run starts at its current control; all other instance data stays fixed. -/
def restart (I : Instance k) (p : Fin k) : Instance k := { I with initial := p }

def GoodFrom (I : Instance k) (p : Fin k) (w c : Word) : Prop :=
  PrefixGood (restart I p) w c

theorem step_restart (I : Instance k) (p q : Fin k) (a : Bool) :
    step (restart I p) q a = step I q a := by cases a <;> rfl

theorem runFrom_restart (I : Instance k) (p q : Fin k) (w : Word) :
    runFrom (restart I p) q w = runFrom I q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
    simp only [runFrom, step_restart]
    cases h : step I q a <;> simp [ih]

theorem stateAt_restart (I : Instance k) (p : Fin k) (w : Word) (i : Nat) :
    stateAt (restart I p) w i = runFrom I p (w.take i) := by
  exact runFrom_restart I p p (w.take i)

theorem unflaggedCheck_restart (I : Instance k) (p : Fin k)
    (x y : Option (Fin k)) :
    unflaggedCheck (restart I p) x y = unflaggedCheck I x y := by
  cases x <;> cases y <;> rfl

theorem goodFrom_iff (I : Instance k) (p : Fin k) (w c : Word) :
    GoodFrom I p w c ↔ ∀ i j, i < j → j ≤ w.length →
      PeriodicTail.SameSuffix (prefixStream w c) i j →
      unflaggedCheck I (runFrom I p (w.take i)) (runFrom I p (w.take j)) = true := by
  simp only [GoodFrom, PrefixGood, stateAt_restart, unflaggedCheck_restart]

theorem goodFrom_initial (I : Instance k) (w c : Word) :
    GoodFrom I I.initial w c ↔ PrefixGood I w c := by rfl

theorem goodFrom_nil (I : Instance k) (p : Fin k) (c : Word) :
    GoodFrom I p [] c := by
  rw [goodFrom_iff]
  intro i j hij hj
  simp only [List.length_nil] at hj
  omega

theorem run_take_cons (I : Instance k) {p r : Fin k} {a : Bool}
    (he : step I p a = some r) (w : Word) (i : Nat) :
    runFrom I p ((a::w).take (i+1)) = runFrom I r (w.take i) := by
  simp [runFrom, he]

/-- Prepending preserves every old comparison and adds exactly the comparisons
from the new cut zero. Flags retain their source/target order. -/
theorem goodFrom_cons_iff (I : Instance k) {p r : Fin k} {a : Bool}
    (he : step I p a = some r) (w c : Word) :
    GoodFrom I p (a::w) c ↔ GoodFrom I r w c ∧
      ∀ j, j ≤ w.length →
        PeriodicTail.SameSuffix (prefixStream (a::w) c) 0 (j+1) →
        unflaggedCheck I (some p) (runFrom I r (w.take j)) = true := by
  rw [goodFrom_iff, goodFrom_iff]
  constructor
  · intro h
    constructor
    · intro i j hij hj hs
      have hs' := (sameSuffix_cons_succ_iff w c a i j).mpr hs
      have hg := h (i+1) (j+1) (by omega) (by simp; omega) hs'
      simpa only [run_take_cons I he] using hg
    · intro j hj hs
      have hg := h 0 (j+1) (by omega) (by simp; omega) hs
      simpa only [List.take_zero, runFrom, run_take_cons I he] using hg
  · rintro ⟨hold,hnew⟩ i j hij hj hs
    cases j with
    | zero => omega
    | succ j =>
      have hj' : j ≤ w.length := by simp only [List.length_cons] at hj; omega
      cases i with
      | zero =>
        simpa only [List.take_zero, runFrom, run_take_cons I he] using hnew j hj' hs
      | succ i =>
        have hs' := (sameSuffix_cons_succ_iff w c a i j).mp hs
        simpa only [run_take_cons I he] using hold i j (by omega) hj' hs'

/-- Safe finite runs have the exact one-letter decomposition, including the
safety of their starting cut. -/
theorem safeRun_cons_iff (I : Instance k) (p q : Fin k) (a : Bool) (w : Word) :
    SafeRun I p (a::w) q ↔ safeState I p = true ∧
      ∃ r, step I p a = some r ∧ SafeRun I r w q := by
  constructor
  · intro h
    have hp := (safeCut_zero_iff I p (a::w)).mp (h.2 0 (by simp))
    cases he : step I p a with
    | none =>
      have hr := h.1
      simp [runFrom, he] at hr
    | some r =>
      refine ⟨hp,r,rfl,?_,?_⟩
      · simpa [runFrom,he] using h.1
      · intro i hi
        obtain ⟨s,hs,hsafe⟩ := h.2 (i+1) (by simp; omega)
        exact ⟨s,by simpa only [run_take_cons I he] using hs,hsafe⟩
  · rintro ⟨hp,r,he,hw⟩
    refine ⟨by simpa [runFrom,he] using hw.1, ?_⟩
    intro i hi
    cases i with
    | zero => exact (safeCut_zero_iff I p (a::w)).mpr hp
    | succ i =>
      have hi' : i ≤ w.length := by simp only [List.length_cons] at hi; omega
      obtain ⟨s,hs,hsafe⟩ := hw.2 i hi'
      exact ⟨s,by simpa only [run_take_cons I he] using hs,hsafe⟩

end Subtail.PeriodicGood
