import Subtail.RankQuery

/-!
# Finishing-query path facts

A018/C080 stage-5 support. This module isolates semantic facts carried by
`finishObserver` runs. It does not assume ClosureFor and does not claim the
full finishing-query/Witness equivalence.
-/
namespace Subtail
namespace RankQueryFinishFacts

open RankQuery

variable {k : Nat}

/-- Membership in a finishing-observer move forces a K edge and records exactly
one safe reverse automaton step. -/
theorem finish_move_facts (I : Instance k) {q p : Fin k}
    {c d : Colour k} {l : Label}
    (h : p ∈ (finishObserver I q).move q c l d) :
    ∃ a : Bool, l = .K a ∧ d.isEnd = false ∧
      step I p a = some q ∧ I.bad.get p = false ∧
      (I.flags.get p).get p = false ∧ d.mask.get p = false := by
  cases l with
  | F => simp [finishObserver] at h
  | S => simp [finishObserver] at h
  | K a =>
    by_cases he : d.isEnd
    · simp [finishObserver, he] at h
    · have hm := List.mem_filter.mp h
      simp only [finishObserver, he, if_false] at hm
      have hp := hm.2
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
      exact ⟨a, rfl, by simpa using he, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

/-- One finishing step must be a K edge; its destination control is the safe
predecessor state recorded by the observer. -/
theorem finish_step_facts (I : Instance k) {q0 : Fin k}
    {G : Graph k} {x y : Node G (finishObserver I q0)}
    (h : Step G (finishObserver I q0) x y) :
    ∃ a : Bool, G.edge x.1 (.K a) = some y.1 ∧
      (G.colour y.1).isEnd = false ∧
      step I y.2 a = some x.2 ∧ I.bad.get y.2 = false ∧
      (I.flags.get y.2).get y.2 = false ∧
      (G.colour y.1).mask.get y.2 = false := by
  obtain ⟨l, he, hm, -⟩ := h
  obtain ⟨a, hl, hend, hstep, hbad, hdiag, hmask⟩ :=
    finish_move_facts I hm
  subst l
  exact ⟨a, he, hend, hstep, hbad, hdiag, hmask⟩

/-- Allowed finishing nodes are precisely non-end graph vertices. -/
theorem finish_allowed_iff (I : Instance k) (q0 : Fin k)
    (G : Graph k) (x : Node G (finishObserver I q0)) :
    Allowed G (finishObserver I q0) x ↔ (G.colour x.1).isEnd = false := by
  simp [Allowed, finishObserver]

/-- The endpoint of every run is allowed. -/
theorem allowed_target_of_run {G : Graph k} {O : Observer k}
    {x y : Node G O} (h : Run G O x y) : Allowed G O y := by
  induction h with
  | refl hx => exact hx
  | step _ hs _ => exact hs.2.2.2

/-- Both endpoints of a finishing run lie away from the graph endpoint. -/
theorem finish_run_notEnd (I : Instance k) (q0 : Fin k)
    {G : Graph k} {x y : Node G (finishObserver I q0)}
    (h : Run G (finishObserver I q0) x y) :
    (G.colour x.1).isEnd = false ∧ (G.colour y.1).isEnd = false := by
  exact ⟨(finish_allowed_iff I q0 G x).mp (allowed_of_run G _ h),
    (finish_allowed_iff I q0 G y).mp (allowed_target_of_run h)⟩

end RankQueryFinishFacts
end Subtail
