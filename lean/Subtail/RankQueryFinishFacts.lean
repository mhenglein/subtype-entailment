import Subtail.RankQuery

/-!
# Finishing-query path facts

A018/C080 stage-5 support. These facts use the existing finishObserver and
literal prefixGraph, with no assumed closure theorem. A finishing continuation
must avoid another full return to the reference. Arbitrary safe completion is
not the same property.
-/
namespace Subtail
namespace RankQueryFinishFacts

open RankQuery

variable {k : Nat}

/-- Exact move contract. The observer's initial control q0 is independent of
its current control q. A move requires target safety, not source permission. -/
theorem finish_move_iff (I : Instance k) (q0 q p : Fin k)
    (c d : Colour k) (l : Label) :
    p ∈ (finishObserver I q0).move q c l d ↔
    ∃ a : Bool, l = .K a ∧ d.isEnd = false ∧
      step I p a = some q ∧ I.bad.get p = false ∧
      (I.flags.get p).get p = false ∧ d.mask.get p = false := by
  constructor
  · intro h
    cases l with
    | F =>
      change p ∈ ([] : List (Fin k)) at h
      cases h
    | S =>
      change p ∈ ([] : List (Fin k)) at h
      cases h
    | K a =>
      cases hd : d.isEnd with
      | true =>
        simp only [finishObserver, hd, if_true] at h
        cases h
      | false =>
        simp only [finishObserver, hd, Bool.false_eq_true, if_false] at h
        have hp := (List.mem_filter.mp h).2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
        obtain ⟨⟨⟨hs, hb⟩, hf⟩, hm⟩ := hp
        exact ⟨a, rfl, rfl, hs, hb, hf, hm⟩
  · rintro ⟨a, rfl, hd, hs, hb, hf, hm⟩
    simp only [finishObserver, hd, Bool.false_eq_true, if_false]
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange p, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
    exact ⟨⟨⟨hs, hb⟩, hf⟩, hm⟩

/-- The original one-current-control interface, retained as a corollary. -/
theorem finish_move_facts (I : Instance k) {q p : Fin k}
    {c d : Colour k} {l : Label}
    (h : p ∈ (finishObserver I q).move q c l d) :
    ∃ a : Bool, l = .K a ∧ d.isEnd = false ∧
      step I p a = some q ∧ I.bad.get p = false ∧
      (I.flags.get p).get p = false ∧ d.mask.get p = false :=
  (finish_move_iff I q q p c d l).mp h

/-- One finishing step is exactly a K edge with the target's safety checks. -/
theorem finish_step_iff (I : Instance k) (q0 : Fin k)
    (G : Graph k) (x y : Node G (finishObserver I q0)) :
    Step G (finishObserver I q0) x y ↔
    ∃ a : Bool, G.edge x.1 (.K a) = some y.1 ∧
      (G.colour y.1).isEnd = false ∧
      step I y.2 a = some x.2 ∧ I.bad.get y.2 = false ∧
      (I.flags.get y.2).get y.2 = false ∧
      (G.colour y.1).mask.get y.2 = false := by
  constructor
  · rintro ⟨l, he, hm, _⟩
    obtain ⟨a, rfl, hend, hs, hb, hf, hmask⟩ :=
      (finish_move_iff I q0 x.2 y.2 (G.colour x.1) (G.colour y.1) l).mp hm
    exact ⟨a, he, hend, hs, hb, hf, hmask⟩
  · rintro ⟨a, he, hend, hs, hb, hf, hmask⟩
    refine ⟨.K a, he, ?_, ?_⟩
    · exact (finish_move_iff I q0 x.2 y.2 (G.colour x.1) (G.colour y.1) (.K a)).mpr
        ⟨a, rfl, hend, hs, hb, hf, hmask⟩
    · change (!(G.colour y.1).isEnd) = true
      rw [hend]
      rfl

/-- Original step interface, retained without a source-permission assumption. -/
theorem finish_step_facts (I : Instance k) {q0 : Fin k}
    {G : Graph k} {x y : Node G (finishObserver I q0)}
    (h : Step G (finishObserver I q0) x y) :
    ∃ a : Bool, G.edge x.1 (.K a) = some y.1 ∧
      (G.colour y.1).isEnd = false ∧
      step I y.2 a = some x.2 ∧ I.bad.get y.2 = false ∧
      (I.flags.get y.2).get y.2 = false ∧
      (G.colour y.1).mask.get y.2 = false :=
  (finish_step_iff I q0 G x y).mp h

/-- Allowed finishing nodes are precisely non-end graph vertices. -/
theorem finish_allowed_iff (I : Instance k) (q0 : Fin k)
    (G : Graph k) (x : Node G (finishObserver I q0)) :
    Allowed G (finishObserver I q0) x ↔ (G.colour x.1).isEnd = false := by
  simp only [Allowed, finishObserver, Bool.not_eq_true']

/-- The target of a run is allowed; Step's existential is unpacked explicitly. -/
theorem allowed_target_of_run {G : Graph k} {O : Observer k}
    {x y : Node G O} (h : Run G O x y) : Allowed G O y := by
  induction h with
  | refl hx => exact hx
  | step _ hs _ =>
    obtain ⟨_, _, _, hy⟩ := hs
    exact hy

/-- Both endpoints of a finishing run lie away from the graph endpoint. -/
theorem finish_run_notEnd (I : Instance k) (q0 : Fin k)
    {G : Graph k} {x y : Node G (finishObserver I q0)}
    (h : Run G (finishObserver I q0) x y) :
    (G.colour x.1).isEnd = false ∧ (G.colour y.1).isEnd = false := by
  exact ⟨(finish_allowed_iff I q0 G x).mp (allowed_of_run G _ h),
    (finish_allowed_iff I q0 G y).mp (allowed_target_of_run h)⟩

end RankQueryFinishFacts
end Subtail
