import Subtail.CanonicalModel
import Subtail.StackReachability

/-!
Executable satisfiability and supplied-address separation, linked to the actual
arbitrary-tree canonical semantics. This does not decide existence of an
unsupplied separating address, and does not assume the terminal rank theorem.
-/
namespace Subtail
namespace CanonicalReachability
open TreeSemantics CanonicalModel StackSummary StackReachability

/-- Exactly the five propagation rules of the already formalized semantics. -/
def systemOf (C : List (Constraint n)) : System n where
  eps p q := decide (Constraint.leq p q ∈ C)
  push a p q := if a then decide (∃ l, Constraint.lower l p q ∈ C)
    else decide (∃ r, Constraint.lower p r q ∈ C)
  pop a p q := if a then decide (∃ l, Constraint.upper p l q ∈ C)
    else decide (∃ r, Constraint.upper p q r ∈ C)

@[simp] theorem eps_spec (C : List (Constraint n)) (p q) :
    (systemOf C).eps p q = true ↔ Constraint.leq p q ∈ C := by simp [systemOf]
@[simp] theorem push_left_spec (C : List (Constraint n)) (p q) :
    (systemOf C).push false p q = true ↔ ∃ r, Constraint.lower p r q ∈ C := by
  simp [systemOf]
@[simp] theorem push_right_spec (C : List (Constraint n)) (p q) :
    (systemOf C).push true p q = true ↔ ∃ l, Constraint.lower l p q ∈ C := by
  simp [systemOf]
@[simp] theorem pop_left_spec (C : List (Constraint n)) (p q) :
    (systemOf C).pop false p q = true ↔ ∃ r, Constraint.upper p q r ∈ C := by
  simp [systemOf]
@[simp] theorem pop_right_spec (C : List (Constraint n)) (p q) :
    (systemOf C).pop true p q = true ↔ ∃ l, Constraint.upper p l q ∈ C := by
  simp [systemOf]

theorem step_preserves_derived {C : List (Constraint n)} {S : Seeds n}
    {c d : Config n} (hd : Derived C S c.1 c.2) (hs : Step (systemOf C) c d) :
    Derived C S d.1 d.2 := by
  cases hs with
  | eps h => exact Derived.leq ((eps_spec _ _ _).mp h) hd
  | @push a p q w h =>
    cases a with
    | false =>
      obtain ⟨r,hr⟩ := (push_left_spec C p q).mp h
      exact Derived.pushLeft hr hd
    | true =>
      obtain ⟨l,hl⟩ := (push_right_spec C p q).mp h
      exact Derived.pushRight hl hd
  | @pop a p q w h =>
    cases a with
    | false =>
      obtain ⟨r,hr⟩ := (pop_left_spec C p q).mp h
      exact Derived.popLeft hr hd
    | true =>
      obtain ⟨l,hl⟩ := (pop_right_spec C p q).mp h
      exact Derived.popRight hl hd

theorem reaches_preserves_derived {C : List (Constraint n)} {S : Seeds n}
    {c d : Config n} (h : Reaches (systemOf C) c d) :
    Derived C S c.1 c.2 -> Derived C S d.1 d.2 := by
  induction h with
  | refl => exact id
  | tail _ hs ih => intro hd; exact step_preserves_derived (ih hd) hs

theorem derived_iff_reaches (C : List (Constraint n)) (S : Seeds n) (q : Fin n) (w : Word) :
    Derived C S q w ↔ ∃ p u, S p u ∧ Reaches (systemOf C) (p,u) (q,w) := by
  constructor
  · intro h
    induction h with
    | @seed q w h => exact ⟨q,w,h,.refl⟩
    | leq hc _ ih =>
      obtain ⟨p,u,hs,hr⟩ := ih
      exact ⟨p,u,hs,.tail hr (.eps ((eps_spec _ _ _).mpr hc))⟩
    | popLeft hc _ ih =>
      obtain ⟨p,u,hs,hr⟩ := ih
      exact ⟨p,u,hs,.tail hr (.pop ((pop_left_spec _ _ _).mpr ⟨_,hc⟩))⟩
    | popRight hc _ ih =>
      obtain ⟨p,u,hs,hr⟩ := ih
      exact ⟨p,u,hs,.tail hr (.pop ((pop_right_spec _ _ _).mpr ⟨_,hc⟩))⟩
    | pushLeft hc _ ih =>
      obtain ⟨p,u,hs,hr⟩ := ih
      exact ⟨p,u,hs,.tail hr (.push ((push_left_spec _ _ _).mpr ⟨_,hc⟩))⟩
    | pushRight hc _ ih =>
      obtain ⟨p,u,hs,hr⟩ := ih
      exact ⟨p,u,hs,.tail hr (.push ((push_right_spec _ _ _).mpr ⟨_,hc⟩))⟩
  · rintro ⟨p,u,hs,hr⟩
    exact reaches_preserves_derived hr (Derived.seed hs)

def seedPred (seeds : List (Config n)) : Seeds n := fun p u => (p,u) ∈ seeds

def derivedCheck (C : List (Constraint n)) (seeds : List (Config n)) (q : Fin n) (w : Word) : Bool :=
  seeds.any fun c => reachesCheck (systemOf C) c.1 c.2 q w

@[simp] theorem derivedCheck_correct (C : List (Constraint n)) (seeds : List (Config n)) (q : Fin n) (w : Word) :
    derivedCheck C seeds q w = true ↔ Derived C (seedPred seeds) q w := by
  rw [derived_iff_reaches]
  constructor
  · intro h
    obtain ⟨c,hc,hr⟩ := List.any_eq_true.mp h
    exact ⟨c.1,c.2,hc,(reachesCheck_correct _ _ _ _ _).mp hr⟩
  · rintro ⟨p,u,hs,hr⟩
    apply List.any_eq_true.mpr
    exact ⟨(p,u),hs,(reachesCheck_correct _ _ _ _ _).mpr hr⟩

/-- No reachable stack at any denied control, with arbitrary output length. -/
def safeCheck (C : List (Constraint n)) (seeds : List (Config n)) : Bool :=
  (List.finRange n).all fun q =>
    if decide (Constraint.denial q ∈ C) then
      !(seeds.any fun c => controlReachCheck (systemOf C) c.1 c.2 q)
    else true

@[simp] theorem safeCheck_correct (C : List (Constraint n)) (seeds : List (Config n)) :
    safeCheck C seeds = true ↔ AvoidsDenials C (seedPred seeds) := by
  constructor
  · intro h q hq w hd
    have hh := List.all_eq_true.mp h q (List.mem_finRange q)
    obtain ⟨p,u,hseed,hr⟩ := (derived_iff_reaches _ _ _ _).mp hd
    have hb : (seeds.any fun c => controlReachCheck (systemOf C) c.1 c.2 q) = true := by
      apply List.any_eq_true.mpr
      exact ⟨(p,u),hseed,(controlReachCheck_correct _ _ _ _).mpr ⟨w,hr⟩⟩
    have hden : Constraint.denial q ∈ C := hq
    simpa [hden,hb] using hh
  · intro h
    apply List.all_eq_true.mpr
    intro q _
    by_cases hq : Constraint.denial q ∈ C
    · have hn : (seeds.any fun c => controlReachCheck (systemOf C) c.1 c.2 q) = false := by
        cases hb : seeds.any (fun c => controlReachCheck (systemOf C) c.1 c.2 q) with
        | false => rfl
        | true =>
          obtain ⟨c,hc,hr⟩ := List.any_eq_true.mp hb
          obtain ⟨w,hw⟩ := (controlReachCheck_correct _ _ _ _).mp hr
          exact False.elim (h q hq w ((derived_iff_reaches _ _ _ _).mpr ⟨c.1,c.2,hc,hw⟩))
      simp [hq,hn]
    · simp [hq]

def forcedList (C : List (Constraint n)) : List (Config n) :=
  ((List.finRange n).filter fun q => decide (∃ l r, Constraint.lower l r q ∈ C)).map
    fun q => (q,[])

@[simp] theorem forcedList_spec (C : List (Constraint n)) (q : Fin n) (w : Word) :
    (q,w) ∈ forcedList C ↔ forcedSeeds C q w := by
  simp [forcedList,forcedSeeds,Forced,List.mem_map,eq_comm,and_left_comm,and_assoc]

theorem forcedList_pred (C : List (Constraint n)) :
    seedPred (forcedList C) = forcedSeeds C := by
  funext q w
  exact propext (forcedList_spec C q w)

def pathList (C : List (Constraint n)) (a : Fin n) (w : Word) : List (Config n) :=
  forcedList C ++ (List.range (w.length+1)).map fun i => (a,w.take i)

@[simp] theorem pathList_spec (C : List (Constraint n)) (a : Fin n) (pi : Word) (q : Fin n) (w : Word) :
    (q,w) ∈ pathList C a pi ↔ pathSeeds C a pi q w := by
  simp only [pathList,List.mem_append,forcedList_spec,pathSeeds]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨i,hi,he⟩ := List.mem_map.mp h
    have hq := (Prod.mk.inj he).1
    have hw := (Prod.mk.inj he).2
    exact ⟨hq.symm,hw ▸ List.take_prefix i pi⟩
  · rintro ⟨rfl,z,rfl⟩
    apply List.mem_map.mpr
    refine ⟨w.length,?_,?_⟩
    · simp only [List.mem_range,List.length_append]
      omega
    · simp

theorem pathList_pred (C : List (Constraint n)) (a : Fin n) (w : Word) :
    seedPred (pathList C a w) = pathSeeds C a w := by
  funext q u
  exact propext (pathList_spec C a w q u)

/-- Total executable satisfiability for finite normalized constraints. -/
def satCheck (C : List (Constraint n)) : Bool := safeCheck C (forcedList C)

@[simp] theorem satCheck_correct (C : List (Constraint n)) :
    satCheck C = true ↔ Satisfiable C := by
  rw [satCheck,safeCheck_correct,forcedList_pred]
  exact (satisfiable_iff_forced_safe C).symm

/-- Exact decision for one SUPPLIED finite separating address, not its existence. -/
def separationCheck (C : List (Constraint n)) (a b : Fin n) (w : Word) : Bool :=
  safeCheck C (pathList C a w) && !(derivedCheck C (pathList C a w) b w)

@[simp] theorem separationCheck_correct (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    separationCheck C a b w = true ↔
      AvoidsDenials C (pathSeeds C a w) ∧ ¬ Derived C (pathSeeds C a w) b w := by
  simp [separationCheck,Bool.eq_false_iff,pathList_pred]

/-- A supplied finite address separates exactly when some ARBITRARY valuation
satisfying C distinguishes the two variables at that very address. -/
theorem separationCheck_iff_countermodel (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    separationCheck C a b w = true ↔
      ∃ rho, Models C rho ∧ (rho a).nodes w ∧ ¬ (rho b).nodes w := by
  rw [separationCheck_correct]
  constructor
  · rintro ⟨hs,hb⟩
    refine ⟨canonical C a w,?_,canonical_contains C a w,hb⟩
    exact closure_models (pathSeeds_closed C a w) (pathSeeds_roots C a w) hs
  · rintro ⟨rho,hm,ha,hb⟩
    refine ⟨avoids_of_model hm (pathSeeds_in_model hm ha),?_⟩
    intro hd
    exact hb (derived_sound hm (pathSeeds_in_model hm ha) hd)

/-- The remaining unbounded word choice is explicit, not silently decided. -/
theorem not_entails_iff_exists_check (C : List (Constraint n)) (a b : Fin n) :
    ¬ Entails C a b ↔ ∃ w, separationCheck C a b w = true := by
  simp only [separationCheck_correct]
  exact not_entails_iff_canonical C a b

end CanonicalReachability
end Subtail
