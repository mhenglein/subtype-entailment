import Subtail.TreeSemantics

/-!
# Least canonical models of normalized subtype constraints

Inductive propagation is an exact semantic closure, NOT a bounded search.
All forced roots and all prefixes of a separating path are present. The final
characterization includes unsatisfiable inputs without assuming satisfiability.
Finite effective regular saturation is a separate, still-unformalized interface.
-/
namespace Subtail
namespace CanonicalModel
open TreeSemantics

abbrev Seeds (n : Nat) := Fin n → Word → Prop

def Forced (C : List (Constraint n)) (q : Fin n) : Prop :=
  ∃ l r, Constraint.lower l r q ∈ C

def Denied (C : List (Constraint n)) (q : Fin n) : Prop :=
  Constraint.denial q ∈ C

def SeedsClosed (S : Seeds n) : Prop := ∀ q, PrefixClosed (S q)
def HasRoots (C : List (Constraint n)) (S : Seeds n) : Prop :=
  ∀ q, Forced C q → S q []

def SeedIncluded (S : Seeds n) (rho : Valuation n) : Prop :=
  ∀ q w, S q w → (rho q).nodes w

/-- Finite derivations of the propagation system, stack top on the LEFT. -/
inductive Derived (C : List (Constraint n)) (S : Seeds n) : Fin n → Word → Prop where
  | seed {q w} : S q w → Derived C S q w
  | leq {a b w} : Constraint.leq a b ∈ C →
      Derived C S a w → Derived C S b w
  | popLeft {a l r w} : Constraint.upper a l r ∈ C →
      Derived C S a (false :: w) → Derived C S l w
  | popRight {a l r w} : Constraint.upper a l r ∈ C →
      Derived C S a (true :: w) → Derived C S r w
  | pushLeft {l r a w} : Constraint.lower l r a ∈ C →
      Derived C S l w → Derived C S a (false :: w)
  | pushRight {l r a w} : Constraint.lower l r a ∈ C →
      Derived C S r w → Derived C S a (true :: w)

/-- Every derivation is contained in EVERY model containing its seeds. -/
theorem derived_sound {C : List (Constraint n)} {S : Seeds n}
    {rho : Valuation n} (hm : Models C rho) (hs : SeedIncluded S rho)
    {q w} (h : Derived C S q w) : (rho q).nodes w := by
  induction h with
  | seed h => exact hs _ _ h
  | leq hc _ ih => exact hm _ hc _ ih
  | popLeft hc _ ih => exact hm _ hc _ ih
  | popRight hc _ ih => exact hm _ hc _ ih
  | pushLeft hc _ ih => exact hm _ hc _ ih
  | pushRight hc _ ih => exact hm _ hc _ ih

/-- Removing an arbitrary finite suffix is valid for the WHOLE closure.
The forced-root assumption is necessary in the zero-prefix push cases. -/
theorem derived_take {C : List (Constraint n)} {S : Seeds n}
    (hc : SeedsClosed S) (hr : HasRoots C S) {q w}
    (h : Derived C S q w) : ∀ i, Derived C S q (w.take i) := by
  induction h with
  | seed h =>
    intro i
    apply Derived.seed
    apply hc _ (List.take i _) (List.drop i _)
    simpa only [List.take_append_drop] using h
  | leq h _ ih => intro i; exact Derived.leq h (ih i)
  | popLeft h _ ih =>
    intro i
    apply Derived.popLeft h
    simpa using ih (i + 1)
  | popRight h _ ih =>
    intro i
    apply Derived.popRight h
    simpa using ih (i + 1)
  | @pushLeft l r a w h _ ih =>
    intro i
    cases i with
    | zero => exact Derived.seed (hr a ⟨l, r, h⟩)
    | succ i => simpa using Derived.pushLeft h (ih i)
  | @pushRight l r a w h _ ih =>
    intro i
    cases i with
    | zero => exact Derived.seed (hr a ⟨l, r, h⟩)
    | succ i => simpa using Derived.pushRight h (ih i)

theorem derived_closed {C : List (Constraint n)} {S : Seeds n}
    (hc : SeedsClosed S) (hr : HasRoots C S) (q : Fin n) :
    PrefixClosed (Derived C S q) := by
  intro u v h
  simpa using derived_take hc hr h u.length

def closureValuation (C : List (Constraint n)) (S : Seeds n)
    (hc : SeedsClosed S) (hr : HasRoots C S) : Valuation n :=
  fun q => ⟨Derived C S q, derived_closed hc hr q⟩

def AvoidsDenials (C : List (Constraint n)) (S : Seeds n) : Prop :=
  ∀ q, Denied C q → ∀ w, ¬ Derived C S q w

/-- Safe canonical propagation satisfies ALL four normalized constraint forms. -/
theorem closure_models {C : List (Constraint n)} {S : Seeds n}
    (hc : SeedsClosed S) (hr : HasRoots C S) (hs : AvoidsDenials C S) :
    Models C (closureValuation C S hc hr) := by
  intro c hm
  cases c with
  | leq a b =>
    intro w hw
    exact Derived.leq hm hw
  | upper a l r =>
    intro w hw
    cases w with
    | nil => trivial
    | cons b w =>
      cases b with
      | false => exact Derived.popLeft hm hw
      | true => exact Derived.popRight hm hw
  | lower l r a =>
    intro w hw
    cases w with
    | nil => exact Derived.seed (hr a ⟨l, r, hm⟩)
    | cons b w =>
      cases b with
      | false => exact Derived.pushLeft hm hw
      | true => exact Derived.pushRight hm hw
  | denial a =>
    intro w hw
    exact hs a hm w hw

theorem avoids_of_model {C : List (Constraint n)} {S : Seeds n}
    {rho : Valuation n} (hm : Models C rho) (hs : SeedIncluded S rho) :
    AvoidsDenials C S := by
  intro q hq w hd
  exact hm (.denial q) hq w (derived_sound hm hs hd)

/-- The least closure is a model exactly when no denied fact is derivable. -/
theorem closure_models_iff {C : List (Constraint n)} {S : Seeds n}
    (hc : SeedsClosed S) (hr : HasRoots C S) :
    Models C (closureValuation C S hc hr) ↔ AvoidsDenials C S := by
  constructor
  · intro hm
    exact avoids_of_model hm (fun _ _ h => Derived.seed h)
  · exact closure_models hc hr

def forcedSeeds (C : List (Constraint n)) : Seeds n :=
  fun q w => Forced C q ∧ w = []

theorem forcedSeeds_closed (C : List (Constraint n)) : SeedsClosed (forcedSeeds C) := by
  intro q u v h
  refine ⟨h.1, ?_⟩
  have he := congrArg List.length h.2
  simp only [List.length_append, List.length_nil] at he
  exact List.length_eq_zero_iff.mp (by omega)

theorem forcedSeeds_roots (C : List (Constraint n)) : HasRoots C (forcedSeeds C) := by
  intro q hq
  exact ⟨hq, rfl⟩

theorem forcedSeeds_in_model {C : List (Constraint n)} {rho : Valuation n}
    (hm : Models C rho) : SeedIncluded (forcedSeeds C) rho := by
  rintro q w ⟨⟨l, r, hc⟩, rfl⟩
  exact hm (.lower l r q) hc [] (product_root _ _)

/-- Exact arbitrary-tree satisfiability characterization; not a decision test. -/
theorem satisfiable_iff_forced_safe (C : List (Constraint n)) :
    Satisfiable C ↔ AvoidsDenials C (forcedSeeds C) := by
  constructor
  · rintro ⟨rho, hm⟩
    exact avoids_of_model hm (forcedSeeds_in_model hm)
  · intro hs
    exact ⟨closureValuation C (forcedSeeds C) (forcedSeeds_closed C) (forcedSeeds_roots C),
      closure_models (forcedSeeds_closed C) (forcedSeeds_roots C) hs⟩

/-- A supplied separating address seeds ALL its prefixes, in addition to roots. -/
def pathSeeds (C : List (Constraint n)) (alpha : Fin n) (pi : Word) : Seeds n :=
  fun q w => forcedSeeds C q w ∨ (q = alpha ∧ w.IsPrefix pi)

theorem pathSeeds_closed (C : List (Constraint n)) (alpha : Fin n) (pi : Word) :
    SeedsClosed (pathSeeds C alpha pi) := by
  intro q u v h
  rcases h with h | ⟨hq, t, ht⟩
  · exact Or.inl (forcedSeeds_closed C q u v h)
  · right
    refine ⟨hq, v ++ t, ?_⟩
    simpa only [List.append_assoc] using ht

theorem pathSeeds_roots (C : List (Constraint n)) (alpha : Fin n) (pi : Word) :
    HasRoots C (pathSeeds C alpha pi) := by
  intro q hq
  exact Or.inl ⟨hq, rfl⟩

theorem pathSeeds_in_model {C : List (Constraint n)} {rho : Valuation n}
    {alpha : Fin n} {pi : Word} (hm : Models C rho) (ha : (rho alpha).nodes pi) :
    SeedIncluded (pathSeeds C alpha pi) rho := by
  intro q w h
  rcases h with h | ⟨rfl, t, ht⟩
  · exact forcedSeeds_in_model hm q w h
  · apply (rho alpha).closed w t
    simpa only [ht] using ha

def canonical (C : List (Constraint n)) (alpha : Fin n) (pi : Word) : Valuation n :=
  closureValuation C (pathSeeds C alpha pi) (pathSeeds_closed C alpha pi)
    (pathSeeds_roots C alpha pi)

theorem canonical_contains (C : List (Constraint n)) (alpha : Fin n) (pi : Word) :
    (canonical C alpha pi alpha).nodes pi := by
  apply Derived.seed
  exact Or.inr ⟨rfl, [], by simp⟩

/-- Canonical closure is below every model containing the proposed address. -/
theorem canonical_least {C : List (Constraint n)} {rho : Valuation n}
    {alpha : Fin n} {pi : Word} (hm : Models C rho) (ha : (rho alpha).nodes pi) :
    ∀ q, Below (canonical C alpha pi q) (rho q) := by
  intro q w hw
  exact derived_sound hm (pathSeeds_in_model hm ha) hw

/-- Exact bridge from arbitrary valuations to one finite separating address.
No satisfiability hypothesis is needed: all forced facts are included explicitly. -/
theorem not_entails_iff_canonical (C : List (Constraint n)) (alpha beta : Fin n) :
    ¬ Entails C alpha beta ↔
      ∃ pi, AvoidsDenials C (pathSeeds C alpha pi) ∧
        ¬ Derived C (pathSeeds C alpha pi) beta pi := by
  constructor
  · intro h
    obtain ⟨rho, pi, hm, ha, hb⟩ :=
      (not_entails_iff_separating C alpha beta).mp h
    refine ⟨pi, avoids_of_model hm (pathSeeds_in_model hm ha), ?_⟩
    intro hd
    exact hb (derived_sound hm (pathSeeds_in_model hm ha) hd)
  · rintro ⟨pi, hs, hb⟩ he
    have hm := closure_models (pathSeeds_closed C alpha pi) (pathSeeds_roots C alpha pi) hs
    exact hb (he (canonical C alpha pi) hm pi (canonical_contains C alpha pi))

/-- A denied forced root makes a normalized system unsatisfiable. -/
theorem forced_denied_unsatisfiable {C : List (Constraint n)} {q : Fin n}
    (hf : Forced C q) (hd : Denied C q) : ¬ Satisfiable C := by
  intro hm
  have hs := (satisfiable_iff_forced_safe C).mp hm
  exact hs q hd [] (Derived.seed ⟨hf, rfl⟩)

/-- Every model of a left-recursive lower product contains an unbounded 0-spine. -/
theorem lower_self_zero_spine {C : List (Constraint n)} {a b : Fin n}
    (hc : Constraint.lower a b a ∈ C) {rho : Valuation n} (hm : Models C rho)
    (i : Nat) : (rho a).nodes (List.replicate i false) := by
  induction i with
  | zero => exact hm (.lower a b a) hc [] (product_root _ _)
  | succ i ih =>
    have h := hm (.lower a b a) hc (false :: List.replicate i false) ih
    simpa using h

theorem lower_self_has_arbitrarily_deep_nodes {C : List (Constraint n)} {a b : Fin n}
    (hc : Constraint.lower a b a ∈ C) {rho : Valuation n} (hm : Models C rho)
    (N : Nat) : ∃ w, (rho a).nodes w ∧ N < w.length := by
  exact ⟨List.replicate (N+1) false, lower_self_zero_spine hc hm (N+1), by simp⟩

end CanonicalModel
end Subtail
