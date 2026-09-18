import Subtail.CanonicalModel

/-!
# Semantic regression proofs and named trust-boundary audit

These are kernel proofs, not a finite-depth model oracle. The specification
quantifies over all path-set trees. No general decision function is defined.
-/
namespace Subtail
namespace CanonicalModelAudit
open TreeSemantics CanonicalModel

def spineConstraints : List (Constraint 2) := [.lower 0 1 0, .denial 1]
def spineValuation : Valuation 2 := fun q => if q = 0 then zeroSpine else bottom

theorem spine_is_model : Models spineConstraints spineValuation := by
  intro c hc
  simp [spineConstraints] at hc
  rcases hc with rfl | rfl
  · simpa [Holds, spineValuation] using zeroSpine_lower
  · intro w hw
    simpa [spineValuation, bottom] using hw

theorem spine_satisfiable : Satisfiable spineConstraints :=
  ⟨spineValuation, spine_is_model⟩

theorem spine_separates_at_empty : ¬ Entails spineConstraints 0 1 := by
  intro h
  have ha : (spineValuation 0).nodes [] := by simp [spineValuation, zeroSpine]
  have hb := h spineValuation spine_is_model [] ha
  simpa [spineValuation, bottom] using hb

/-- EVERY model of these constraints has unbounded product depth. -/
theorem spine_no_bounded_model (rho : Valuation 2) (hm : Models spineConstraints rho) :
    ¬ ∃ N, ∀ w, (rho 0).nodes w → w.length ≤ N := by
  rintro ⟨N, hn⟩
  obtain ⟨w, hw, hlen⟩ := lower_self_has_arbitrarily_deep_nodes
    (a := (0 : Fin 2)) (b := 1) (by simp [spineConstraints]) hm N
  have hb := hn w hw
  omega

def contradictory : List (Constraint 2) := [.lower 0 0 1, .denial 1]

theorem contradictory_unsatisfiable : ¬ Satisfiable contradictory := by
  apply forced_denied_unsatisfiable (q := (1 : Fin 2))
  · exact ⟨0, 0, by simp [contradictory]⟩
  · simp [Denied, contradictory]

theorem contradictory_entails : Entails contradictory 0 1 :=
  unsatisfiable_entails contradictory 0 1 contradictory_unsatisfiable

/-- A prefix seed that can be forgotten by a one-word-only implementation. -/
def prefixExample : List (Constraint 3) := [.lower 0 1 2, .denial 1]

theorem empty_prefix_is_seed : pathSeeds prefixExample 0 [false] 0 [] := by
  right
  exact ⟨rfl, [false], rfl⟩

theorem empty_prefix_has_consequence :
    Derived prefixExample (pathSeeds prefixExample 0 [false]) 2 [false] := by
  exact Derived.pushLeft (l := 0) (r := 1) (a := 2) (w := [])
    (by simp [prefixExample]) (Derived.seed empty_prefix_is_seed)

def singleWordOnly : Seeds 3 := fun q w => q = 0 ∧ w = [false]

theorem single_word_seeds_are_not_closed : ¬ SeedsClosed singleWordOnly := by
  intro hc
  have h := hc 0 [] [false] (show singleWordOnly 0 ([] ++ [false]) from ⟨rfl, rfl⟩)
  simp [singleWordOnly] at h

theorem bottom_root_exists : domain bottom [] := domain_root bottom

theorem bottom_has_no_children (a : Bool) : ¬ domain bottom [a] := by
  intro h
  exact (domain_child bottom [] a).mp h

end CanonicalModelAudit
end Subtail

#print axioms Subtail.TreeSemantics.tree_roundtrip
#print axioms Subtail.TreeSemantics.diagram_domain_exact
#print axioms Subtail.CanonicalModel.derived_closed
#print axioms Subtail.CanonicalModel.closure_models_iff
#print axioms Subtail.CanonicalModel.satisfiable_iff_forced_safe
#print axioms Subtail.CanonicalModel.not_entails_iff_canonical
#print axioms Subtail.CanonicalModelAudit.spine_no_bounded_model
#print axioms Subtail.CanonicalModelAudit.spine_separates_at_empty
