import Subtail.PopAcyclic
import Subtail.FiniteTreeReduction
import Subtail.EntailmentFast

/-! Executable finite-tree entailment via consuming reverse-pop cycles.
The graph classifier supplies the hypotheses of the existing semantic lemmas.
All runtime definitions use the already checked finite cached constructions.
-/
namespace Subtail.FiniteTreeDecision

open TreeSemantics ExpressionNormalization CanonicalModel CanonicalReachability
  StackSummary StackReachability FiniteTreeReduction

/-- A reverse-pop letter edge whose target can return to its source. -/
def growthCheck (M : System n) : Bool :=
  let cache := CanonicalReachabilityFast.prepare M
  (List.finRange n).any fun p => (List.finRange n).any fun r =>
    (M.push false r p || M.push true r p) &&
      CanonicalReachabilityFast.lookup cache.paths r p

theorem growthCheck_correct (M : System n) :
    growthCheck M = true ↔
      ∃ p r a, M.push a r p = true ∧ ∃ w, Pop (reverse M) r w p := by
  have hp := (CanonicalReachabilityFast.prepare_correct M).paths_eq
  simp only [growthCheck, hp, pathCheck_correct, List.any_eq_true,
    List.mem_finRange, true_and, Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨p, r, hpop, hpath⟩
    obtain ⟨w, hw⟩ := (exists_pop_iff_path (reverse M) r p).mpr hpath
    rcases hpop with hf | ht
    · exact ⟨p, r, false, hf, w, hw⟩
    · exact ⟨p, r, true, ht, w, hw⟩
  · rintro ⟨p, r, a, ha, w, hw⟩
    refine ⟨p, r, ?_, (exists_pop_iff_path (reverse M) r p).mp ⟨w, hw⟩⟩
    cases a
    · exact Or.inl ha
    · exact Or.inr ha

theorem growthCheck_false_no_loop (M : System n) (hg : growthCheck M = false)
    (p : Fin n) (w : Word) (hw : Pop (reverse M) p w p) : w = [] := by
  cases w with
  | nil => rfl
  | cons a w =>
      obtain ⟨r, s, hb, hp, ht⟩ := hw
      have hreturn : Pop (reverse M) s w r := pop_post ht hb
      have htrue : growthCheck M = true :=
        (growthCheck_correct M).mpr ⟨r, s, a, hp, w, hreturn⟩
      rw [hg] at htrue
      contradiction

theorem growthCheck_false_bound (M : System n) (hg : growthCheck M = false) :
    UniformReversePopBound M := by
  refine ⟨n, ?_⟩
  intro m q w hw
  exact PopAcyclic.pop_length_lt_of_no_nonempty_loop (reverse M)
    (growthCheck_false_no_loop M hg) hw

theorem push_target_forced (C : List (Constraint n)) (p r : Fin n) (a : Bool)
    (hp : (systemOf C).push a r p = true) : Forced C p := by
  cases a with
  | false =>
      obtain ⟨s, hs⟩ := (push_left_spec C r p).mp hp
      exact ⟨r, s, hs⟩
  | true =>
      obtain ⟨s, hs⟩ := (push_right_spec C r p).mp hp
      exact ⟨s, r, hs⟩

theorem growthCheck_true_noFiniteModel (C : List (Constraint n))
    (hg : growthCheck (systemOf C) = true) : ¬ FiniteSatisfiable C := by
  obtain ⟨p, r, a, hp, w, hw⟩ := (growthCheck_correct (systemOf C)).mp hg
  apply forced_reverse_pop_loop_noFiniteModel C p (push_target_forced C p r a hp)
  refine ⟨a :: w, by simp, ?_⟩
  exact ⟨p, r, Balanced.refl p, hp, hw⟩

/-- First component reports forced infinite growth; second decides the query. -/
def run (G : Input n) (s t : Expr n) : Bool × Bool :=
  let growth := growthCheck (systemOf (normalized G s t))
  (growth, growth || EntailmentFast.entailsCheck G s t)

def entailsCheck (G : Input n) (s t : Expr n) : Bool :=
  (run G s t).2

theorem run_growth_noFiniteModel (G : Input n) (s t : Expr n)
    (hg : (run G s t).1 = true) :
    ¬ FiniteSatisfiable (normalized G s t) := by
  exact growthCheck_true_noFiniteModel _ hg

theorem run_growth_noFiniteExprModel (G : Input n) (s t : Expr n)
    (hg : (run G s t).1 = true) :
    ¬ ∃ rho, (∀ q, FiniteTree (rho q)) ∧ ExprModels G rho := by
  rintro ⟨rho, hf, hm⟩
  apply run_growth_noFiniteModel G s t hg
  exact ⟨(naming G s t).extend rho, extend_models G s t rho hm,
    fun i => finiteTree_extend (naming G s t) rho hf i⟩

theorem entailsCheck_correct (G : Input n) (s t : Expr n) :
    entailsCheck G s t = true ↔ FiniteExprEntails G s t := by
  cases hg : growthCheck (systemOf (normalized G s t)) with
  | false =>
      have hiff : FiniteExprEntails G s t ↔ ExprEntails G s t :=
        (normalize_finite_entails_iff G s t).trans
          ((finiteEntails_iff_entails_of_uniform_reverse_pop _ _ _
            (growthCheck_false_bound _ hg)).trans (normalize_entails_iff G s t).symm)
      simp only [entailsCheck, run, hg, Bool.false_or]
      exact (EntailmentFast.entailsCheck_correct G s t).trans hiff.symm
  | true =>
      have hn := growthCheck_true_noFiniteModel _ hg
      have hf : FiniteExprEntails G s t := (normalize_finite_entails_iff G s t).mpr (by
        intro rho hr hm
        exact False.elim (hn ⟨rho, hm, hr⟩))
      simp only [entailsCheck, run, hg, Bool.true_or]
      exact ⟨fun _ => hf, fun _ => True.intro⟩

end Subtail.FiniteTreeDecision
