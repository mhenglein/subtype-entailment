import Subtail.TerminalDecisionLazy
import Subtail.CanonicalReachabilityFast

/-!
Sound finite positive closure in front of the complete arbitrary-tree decision.
An unsuccessful bounded closure has no negative meaning.
-/
namespace Subtail.EntailmentFast

open TreeSemantics ExpressionNormalization

abbrev Relation (n : Nat) := List (Fin n × Fin n)

def Sound (C : List (Constraint n)) (R : Relation n) : Prop :=
  ∀ p q, (p,q) ∈ R → Entails C p q

def productRule (C : List (Constraint n)) (R : Relation n) (p q : Fin n) : Bool :=
  C.any fun c => match c with
    | .upper a l r => decide (p = a) && C.any (fun d => match d with
        | .lower l' r' b => decide (q = b) && decide ((l,l') ∈ R) && decide ((r,r') ∈ R)
        | _ => false)
    | _ => false

theorem productRule_sound (C : List (Constraint n)) (R : Relation n)
    (hR : Sound C R) (p q : Fin n) (h : productRule C R p q = true) :
    Entails C p q := by
  unfold productRule at h
  obtain ⟨c, hc, h⟩ := List.any_eq_true.mp h
  cases c with
  | upper a l r =>
    have h' : p = a ∧ (C.any fun d => match d with
        | .lower l' r' b => decide (q = b) && decide ((l,l') ∈ R) && decide ((r,r') ∈ R)
        | _ => false) = true := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
    obtain ⟨rfl, h'⟩ := h'
    obtain ⟨d, hd, h'⟩ := List.any_eq_true.mp h'
    cases d with
    | lower l' r' b =>
      have h'' : (q = b ∧ (l,l') ∈ R) ∧ (r,r') ∈ R := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using h'
      obtain ⟨⟨rfl, hl⟩, hr⟩ := h''
      intro rho hm w hw
      exact hm _ hd w
        (product_mono (hR l l' hl rho hm) (hR r r' hr rho hm) w (hm _ hc w hw))
    | leq _ _ => simp at h'
    | upper _ _ _ => simp at h'
    | denial _ => simp at h'
  | leq _ _ => simp at h
  | lower _ _ _ => simp at h
  | denial _ => simp at h

def positiveRule (C : List (Constraint n)) (R : Relation n) (p q : Fin n) : Bool :=
  decide ((p,q) ∈ R) || decide (p = q) || decide (Constraint.leq p q ∈ C) ||
    decide (Constraint.denial p ∈ C) ||
    (List.finRange n).any (fun m => decide ((p,m) ∈ R) && decide ((m,q) ∈ R)) ||
    productRule C R p q

theorem positiveRule_sound (C : List (Constraint n)) (R : Relation n)
    (hR : Sound C R) (p q : Fin n) (h : positiveRule C R p q = true) :
    Entails C p q := by
  simp only [positiveRule, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, Bool.and_eq_true, List.mem_finRange, true_and] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  · exact hR p q h
  · subst q; exact EntailmentDecision.entails_self C p
  · exact EntailmentDecision.entails_of_premise C p q h
  · intro rho hm w hw
    exact False.elim (hm _ h w hw)
  · obtain ⟨m, hp, hq⟩ := h
    intro rho hm w hw
    exact hR m q hq rho hm w (hR p m hp rho hm w hw)
  · exact productRule_sound C R hR p q h

def positiveStep (C : List (Constraint n)) (R : Relation n) : Relation n :=
  (StackSummary.pairs n).filter fun x => positiveRule C R x.1 x.2

theorem positiveStep_sound (C : List (Constraint n)) (R : Relation n)
    (hR : Sound C R) : Sound C (positiveStep C R) := by
  intro p q h
  exact positiveRule_sound C R hR p q (List.mem_filter.mp h).2

def positiveClosure (C : List (Constraint n)) : Nat → Relation n → Relation n
  | 0, R => R
  | fuel + 1, R =>
    let R' := positiveStep C R
    if R' = R then R else positiveClosure C fuel R'

theorem positiveClosure_sound (C : List (Constraint n)) (fuel : Nat) (R : Relation n)
    (hR : Sound C R) : Sound C (positiveClosure C fuel R) := by
  induction fuel generalizing R with
  | zero => exact hR
  | succ fuel ih =>
    simp only [positiveClosure]
    split
    · exact hR
    · exact ih _ (positiveStep_sound C R hR)

def positiveCheck (C : List (Constraint n)) (p q : Fin n) : Bool :=
  positiveRule C [] p q || decide ((p,q) ∈ positiveClosure C (n*n+1) [])

theorem positiveCheck_sound (C : List (Constraint n)) (p q : Fin n)
    (h : positiveCheck C p q = true) : Entails C p q := by
  have hs : Sound C ([] : Relation n) := by intro a b h; simp at h
  simp only [positiveCheck, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact positiveRule_sound C [] hs p q h
  · exact positiveClosure_sound C (n*n+1) [] hs p q h

def shortPaths : List Word := [[], [false], [true], [false,false], [false,true],
  [true,false], [true,true]]

def expressionPaths : Expr n → List Word
  | .var _ => [[]]
  | .bot => [[]]
  | .prod s t => [] :: ((expressionPaths s).map (false :: ·) ++
      (expressionPaths t).map (true :: ·))

/-- Finite syntax suggests paths; no completeness or witness bound is assumed. -/
def candidatePaths (G : Input n) (s t : Expr n) : List Word :=
  (shortPaths ++ expressionPaths s ++ expressionPaths t ++
    G.flatMap (fun pair => expressionPaths pair.1 ++ expressionPaths pair.2)).eraseDups

def separationExists (C : List (Constraint n))
    (cache : CanonicalReachabilityFast.Cache (CanonicalReachability.systemOf C))
    (a b : Fin n) (paths : List Word) : Bool :=
  paths.any (CanonicalReachabilityFast.separationCheck C cache a b)

theorem separationExists_sound (C : List (Constraint n))
    (cache : CanonicalReachabilityFast.Cache (CanonicalReachability.systemOf C))
    (hc : CanonicalReachabilityFast.Correct (CanonicalReachability.systemOf C) cache)
    (a b : Fin n) (paths : List Word) (h : separationExists C cache a b paths = true) :
    ¬ Entails C a b := by
  obtain ⟨w, _, hw⟩ := List.any_eq_true.mp h
  rw [CanonicalReachabilityFast.separationCheck_eq C cache hc] at hw
  exact (CanonicalReachability.not_entails_iff_exists_check C a b).mpr ⟨w, hw⟩

/-- Cached exact tests precede the complete fallback. An empty candidate list is valid. -/
def afterPositive (C : List (Constraint n))
    (cache : CanonicalReachabilityFast.Cache (CanonicalReachability.systemOf C))
    (a b : Fin n) (paths : List Word) : Bool :=
  if CanonicalReachabilityFast.satCheck C cache then
    if separationExists C cache a b paths then false
    else TerminalDecisionLazy.rawNormalizedEntailsCheckLazy C a b
  else true

theorem afterPositive_correct (C : List (Constraint n))
    (cache : CanonicalReachabilityFast.Cache (CanonicalReachability.systemOf C))
    (hc : CanonicalReachabilityFast.Correct (CanonicalReachability.systemOf C) cache)
    (a b : Fin n) (paths : List Word) :
    afterPositive C cache a b paths = true ↔ Entails C a b := by
  cases hs : CanonicalReachabilityFast.satCheck C cache with
  | false =>
    have he : Entails C a b := by
      apply unsatisfiable_entails
      intro hm
      have ht := (CanonicalReachability.satCheck_correct C).mpr hm
      rw [← CanonicalReachabilityFast.satCheck_eq C cache hc, hs] at ht
      cases ht
    simp [afterPositive, hs, he]
  | true =>
    cases hw : separationExists C cache a b paths with
    | true => simp [afterPositive, hs, hw, separationExists_sound C cache hc a b paths hw]
    | false => simpa [afterPositive, hs, hw] using
        TerminalDecisionLazy.rawNormalizedEntailsCheckLazy_correct C a b

def normalizedWithPaths (C : List (Constraint n)) (a b : Fin n) (paths : List Word) : Bool :=
  if positiveCheck C a b then true
  else afterPositive C (CanonicalReachabilityFast.prepare (CanonicalReachability.systemOf C)) a b paths

theorem normalizedWithPaths_correct (C : List (Constraint n)) (a b : Fin n) (paths : List Word) :
    normalizedWithPaths C a b paths = true ↔ Entails C a b := by
  cases h : positiveCheck C a b with
  | true => simp [normalizedWithPaths, h, positiveCheck_sound C a b h]
  | false => simpa [normalizedWithPaths, h] using
      afterPositive_correct C _ (CanonicalReachabilityFast.prepare_correct _) a b paths

/-- The shortcuts are sufficient certificates; the fallback is complete. -/
def normalizedEntailsCheck (C : List (Constraint n)) (a b : Fin n) : Bool :=
  normalizedWithPaths C a b shortPaths

theorem normalizedEntailsCheck_correct (C : List (Constraint n)) (a b : Fin n) :
    normalizedEntailsCheck C a b = true ↔ Entails C a b := by
  exact normalizedWithPaths_correct C a b shortPaths

def entailsCheck (G : Input n) (s t : Expr n) : Bool :=
  normalizedWithPaths (normalized G s t)
    ((naming G s t).ref s) ((naming G s t).ref t) (candidatePaths G s t)

theorem entailsCheck_correct (G : Input n) (s t : Expr n) :
    entailsCheck G s t = true ↔ ExprEntails G s t := by
  rw [entailsCheck, normalizedWithPaths_correct]
  exact (normalize_entails_iff G s t).symm

theorem entailsCheck_eq (G : Input n) (s t : Expr n) :
    entailsCheck G s t = EntailmentDecision.entailsCheck G s t := by
  apply Bool.eq_iff_iff.mpr
  rw [entailsCheck_correct, EntailmentDecision.entailsCheck_correct]

end Subtail.EntailmentFast
