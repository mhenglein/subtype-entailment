import Subtail.ExpressionNormalization
import Subtail.SubtypeTerminalBridge
import Subtail.InfiniteDecision

/-!
Total entailment for finite expressions over bottom and binary product.
The specification ranges over arbitrary, possibly infinite trees. The finite
algorithms use no witness bound or quantitative closure assumption.
-/
namespace Subtail.EntailmentDecision

open TreeSemantics ExpressionNormalization SummaryAutomaton
open SubtypeTerminalBridge AbsorbingTerminal InfiniteDecision RankQueryDecision

variable {n : Nat}

/-- The complete two-branch backend for normalized variable queries. -/
def rawNormalizedEntailsCheck (C : List (Constraint n)) (a b : Fin n) : Bool :=
  let I := summaryInstance C a b
  !(infiniteWitnessCheck I || terminalWitnessCheck (terminalize I))

theorem rawNormalizedEntailsCheck_correct (C : List (Constraint n)) (a b : Fin n) :
    rawNormalizedEntailsCheck C a b = true ↔ Entails C a b := by
  classical
  have hs : ¬ Entails C a b ↔
      infiniteWitnessCheck (summaryInstance C a b) = true ∨
        terminalWitnessCheck (terminalize (summaryInstance C a b)) = true := by
    rw [not_entails_iff_infinite_or_terminal,
      infiniteWitnessCheck_correct _ (summary_absorbing C a b)]
  cases hi : infiniteWitnessCheck (summaryInstance C a b) <;>
    cases ht : terminalWitnessCheck (terminalize (summaryInstance C a b)) <;>
    simp_all [rawNormalizedEntailsCheck]

theorem entails_self (C : List (Constraint n)) (a : Fin n) : Entails C a a := by
  intro rho _ w h
  exact h

theorem entails_of_premise (C : List (Constraint n)) (a b : Fin n)
    (h : Constraint.leq a b ∈ C) : Entails C a b := by
  intro rho hm
  exact hm _ h

/-- Proved inexpensive cases avoid invoking the exhaustive backend needlessly.
The supplied empty-address test is sufficient only for a negative answer;
its failure always falls through to the complete backend. -/
def normalizedEntailsCheck (C : List (Constraint n)) (a b : Fin n) : Bool :=
  if a = b then true
  else if Constraint.leq a b ∈ C then true
  else if CanonicalReachability.satCheck C then
    if CanonicalReachability.separationCheck C a b [] then false
    else rawNormalizedEntailsCheck C a b
  else true

theorem normalizedEntailsCheck_correct (C : List (Constraint n)) (a b : Fin n) :
    normalizedEntailsCheck C a b = true ↔ Entails C a b := by
  by_cases hab : a = b
  · subst b
    simp [normalizedEntailsCheck, entails_self]
  by_cases hp : Constraint.leq a b ∈ C
  · simp [normalizedEntailsCheck, hab, hp, entails_of_premise C a b hp]
  cases hs : CanonicalReachability.satCheck C with
  | false =>
    have he : Entails C a b := by
      intro rho hm
      have ht := (CanonicalReachability.satCheck_correct C).mpr ⟨rho, hm⟩
      simp [hs] at ht
    simp [normalizedEntailsCheck, hab, hp, hs, he]
  | true =>
    cases hw : CanonicalReachability.separationCheck C a b [] with
    | false =>
      simpa [normalizedEntailsCheck, hab, hp, hs, hw] using
        rawNormalizedEntailsCheck_correct C a b
    | true =>
      have he : ¬ Entails C a b :=
        (CanonicalReachability.not_entails_iff_exists_check C a b).mpr ⟨[], hw⟩
      simp [normalizedEntailsCheck, hab, hp, hs, hw, he]

/-- Total expression-level decision. Only finite syntax is normalized;
values of the variables are never unfolded or enumerated. -/
def entailsCheck (G : Input n) (s t : Expr n) : Bool :=
  normalizedEntailsCheck (normalized G s t)
    ((naming G s t).ref s) ((naming G s t).ref t)

/-- The complete input language, with no satisfiability, regularity, witness
bound, or absorption hypothesis on the caller. -/
theorem entailsCheck_correct (G : Input n) (s t : Expr n) :
    entailsCheck G s t = true ↔ ExprEntails G s t := by
  rw [entailsCheck, normalizedEntailsCheck_correct]
  exact (normalize_entails_iff G s t).symm

theorem entailsCheck_false_iff (G : Input n) (s t : Expr n) :
    entailsCheck G s t = false ↔ ¬ ExprEntails G s t := by
  simpa only [Bool.eq_false_iff] using not_congr (entailsCheck_correct G s t)

end Subtail.EntailmentDecision
