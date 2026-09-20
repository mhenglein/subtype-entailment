import Subtail.EntailmentFast

/-! Materialize primitive transitions once, then reuse the existing exact tests.
The table-backed System equals its input on every control and letter. The
reference terminal fallback and the order of all candidate tests are unchanged.
-/
namespace Subtail.EntailmentPrepared

open TreeSemantics ExpressionNormalization StackSummary CanonicalReachability
open CanonicalReachabilityFast

def tabulate (edge : Fin n → Fin n → Bool) : Matrix n :=
  Vector.ofFn fun p => Vector.ofFn fun q => edge p q

@[simp] theorem lookup_tabulate (edge : Fin n → Fin n → Bool) (p q : Fin n) :
    lookup (tabulate edge) p q = edge p q := by
  simp [lookup, tabulate]

def materialize (M : System n) : System n :=
  let eps := tabulate M.eps
  let push0 := tabulate (M.push false)
  let push1 := tabulate (M.push true)
  let pop0 := tabulate (M.pop false)
  let pop1 := tabulate (M.pop true)
  ⟨lookup eps, fun a => lookup (if a then push1 else push0),
    fun a => lookup (if a then pop1 else pop0)⟩

theorem materialize_eq (M : System n) : materialize M = M := by
  rcases M with ⟨eps, push, pop⟩
  unfold materialize
  congr 1
  · funext p q
    exact lookup_tabulate eps p q
  · funext a p q
    cases a <;> simp
  · funext a p q
    cases a <;> simp

/-- Only runtime data; equality and correctness are proved separately. -/
structure Prepared (n : Nat) where
  machine : System n
  cache : Cache machine

def reference (M : System n) : Prepared n :=
  ⟨M, CanonicalReachabilityFast.prepare M⟩

def prepare (M : System n) : Prepared n :=
  reference (materialize M)

theorem prepare_eq (M : System n) : prepare M = reference M := by
  rw [prepare, materialize_eq]

def derivedCheck (P : Prepared n) (seeds : List (Config n))
    (q : Fin n) (w : Word) : Bool :=
  seeds.any fun c => reachesCheck P.machine P.cache c.1 c.2 q w

def safeCheck (C : List (Constraint n)) (P : Prepared n)
    (seeds : List (Config n)) : Bool :=
  (List.finRange n).all fun q =>
    if decide (Constraint.denial q ∈ C) then
      !(seeds.any fun c => controlReachCheck P.machine P.cache c.1 c.2 q)
    else true

def satCheck (C : List (Constraint n)) (P : Prepared n) : Bool :=
  safeCheck C P (forcedList C)

def separationCheck (C : List (Constraint n)) (P : Prepared n)
    (a b : Fin n) (w : Word) : Bool :=
  let seeds := pathList C a w
  safeCheck C P seeds && !(derivedCheck P seeds b w)

theorem satCheck_eq (C : List (Constraint n)) :
    satCheck C (prepare (systemOf C)) =
      CanonicalReachabilityFast.satCheck C (CanonicalReachabilityFast.prepare (systemOf C)) := by
  rw [prepare_eq]
  rfl

theorem separationCheck_eq (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    separationCheck C (prepare (systemOf C)) a b w =
      CanonicalReachabilityFast.separationCheck C
        (CanonicalReachabilityFast.prepare (systemOf C)) a b w := by
  rw [prepare_eq]
  rfl

def afterPositive (C : List (Constraint n)) (P : Prepared n)
    (a b : Fin n) (paths : List Word) : Bool :=
  if satCheck C P then
    if paths.any (separationCheck C P a b) then false
    else TerminalDecisionLazy.rawNormalizedEntailsCheckLazy C a b
  else true

theorem afterPositive_eq (C : List (Constraint n)) (a b : Fin n) (paths : List Word) :
    afterPositive C (prepare (systemOf C)) a b paths =
      EntailmentFast.afterPositive C (CanonicalReachabilityFast.prepare (systemOf C)) a b paths := by
  rw [prepare_eq]
  rfl

def normalizedWithPaths (C : List (Constraint n)) (a b : Fin n) (paths : List Word) : Bool :=
  if EntailmentFast.positiveCheck C a b then true
  else afterPositive C (prepare (systemOf C)) a b paths

theorem normalizedWithPaths_eq (C : List (Constraint n)) (a b : Fin n) (paths : List Word) :
    normalizedWithPaths C a b paths = EntailmentFast.normalizedWithPaths C a b paths := by
  simp only [normalizedWithPaths, EntailmentFast.normalizedWithPaths, afterPositive_eq]

def normalizedEntailsCheck (C : List (Constraint n)) (a b : Fin n) : Bool :=
  normalizedWithPaths C a b EntailmentFast.shortPaths

theorem normalizedEntailsCheck_eq (C : List (Constraint n)) (a b : Fin n) :
    normalizedEntailsCheck C a b = EntailmentFast.normalizedEntailsCheck C a b := by
  exact normalizedWithPaths_eq C a b EntailmentFast.shortPaths

def entailsCheck (G : Input n) (s t : Expr n) : Bool :=
  normalizedWithPaths (normalized G s t)
    ((naming G s t).ref s) ((naming G s t).ref t) (EntailmentFast.candidatePaths G s t)

theorem entailsCheck_eq_fast (G : Input n) (s t : Expr n) :
    entailsCheck G s t = EntailmentFast.entailsCheck G s t := by
  exact normalizedWithPaths_eq _ _ _ _

theorem entailsCheck_correct (G : Input n) (s t : Expr n) :
    entailsCheck G s t = true ↔ ExprEntails G s t := by
  rw [entailsCheck_eq_fast, EntailmentFast.entailsCheck_correct]

theorem entailsCheck_eq (G : Input n) (s t : Expr n) :
    entailsCheck G s t = EntailmentDecision.entailsCheck G s t := by
  rw [entailsCheck_eq_fast, EntailmentFast.entailsCheck_eq]

end Subtail.EntailmentPrepared
