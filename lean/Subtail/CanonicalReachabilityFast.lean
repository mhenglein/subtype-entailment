import Subtail.SummaryAutomaton
import Subtail.FiniteSearch
import Subtail.StackSummaryFast

/-! Cached finite tables for exact arbitrary-stack and supplied-address tests. -/
namespace Subtail.CanonicalReachabilityFast

open TreeSemantics StackSummary StackReachability CanonicalReachability

abbrev Matrix (n : Nat) := Vector (Vector Bool n) n

def lookup (T : Matrix n) (p q : Fin n) : Bool := (T.get p).get q

def matrix (R : List (Fin n × Fin n)) : Matrix n :=
  Vector.ofFn fun p => Vector.ofFn fun q => decide ((p,q) ∈ R)

@[simp] theorem lookup_matrix (R : List (Fin n × Fin n)) (p q : Fin n) :
    lookup (matrix R) p q = decide ((p,q) ∈ R) := by
  simp [lookup, matrix]

def successors (edge : Fin n → Fin n → Bool) (p : Fin n) : List (Fin n) :=
  (List.finRange n).filter (edge p)

theorem reach_iff_path (edge : Fin n → Fin n → Bool) (p q : Fin n) :
    FiniteSearch.Reach (successors edge) p q ↔ StackSummary.Path edge p q := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | step _ he ih => exact .step ih (List.mem_filter.mp he).2
  · intro h
    induction h with
    | refl => exact .refl
    | step _ he ih => exact .step ih (List.mem_filter.mpr ⟨List.mem_finRange _, he⟩)

def pathSet (edge : Fin n → Fin n → Bool) (p : Fin n) : List (Fin n) :=
  FiniteSearch.reachable (successors edge) (List.finRange n) p

theorem mem_pathSet (edge : Fin n → Fin n → Bool) (p q : Fin n) :
    q ∈ pathSet edge p ↔ StackSummary.Path edge p q := by
  exact (FiniteSearch.mem_reachable_iff (successors edge) (List.finRange n)
    (fun x => List.mem_finRange x)).trans (reach_iff_path edge p q)

def pathMatrix (edge : Fin n → Fin n → Bool) : Matrix n :=
  Vector.ofFn fun p =>
    let reached := pathSet edge p
    Vector.ofFn fun q => decide (q ∈ reached)

theorem lookup_pathMatrix (edge : Fin n → Fin n → Bool) (p q : Fin n) :
    lookup (pathMatrix edge) p q = StackSummary.pathCheck edge p q := by
  apply Bool.eq_iff_iff.mpr
  simp [lookup, pathMatrix, mem_pathSet]

/-- Runtime payload; its semantic invariant is proved separately. -/
structure Cache (M : System n) where
  forward : Matrix n
  backward : Matrix n
  paths : Matrix n

structure Correct (M : System n) (cache : Cache M) : Prop where
  forward_eq : ∀ p q, lookup cache.forward p q = StackSummary.balancedCheck M p q
  backward_eq : ∀ p q, lookup cache.backward p q = StackSummary.balancedCheck (reverse M) p q
  paths_eq : ∀ p q, lookup cache.paths p q = StackSummary.pathCheck (controlEdge (reverse M)) p q

def prepare (M : System n) : Cache M :=
  let forward := matrix (StackSummaryFast.balancedTable M)
  let backward := matrix (StackSummaryFast.balancedTable (reverse M))
  let edge := fun p q => lookup backward p q || (reverse M).pop false p q || (reverse M).pop true p q
  ⟨forward, backward, pathMatrix edge⟩

theorem prepare_correct (M : System n) : Correct M (prepare M) := by
  have hf : ∀ p q, lookup (matrix (StackSummaryFast.balancedTable M)) p q =
      StackSummary.balancedCheck M p q := by
    intro p q
    rw [lookup_matrix]
    exact StackSummaryFast.balancedCheck_eq_reference M p q
  have hb : ∀ p q, lookup (matrix (StackSummaryFast.balancedTable (reverse M))) p q =
      StackSummary.balancedCheck (reverse M) p q := by
    intro p q
    rw [lookup_matrix]
    exact StackSummaryFast.balancedCheck_eq_reference (reverse M) p q
  refine ⟨hf, hb, ?_⟩
  intro p q
  simp only [prepare, lookup_pathMatrix, hb]
  rfl

def nextSet (M : System n) (T : Matrix n) (S : List (Fin n)) (a : Bool) : List (Fin n) :=
  (List.finRange n).filter fun q =>
    S.any fun p => (List.finRange n).any fun r => M.pop a p r && lookup T r q

theorem nextSet_eq (M : System n) (T : Matrix n)
    (hT : ∀ p q, lookup T p q = StackSummary.balancedCheck M p q)
    (S : List (Fin n)) (a : Bool) :
    nextSet M T S a = SummaryAutomaton.nextSet M S a := by
  simp only [nextSet, SummaryAutomaton.nextSet, hT]

/-- A word consumes one letter per materialized subset transition. -/
def popSet (M : System n) (T : Matrix n) (p : Fin n) (w : Word) : List (Fin n) :=
  w.foldl (fun S a => nextSet M T S a)
    ((List.finRange n).filter fun q => lookup T p q)

theorem popSet_eq (M : System n) (T : Matrix n)
    (hT : ∀ p q, lookup T p q = StackSummary.balancedCheck M p q)
    (p : Fin n) (w : Word) : popSet M T p w = SummaryAutomaton.popSet M p w := by
  have aux : ∀ v : Word, popSet M T p v.reverse = SummaryAutomaton.popSet M p v.reverse := by
    intro v
    induction v with
    | nil => simp [popSet, SummaryAutomaton.popSet, StackReachability.popCheck, hT]
    | cons a v ih =>
      rw [List.reverse_cons, SummaryAutomaton.popSet_snoc]
      simp only [popSet, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
      rw [ih, nextSet_eq M T hT]
  simpa only [List.reverse_reverse] using aux w.reverse

theorem mem_popSet (M : System n) (T : Matrix n)
    (hT : ∀ p q, lookup T p q = StackSummary.balancedCheck M p q)
    (p q : Fin n) (w : Word) : q ∈ popSet M T p w ↔ Pop M p w q := by
  rw [popSet_eq M T hT, SummaryAutomaton.mem_popSet]

def reachesCheck (M : System n) (cache : Cache M)
    (p : Fin n) (u : Word) (q : Fin n) (v : Word) : Bool :=
  (List.range (u.length+1)).any fun i =>
    let P := popSet M cache.forward p (u.take i)
    (List.range (v.length+1)).any fun j =>
      let Q := popSet (reverse M) cache.backward q (v.take j)
      (u.drop i == v.drop j) &&
        (List.finRange n).any fun m => decide (m ∈ P) && decide (m ∈ Q)

theorem reachesCheck_eq (M : System n) (cache : Cache M) (hc : Correct M cache)
    (p : Fin n) (u : Word) (q : Fin n) (v : Word) :
    reachesCheck M cache p u q v = StackReachability.reachesCheck M p u q v := by
  apply Bool.eq_iff_iff.mpr
  simp [reachesCheck, StackReachability.reachesCheck, List.any_eq_true,
    mem_popSet M cache.forward hc.forward_eq,
    mem_popSet (reverse M) cache.backward hc.backward_eq, and_assoc]

def controlReachCheck (M : System n) (cache : Cache M)
    (p : Fin n) (u : Word) (q : Fin n) : Bool :=
  (List.range (u.length+1)).any fun i =>
    let P := popSet M cache.forward p (u.take i)
    (List.finRange n).any fun m => decide (m ∈ P) && lookup cache.paths q m

theorem controlReachCheck_eq (M : System n) (cache : Cache M) (hc : Correct M cache)
    (p : Fin n) (u : Word) (q : Fin n) :
    controlReachCheck M cache p u q = StackReachability.controlReachCheck M p u q := by
  apply Bool.eq_iff_iff.mpr
  simp [controlReachCheck, StackReachability.controlReachCheck, List.any_eq_true,
    mem_popSet M cache.forward hc.forward_eq, hc.paths_eq]

def derivedCheck (C : List (Constraint n)) (cache : Cache (systemOf C))
    (seeds : List (Config n)) (q : Fin n) (w : Word) : Bool :=
  seeds.any fun c => reachesCheck (systemOf C) cache c.1 c.2 q w

theorem derivedCheck_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache)
    (seeds : List (Config n)) (q : Fin n) (w : Word) :
    derivedCheck C cache seeds q w = CanonicalReachability.derivedCheck C seeds q w := by
  simp only [derivedCheck, CanonicalReachability.derivedCheck, reachesCheck_eq _ _ hc]

def safeCheck (C : List (Constraint n)) (cache : Cache (systemOf C))
    (seeds : List (Config n)) : Bool :=
  (List.finRange n).all fun q =>
    if decide (Constraint.denial q ∈ C) then
      !(seeds.any fun c => controlReachCheck (systemOf C) cache c.1 c.2 q)
    else true

theorem safeCheck_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache)
    (seeds : List (Config n)) :
    safeCheck C cache seeds = CanonicalReachability.safeCheck C seeds := by
  simp only [safeCheck, CanonicalReachability.safeCheck, controlReachCheck_eq _ _ hc]

def satCheck (C : List (Constraint n)) (cache : Cache (systemOf C)) : Bool :=
  safeCheck C cache (forcedList C)

theorem satCheck_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache) :
    satCheck C cache = CanonicalReachability.satCheck C := by
  exact safeCheck_eq C cache hc (forcedList C)

def separationCheck (C : List (Constraint n)) (cache : Cache (systemOf C))
    (a b : Fin n) (w : Word) : Bool :=
  let seeds := pathList C a w
  safeCheck C cache seeds && !(derivedCheck C cache seeds b w)

theorem separationCheck_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache)
    (a b : Fin n) (w : Word) :
    separationCheck C cache a b w = CanonicalReachability.separationCheck C a b w := by
  simp only [separationCheck, CanonicalReachability.separationCheck,
    safeCheck_eq _ _ hc, derivedCheck_eq _ _ hc]

end Subtail.CanonicalReachabilityFast
