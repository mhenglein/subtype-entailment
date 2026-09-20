import Subtail.CanonicalReachabilityFast
import Subtail.InfiniteDecisionLazy

/-! Construct the same physical summary automaton from exact finite tables.
The constructor accepts runtime data; its equality theorem separately checks
the machine and cache invariant. No state, flag, bound or decision is changed.
-/
namespace Subtail.SummaryInstanceCached

open TreeSemantics StackSummary StackReachability CanonicalReachability
open CanonicalReachabilityFast SummaryAutomaton

def initialPair (M : System n) (cache : Cache M) (a b : Fin n) : Summary n :=
  ((List.finRange n).filter fun q => lookup cache.forward a q,
   (List.finRange n).filter fun q => lookup cache.backward b q)

theorem initialPair_mem (M : System n) (cache : Cache M) (a b : Fin n) :
    initialPair M cache a b ∈ states n :=
  pair_mem_states (filter_mem_subsets _ _) (filter_mem_subsets _ _)

def initial (M : System n) (cache : Cache M) (a b : Fin n) : Fin (states n).length :=
  encode (initialPair M cache a b) (initialPair_mem M cache a b)

def advancePair (M : System n) (cache : Cache M) (s : Summary n) (x : Bool) : Summary n :=
  (CanonicalReachabilityFast.nextSet M cache.forward s.1 x,
   CanonicalReachabilityFast.nextSet (reverse M) cache.backward s.2 x)

theorem advancePair_mem (M : System n) (cache : Cache M) (s : Summary n) (x : Bool) :
    advancePair M cache s x ∈ states n :=
  pair_mem_states (filter_mem_subsets _ _) (filter_mem_subsets _ _)

def advance (M : System n) (cache : Cache M) (q : Fin (states n).length) (x : Bool) :
    Fin (states n).length :=
  encode (advancePair M cache (decode q) x) (advancePair_mem M cache (decode q) x)

def dangerCheck (C : List (Constraint n)) (M : System n) (cache : Cache M) (m : Fin n) : Bool :=
  (List.finRange n).any fun d => decide (Constraint.denial d ∈ C) && lookup cache.paths d m

def satCheck (C : List (Constraint n)) (M : System n) (cache : Cache M) : Bool :=
  (List.finRange n).all fun q =>
    if decide (Constraint.denial q ∈ C) then
      !((forcedList C).any fun c => controlReachCheck M cache c.1 c.2 q)
    else true

def summaryInstance (C : List (Constraint n)) (M : System n) (cache : Cache M)
    (a b : Fin n) : Instance (states n).length :=
  let sat := satCheck C M cache
  let danger := Vector.ofFn (dangerCheck C M cache)
  { initial := initial M cache a b
    transitions := Vector.ofFn fun q => (some (advance M cache q false), some (advance M cache q true))
    bad := Vector.ofFn fun q => !sat || (decode q).1.any (fun m => danger.get m)
    final := Vector.ofFn fun q =>
      !((decode q).2.any fun f => decide (∃ l r, Constraint.lower l r f ∈ C))
    flags := Vector.ofFn fun p => Vector.ofFn fun q =>
      (decode p).1.any fun m => decide (m ∈ (decode q).2) }

theorem initialPair_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache) (a b : Fin n) :
    initialPair (systemOf C) cache a b = summaryAt C a b [] := by
  simp only [initialPair, summaryAt, SummaryAutomaton.popSet, popCheck,
    hc.forward_eq, hc.backward_eq]

theorem initial_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache) (a b : Fin n) :
    initial (systemOf C) cache a b = code C a b [] := by
  simp only [initial, code, initialPair_eq C cache hc]

theorem advancePair_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache) (s : Summary n) (x : Bool) :
    advancePair (systemOf C) cache s x = SummaryAutomaton.advancePair C s x := by
  simp only [advancePair, SummaryAutomaton.advancePair,
    CanonicalReachabilityFast.nextSet_eq _ _ hc.forward_eq,
    CanonicalReachabilityFast.nextSet_eq _ _ hc.backward_eq]

theorem advance_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache) (q : Fin (states n).length) (x : Bool) :
    advance (systemOf C) cache q x = SummaryAutomaton.advance C q x := by
  simp only [advance, SummaryAutomaton.advance, advancePair_eq C cache hc]

theorem dangerCheck_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache) (m : Fin n) :
    dangerCheck C (systemOf C) cache m = SummaryBridge.dangerCheck C m := by
  simp only [dangerCheck, SummaryBridge.dangerCheck, hc.paths_eq]

theorem satCheck_eq (C : List (Constraint n)) (cache : Cache (systemOf C))
    (hc : Correct (systemOf C) cache) :
    satCheck C (systemOf C) cache = CanonicalReachability.satCheck C := by
  exact CanonicalReachabilityFast.satCheck_eq C cache hc

/-- Equality includes unreachable physical states and every ordered flag. -/
theorem summaryInstance_eq (C : List (Constraint n)) (M : System n) (cache : Cache M)
    (hM : M = systemOf C) (hc : Correct M cache) (a b : Fin n) :
    summaryInstance C M cache a b = SummaryAutomaton.summaryInstance C a b := by
  subst M
  simp only [summaryInstance, initial_eq C cache hc, advance_eq C cache hc,
    satCheck_eq C cache hc, dangerCheck_eq C cache hc, vector_get_ofFn]
  rfl

def rawWith (C : List (Constraint n)) (M : System n) (cache : Cache M) (a b : Fin n) : Bool :=
  let I := summaryInstance C M cache a b
  !(InfiniteDecisionLazy.infiniteWitnessCheckLazy I ||
    TerminalDecisionLazy.terminalWitnessCheckLazy (AbsorbingTerminal.terminalize I))

theorem rawWith_eq (C : List (Constraint n)) (M : System n) (cache : Cache M)
    (hM : M = systemOf C) (hc : Correct M cache) (a b : Fin n) :
    rawWith C M cache a b = InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy C a b := by
  simp only [rawWith, summaryInstance_eq C M cache hM hc,
    InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy]

end Subtail.SummaryInstanceCached
