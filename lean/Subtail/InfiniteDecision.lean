import Subtail.InfiniteCycle
import Subtail.RankQueryEnumeration
import Subtail.FiniteSearch

/-!
Executable finite candidate data for the C029 decision. The prefix search
ranges over all finite paths of the periodic monitor, not bounded words.
-/
namespace Subtail.InfiniteDecision
open AbsorbingTerminal RankQueryEnumeration
variable {k : Nat}

def safeOption (I : Instance k) : Option (Fin k) → Bool
  | none => false
  | some q => safeState I q

theorem safeOption_iff (I : Instance k) (o : Option (Fin k)) :
    safeOption I o = true ↔ ∃ q, o = some q ∧ safeState I q = true := by
  cases o <;> simp [safeOption]

/-- All cuts of this supplied finite run, including its initial and final cuts. -/
def safeRunCheck (I : Instance k) (q : Fin k) (w : Word) (r : Fin k) : Bool :=
  decide (runFrom I q w = some r) &&
    (List.range (w.length + 1)).all (fun i => safeOption I (runFrom I q (w.take i)))

theorem safeRunCheck_correct (I : Instance k) (q : Fin k) (w : Word) (r : Fin k) :
    safeRunCheck I q w r = true ↔ SafeRun I q w r := by
  simp only [safeRunCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, safeOption_iff, SafeRun, safeCut]
  constructor
  · rintro ⟨hr, hs⟩
    exact ⟨hr, fun i hi => hs i (by omega)⟩
  · rintro ⟨hr, hs⟩
    exact ⟨hr, fun i hi => hs i (by omega)⟩

/-- The endpoint is final and has an empty incoming column; the cycle is safe,
nonempty, and within the proved k-letter bound. -/
def cycleCheck (I : Instance k) (q : Fin k) (c : Word) : Bool :=
  decide (c ≠ []) && decide (c.length ≤ k) && I.final.get q &&
    (List.finRange k).all (fun p => !((I.flags.get p).get q)) &&
    safeRunCheck I q c q

theorem cycleCheck_correct (I : Instance k) (q : Fin k) (c : Word) :
    cycleCheck I q c = true ↔
      c ≠ [] ∧ c.length ≤ k ∧ I.final.get q = true ∧
      (∀ p, (I.flags.get p).get q = false) ∧ SafeRun I q c q := by
  simp only [cycleCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    safeRunCheck_correct]
  constructor
  · rintro ⟨⟨⟨⟨hne, hlen⟩, hf⟩, hcol⟩, hr⟩
    exact ⟨hne, hlen, hf, fun p => by simpa using hcol p (List.mem_finRange p), hr⟩
  · rintro ⟨hne, hlen, hf, hcol, hr⟩
    exact ⟨⟨⟨⟨hne, hlen⟩, hf⟩, fun p _ => by simpa using hcol p⟩, hr⟩

def candidates (I : Instance k) : List (Fin k × Word) :=
  ((List.finRange k).flatMap fun q =>
    (boundedLists bools k).map (fun c => (q,c))).filter
    (fun qc => cycleCheck I qc.1 qc.2)

theorem mem_candidates (I : Instance k) (q : Fin k) (c : Word) :
    (q,c) ∈ candidates I ↔ cycleCheck I q c = true := by
  constructor
  · intro h
    exact (List.mem_filter.mp h).2
  · intro h
    apply List.mem_filter.mpr
    refine ⟨?_, h⟩
    apply List.mem_flatMap.mpr
    refine ⟨q, List.mem_finRange q, ?_⟩
    apply List.mem_map.mpr
    refine ⟨c, ?_, rfl⟩
    exact (mem_boundedLists bools k c).mpr
      ⟨(cycleCheck_correct I q c).mp h |>.2.1, fun a _ => mem_bools a⟩

end Subtail.InfiniteDecision
