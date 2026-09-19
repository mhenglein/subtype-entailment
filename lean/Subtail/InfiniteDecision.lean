import Subtail.InfiniteCycle
import Subtail.PeriodicRun
import Subtail.PeriodicMonitor
import Subtail.RankQueryEnumeration
import Subtail.FiniteSearch

/-!
Executable finite candidate data for the C029 decision. The prefix search
ranges over all finite paths of the periodic monitor, not bounded words.
-/
namespace Subtail.InfiniteDecision
open AbsorbingTerminal RankQueryEnumeration
variable {k : Nat}

theorem sum_map_constant (xs : List α) (n : Nat) :
    (xs.map (fun _ => n)).sum = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem exactLists_length (xs : List α) (n : Nat) :
    (exactLists xs n).length = xs.length ^ n := by
  induction n with
  | zero => simp [exactLists]
  | succ n ih =>
    simp [exactLists, List.length_flatMap, ih, sum_map_constant,
      Nat.pow_succ, Nat.mul_comm]

theorem masks_length_le (k : Nat) : (masks k).length ≤ 2^k := by
  calc
    (masks k).length ≤ (exactLists bools k).length := List.length_filterMap_le _ _
    _ = 2^k := by rw [exactLists_length]; rfl

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

/-- The unbounded prefix obligation left after exact bounded-cycle enumeration. -/
theorem infWitness_iff_good_candidate (I : Instance k) (hA : Absorbing I) :
    InfWitness I ↔ ∃ q c, (q,c) ∈ candidates I ∧
      ∃ w, SafeRun I I.initial w q ∧ PeriodicRun.PrefixGood I w c := by
  constructor
  · intro h
    obtain ⟨w,q,c,hw,hq,hcol,hcycle,hne,hlen⟩ :=
      (InfiniteCycle.infWitness_iff_bounded_cycle I hA).mp h
    have hf : I.final.get q = true := by
      simpa [finalCheck, hq] using hw.2.1
    refine ⟨q,c,(mem_candidates I q c).mpr ?_,w,
      PeriodicRun.witness_safeRun I hw hq, PeriodicRun.prefixGood_of_witness I hw c⟩
    exact (cycleCheck_correct I q c).mpr ⟨hne,hlen,hf,hcol,hcycle⟩
  · rintro ⟨q,c,hmem,w,hw,hgood⟩
    obtain ⟨hne,hlen,hf,hcol,hcycle⟩ :=
      (cycleCheck_correct I q c).mp ((mem_candidates I q c).mp hmem)
    exact PeriodicRun.infWitness_of_prefix_good I hA hw hcycle hne hf hgood

/-- Raw finite-state cardinal bound; computing it does not enumerate the states. -/
def monitorCapacity (k : Nat) (c : Word) : Nat :=
  k * (c.length * (2 * ((2^k)^c.length)))

theorem bucketVectors_length_le (k d : Nat) :
    (PeriodicMonitor.bucketVectors k d).length ≤ (2^k)^d := by
  calc
    _ ≤ (exactLists (masks k) d).length := List.length_filterMap_le _ _
    _ = (masks k).length^d := exactLists_length _ _
    _ ≤ (2^k)^d := Nat.pow_le_pow_left (masks_length_le k) d

theorem allStates_length_le (k : Nat) (c : Word) :
    (PeriodicMonitor.allStates k c).length ≤ monitorCapacity k c := by
  have hb := bucketVectors_length_le k c.length
  have he : (PeriodicMonitor.allStates k c).length =
      k * (c.length * (2 * (PeriodicMonitor.bucketVectors k c.length).length)) := by
    simp [PeriodicMonitor.allStates, List.length_flatMap, sum_map_constant,
      bools, Nat.two_mul]
  rw [he]
  exact Nat.mul_le_mul_left k
    (Nat.mul_le_mul_left c.length (Nat.mul_le_mul_left 2 hb))

theorem reach_iff_path (I : Instance k) (c : Word) (x y : PeriodicMonitor.State k c) :
    FiniteSearch.Reach (PeriodicMonitor.successors I c) x y ↔
      PeriodicMonitor.Path I c x y := by
  constructor
  · intro h
    induction h with
    | refl => exact PeriodicMonitor.Path.refl
    | step _ hs ih => exact PeriodicMonitor.Path.step ih hs
  · intro h
    induction h with
    | refl => exact FiniteSearch.Reach.refl
    | step _ hs ih => exact FiniteSearch.Reach.step ih hs

/-- Search every reverse prefix through the finite monitor graph. -/
def prefixCheck (I : Instance k) (q : Fin k) (c : Word) : Bool :=
  match PeriodicMonitor.seed q c with
  | none => false
  | some start => safeState I q &&
      FiniteSearch.reachesAnyWithFuel (PeriodicMonitor.successors I c)
        (monitorCapacity k c) start (PeriodicMonitor.accepts I)

theorem prefixCheck_path (I : Instance k) (q : Fin k) (c : Word)
    (start : PeriodicMonitor.State k c) (hs : PeriodicMonitor.seed q c = some start) :
    prefixCheck I q c = true ↔ safeState I q = true ∧
      ∃ finish, PeriodicMonitor.Path I c start finish ∧
        PeriodicMonitor.accepts I finish = true := by
  simp only [prefixCheck, hs, Bool.and_eq_true]
  rw [FiniteSearch.reachesAnyWithFuel_correct (PeriodicMonitor.successors I c)
    (PeriodicMonitor.allStates k c) PeriodicMonitor.mem_allStates
    (monitorCapacity k c) (allStates_length_le k c)]
  simp only [reach_iff_path]

/-- Total C029 candidate decision. The semantic monitor equivalence supplies
its correctness under strong absorption. -/
def infiniteWitnessCheck (I : Instance k) : Bool :=
  (candidates I).any (fun qc => prefixCheck I qc.1 qc.2)

end Subtail.InfiniteDecision
