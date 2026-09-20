import Subtail.TerminalDecisionLazy

/-!
# Incremental cycle search for the complete C029 decision

Enumerate the same finite words without allocating the full candidate list.
A false initial safety gate excludes every successful prefix monitor. Equality
to the reference Boolean holds for every instance, without absorption.
-/
namespace Subtail.InfiniteDecisionLazy

open AbsorbingTerminal InfiniteDecision RankQueryEnumeration
open TreeSemantics SummaryAutomaton

/-- Exact-length existential search with structural termination. -/
def anyExact (xs : List α) : Nat → (List α → Bool) → Bool
  | 0, test => test []
  | n + 1, test => xs.any (fun x => anyExact xs n (fun w => test (x :: w)))

theorem anyExact_eq (xs : List α) (n : Nat) (test : List α → Bool) :
    anyExact xs n test = (exactLists xs n).any test := by
  induction n generalizing test with
  | zero => simp [anyExact, exactLists]
  | succ n ih => simp [anyExact, exactLists, List.any_flatMap, List.any_map, Function.comp_def, ih]

/-- Same increasing length order as the existing bounded word list. -/
def anyBounded (xs : List α) (n : Nat) (test : List α → Bool) : Bool :=
  (List.range (n + 1)).any (fun len => anyExact xs len test)

theorem anyBounded_eq (xs : List α) (n : Nat) (test : List α → Bool) :
    anyBounded xs n test = (boundedLists xs n).any test := by
  simp [anyBounded, boundedLists, List.any_flatMap, anyExact_eq]

def endpointCheck (I : Instance k) (q : Fin k) : Bool :=
  I.final.get q && (List.finRange k).all (fun p => !((I.flags.get p).get q))

theorem endpointCheck_of_cycleCheck (I : Instance k) (q : Fin k) (c : Word)
    (h : cycleCheck I q c = true) : endpointCheck I q = true := by
  simp only [cycleCheck, Bool.and_eq_true] at h
  simp only [endpointCheck, Bool.and_eq_true]
  exact ⟨h.1.1.2, h.1.2⟩

/-- Endpoint filtering and streaming preserve the complete original search. -/
def scan (I : Instance k) : Bool :=
  (List.finRange k).any fun q => endpointCheck I q &&
    anyBounded bools k (fun c => cycleCheck I q c && prefixCheck I q c)

theorem scan_eq (I : Instance k) : scan I = infiniteWitnessCheck I := by
  apply Bool.eq_iff_iff.mpr
  simp only [scan, anyBounded_eq, infiniteWitnessCheck, List.any_eq_true,
    Bool.and_eq_true]
  constructor
  · rintro ⟨q, _, _, c, _, hc, hp⟩
    exact ⟨(q, c), (mem_candidates I q c).mpr hc, hp⟩
  · rintro ⟨⟨q, c⟩, hm, hp⟩
    have hc := (mem_candidates I q c).mp hm
    have hlen := (cycleCheck_correct I q c).mp hc |>.2.1
    refine ⟨q, List.mem_finRange q, endpointCheck_of_cycleCheck I q c hc,
      c, ?_, hc, hp⟩
    exact (mem_boundedLists bools k c).mpr ⟨hlen, fun a _ => mem_bools a⟩

theorem initial_safe_of_infiniteWitnessCheck (I : Instance k)
    (h : infiniteWitnessCheck I = true) : safeState I I.initial = true := by
  obtain ⟨⟨q, c⟩, hm, hp⟩ := List.any_eq_true.mp h
  obtain ⟨w, hw, _⟩ := (candidate_prefixCheck_correct I q c hm).mp hp
  exact (safeCut_zero_iff I I.initial w).mp (hw.2 0 (Nat.zero_le _))

def infiniteWitnessCheckLazy (I : Instance k) : Bool :=
  safeState I I.initial && scan I

theorem infiniteWitnessCheckLazy_eq (I : Instance k) :
    infiniteWitnessCheckLazy I = infiniteWitnessCheck I := by
  rw [infiniteWitnessCheckLazy, scan_eq]
  cases h : infiniteWitnessCheck I with
  | false => simp
  | true => simp [initial_safe_of_infiniteWitnessCheck I h]

theorem infiniteWitnessCheckLazy_correct (I : Instance k) (hA : Absorbing I) :
    infiniteWitnessCheckLazy I = true ↔ InfWitness I := by
  rw [infiniteWitnessCheckLazy_eq]
  exact infiniteWitnessCheck_correct I hA

/-- Complete raw decision; the summary and terminal branch are unchanged. -/
def rawNormalizedEntailsCheckLazy (C : List (Constraint n)) (a b : Fin n) : Bool :=
  let I := summaryInstance C a b
  !(infiniteWitnessCheckLazy I || TerminalDecisionLazy.terminalWitnessCheckLazy (terminalize I))

theorem rawNormalizedEntailsCheckLazy_eq (C : List (Constraint n)) (a b : Fin n) :
    rawNormalizedEntailsCheckLazy C a b =
      TerminalDecisionLazy.rawNormalizedEntailsCheckLazy C a b := by
  simp only [rawNormalizedEntailsCheckLazy,
    TerminalDecisionLazy.rawNormalizedEntailsCheckLazy, infiniteWitnessCheckLazy_eq]

theorem rawNormalizedEntailsCheckLazy_correct (C : List (Constraint n)) (a b : Fin n) :
    rawNormalizedEntailsCheckLazy C a b = true ↔ Entails C a b := by
  rw [rawNormalizedEntailsCheckLazy_eq]
  exact TerminalDecisionLazy.rawNormalizedEntailsCheckLazy_correct C a b

end Subtail.InfiniteDecisionLazy
