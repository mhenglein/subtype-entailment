import Subtail.EntailmentDecision

/-!
# Lazy wrapper for the terminal witness decision

This module keeps the existing terminal reference implementation unchanged.  It
adds a Boolean-equivalent wrapper which first checks whether any of the finite
one-letter references is safe, and constructs the promoted query only if that
gate succeeds.  The query is still built once and shared by the original
candidate scan.
-/
namespace Subtail.TerminalDecisionLazy

open Subtail
open TreeSemantics ExpressionNormalization SummaryAutomaton AbsorbingTerminal
  InfiniteDecision
open RankQuery RankQueryDecision RankQueryEnumeration TerminalRank

variable {k : Nat}

/-- Whether any reference considered by the terminal decision passes its exact
finite safety predicate.  This is only an evaluation-order gate. -/
def safeOneLetterExists (I : Instance k) : Bool :=
  [false, true].any fun a =>
    (List.finRange k).any fun f =>
      (List.finRange k).any fun p =>
        safeReferenceCheck I (oneLetter a f p)

/-- The original terminal candidate scan, parameterized by an already-built
promoted query. -/
def terminalCandidateScan (I : Instance k) (phi : Query k) : Bool :=
  [false, true].any fun a =>
    (List.finRange k).any fun f => (List.finRange k).any fun p =>
      safeReferenceCheck I (oneLetter a f p) &&
        satCheck (prefixGraph I (oneLetter a f p)) phi

/-- The terminal decision with a global safe-reference gate.  The promoted
query is built once only after the gate succeeds. -/
def terminalWitnessCheckLazy (I : Instance k) : Bool :=
  witnessCheck I [] ||
    if safeOneLetterExists I then
      terminalCandidateScan I
        (promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2))
    else false

/-- A successful candidate scan necessarily has a safe one-letter reference. -/
theorem terminalCandidateScan_true_implies_safeOneLetterExists
    (I : Instance k) (phi : Query k)
    (h : terminalCandidateScan I phi = true) :
    safeOneLetterExists I = true := by
  unfold terminalCandidateScan at h
  obtain ⟨a, ha, hrest⟩ := List.any_eq_true.mp h
  obtain ⟨f, hf, hrest⟩ := List.any_eq_true.mp hrest
  obtain ⟨p, hp, hcheck⟩ := List.any_eq_true.mp hrest
  have hs_pair :
      safeReferenceCheck I (oneLetter a f p) = true ∧
        satCheck (prefixGraph I (oneLetter a f p)) phi = true := by
    simpa only [Bool.and_eq_true] using hcheck
  have hs : safeReferenceCheck I (oneLetter a f p) = true := hs_pair.1
  apply List.any_eq_true.mpr
  refine ⟨a, ha, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨f, hf, ?_⟩
  exact List.any_eq_true.mpr ⟨p, hp, hs⟩

/-- A false global gate makes the candidate scan false, for every query. -/
theorem terminalCandidateScan_false_of_safeOneLetterExists_false
    (I : Instance k) (phi : Query k)
    (h : safeOneLetterExists I = false) :
    terminalCandidateScan I phi = false := by
  cases hs : terminalCandidateScan I phi with
  | false => rfl
  | true =>
      have hg := terminalCandidateScan_true_implies_safeOneLetterExists I phi hs
      simp [h] at hg

/-- The global gate does not change the result of the original terminal scan.
The only new case is a false gate, where the scan is false by the preceding
lemmas. -/
theorem terminalWitnessCheckLazy_eq (I : Instance k) :
    terminalWitnessCheckLazy I = RankQueryDecision.terminalWitnessCheck I := by
  by_cases hw : witnessCheck I [] = true
  · simp [terminalWitnessCheckLazy, RankQueryDecision.terminalWitnessCheck, hw]
  · have hw' : witnessCheck I [] = false := by
      cases h : witnessCheck I [] <;> simp_all
    by_cases hg : safeOneLetterExists I = true
    · simp [terminalWitnessCheckLazy, RankQueryDecision.terminalWitnessCheck,
        terminalCandidateScan, hw', hg]
    · have hg' : safeOneLetterExists I = false := by
        cases h : safeOneLetterExists I <;> simp_all
      let phi : Query k :=
        promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2)
      have hscan := terminalCandidateScan_false_of_safeOneLetterExists_false I phi hg'
      have hscan' :
          (let q := promote (preimage I RankQueryCoverage.budget)
              (finishQuery I) (k - 2)
           [false, true].any fun a =>
             (List.finRange k).any fun f => (List.finRange k).any fun p =>
               safeReferenceCheck I (oneLetter a f p) &&
                 satCheck (prefixGraph I (oneLetter a f p)) q) = false := by
        change terminalCandidateScan I phi = false
        exact hscan
      simp [terminalWitnessCheckLazy, RankQueryDecision.terminalWitnessCheck,
        hw', hg, hscan']

/-- The gated wrapper has the same terminal candidate specification.  This is
    the syntactic candidate statement; semantic witness completeness also
    requires terminal final states, as stated below. -/
theorem terminalWitnessCheckLazy_correct (I : Instance k) :
    terminalWitnessCheckLazy I = true ↔
      Witness I [] ∨ ∃ (a : Bool) (f p : Fin k),
        SafeReference I (oneLetter a f p) ∧
        Sat (prefixGraph I (oneLetter a f p))
          (promote (preimage I RankQueryCoverage.budget) (finishQuery I) (k - 2)) := by
  rw [terminalWitnessCheckLazy_eq]
  exact RankQueryDecision.terminalWitnessCheck_spec I

/-- Under terminal final states, the gated terminal check is equivalent to
    existence of an original witness. -/
theorem terminalWitnessCheckLazy_witness_iff (I : Instance k)
    (hT : TerminalFinals I) :
    terminalWitnessCheckLazy I = true ↔ ∃ w : Word, Witness I w := by
  rw [terminalWitnessCheckLazy_eq]
  exact RankQueryDecision.terminalWitnessCheck_correct I hT

/-- Raw normalized entailment with the globally gated terminal branch.  The
    infinite branch and all input constructions are unchanged. -/
def rawNormalizedEntailsCheckLazy {n : Nat}
    (C : List (Constraint n)) (a b : Fin n) : Bool :=
  let I := summaryInstance C a b
  !(infiniteWitnessCheck I || terminalWitnessCheckLazy (terminalize I))

theorem rawNormalizedEntailsCheckLazy_eq {n : Nat}
    (C : List (Constraint n)) (a b : Fin n) :
    rawNormalizedEntailsCheckLazy C a b =
      Subtail.EntailmentDecision.rawNormalizedEntailsCheck C a b := by
  simp only [rawNormalizedEntailsCheckLazy,
    Subtail.EntailmentDecision.rawNormalizedEntailsCheck]
  rw [terminalWitnessCheckLazy_eq]

theorem rawNormalizedEntailsCheckLazy_correct {n : Nat}
    (C : List (Constraint n)) (a b : Fin n) :
    rawNormalizedEntailsCheckLazy C a b = true ↔ Entails C a b := by
  rw [rawNormalizedEntailsCheckLazy_eq]
  exact Subtail.EntailmentDecision.rawNormalizedEntailsCheck_correct C a b

/-- Normalized entailment with exactly the original cheap guards, replacing
    only the terminal backend call by the globally gated wrapper. -/
def normalizedEntailsCheckLazy {n : Nat}
    (C : List (Constraint n)) (a b : Fin n) : Bool :=
  if a = b then true
  else if Constraint.leq a b ∈ C then true
  else if CanonicalReachability.satCheck C then
    if CanonicalReachability.separationCheck C a b [] then false
    else rawNormalizedEntailsCheckLazy C a b
  else true

theorem normalizedEntailsCheckLazy_eq {n : Nat}
    (C : List (Constraint n)) (a b : Fin n) :
    normalizedEntailsCheckLazy C a b =
      Subtail.EntailmentDecision.normalizedEntailsCheck C a b := by
  by_cases hab : a = b
  · simp [normalizedEntailsCheckLazy,
      Subtail.EntailmentDecision.normalizedEntailsCheck, hab]
  by_cases hp : Constraint.leq a b ∈ C
  · simp [normalizedEntailsCheckLazy,
      Subtail.EntailmentDecision.normalizedEntailsCheck, hab, hp]
  by_cases hs : CanonicalReachability.satCheck C = true
  · by_cases hw : CanonicalReachability.separationCheck C a b [] = true
    · simp [normalizedEntailsCheckLazy,
        Subtail.EntailmentDecision.normalizedEntailsCheck, hab, hp, hs, hw]
    · simp [normalizedEntailsCheckLazy,
        Subtail.EntailmentDecision.normalizedEntailsCheck, hab, hp, hs, hw,
        rawNormalizedEntailsCheckLazy_eq]
  · simp [normalizedEntailsCheckLazy,
      Subtail.EntailmentDecision.normalizedEntailsCheck, hab, hp, hs]

theorem normalizedEntailsCheckLazy_correct {n : Nat}
    (C : List (Constraint n)) (a b : Fin n) :
    normalizedEntailsCheckLazy C a b = true ↔ Entails C a b := by
  rw [normalizedEntailsCheckLazy_eq]
  exact Subtail.EntailmentDecision.normalizedEntailsCheck_correct C a b

/-- Full expression-level entailment with the existing normalization and
    naming pipeline, replacing only the normalized backend call. -/
def entailsCheckLazy {n : Nat} (G : Input n) (s t : Expr n) : Bool :=
  normalizedEntailsCheckLazy (normalized G s t)
    ((naming G s t).ref s) ((naming G s t).ref t)

theorem entailsCheckLazy_eq {n : Nat} (G : Input n) (s t : Expr n) :
    entailsCheckLazy G s t = Subtail.EntailmentDecision.entailsCheck G s t := by
  unfold entailsCheckLazy Subtail.EntailmentDecision.entailsCheck
  rw [normalizedEntailsCheckLazy_eq]

theorem entailsCheckLazy_correct {n : Nat} (G : Input n) (s t : Expr n) :
    entailsCheckLazy G s t = true ↔ ExprEntails G s t := by
  rw [entailsCheckLazy_eq]
  exact Subtail.EntailmentDecision.entailsCheck_correct G s t

end Subtail.TerminalDecisionLazy
