import Subtail.Basic

/-!
# Conditional finite-budget decision

This file formalizes the logical shell of the memo's proposed decision route.
It does not provide the missing computable budget bound, and it does not
implement the BorderAvoid test.  Instead, it supplies an executable finite
enumeration once a concrete bound `F` and a concrete Boolean test `success`
are supplied.

The `success` argument is deliberately a function returning `Bool`.  Thus the
definition below can run once concrete functions are supplied.  The theorem
also keeps the two mathematical obligations explicit:

* soundness: a successful test gives a genuine BorderAvoid witness; and
* bounded coverage: every genuine BorderAvoid witness has some successful
  budget within the bound.

The `size` argument below is an explicit executable size function.  Its caller
chooses the finite encoding measure used by the bound.

The result is conditional.  In particular, supplying a noncomputable
function or proving the hypotheses by an oracle would not produce a decision
procedure for Problem 1.7.
-/

namespace Subtail

/-- The finite budget used by the conditional search. -/
def budgetLimit (size : Instance k → Nat) (F : Nat → Nat) (I : Instance k) : Nat :=
  F (size I)

/-!
`boundedSuccess` checks the budget before calling `success`.  The two nested
`List.range` calls therefore enumerate every pair whose coordinates are at
most the budget, while the guard makes the test run only for pairs satisfying
`L + D ≤ bound`.
-/
def boundedSuccess (success : Instance k → Nat → Nat → Bool)
    (I : Instance k) (bound L D : Nat) : Bool :=
  if L + D ≤ bound then success I L D else false

/--
Run the executable test over all pairs `(L,D)` with `L + D ≤ F(size I)`.

This is a finite Boolean computation.  It is intentionally parameterized by
`size`, `F`, and `success`; no computable budget bound or BorderAvoid
implementation is asserted here.
-/
def finiteBudgetDecision (size : Instance k → Nat) (F : Nat → Nat)
    (success : Instance k → Nat → Nat → Bool) (I : Instance k) : Bool :=
  let bound := budgetLimit size F I
  (List.range (bound + 1)).any (fun L =>
    (List.range (bound + 1)).any (fun D =>
      boundedSuccess success I bound L D))

theorem boundedSuccess_eq_true_iff
    (success : Instance k → Nat → Nat → Bool)
    (I : Instance k) (bound L D : Nat) :
    boundedSuccess success I bound L D = true ↔
      L + D ≤ bound ∧ success I L D = true := by
  simp [boundedSuccess]

theorem finiteBudgetDecision_eq_true_iff
    (size : Instance k → Nat)
    (F : Nat → Nat)
    (success : Instance k → Nat → Nat → Bool)
    (I : Instance k) :
    finiteBudgetDecision size F success I = true ↔
      ∃ L D, L + D ≤ budgetLimit size F I ∧ success I L D = true := by
  let bound := budgetLimit size F I
  constructor
  · intro h
    simp only [finiteBudgetDecision, budgetLimit, List.any_eq_true,
      List.mem_range] at h
    obtain ⟨L, hL, D, hD, hsuccess⟩ := h
    have hbounded := (boundedSuccess_eq_true_iff success I bound L D).mp
      hsuccess
    exact ⟨L, D, hbounded.1, hbounded.2⟩
  · rintro ⟨L, D, hbudget, hsuccess⟩
    simp only [finiteBudgetDecision, budgetLimit, List.any_eq_true,
      List.mem_range]
    have hL : L < bound + 1 := Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right L D)
      hbudget)
    have hD : D < bound + 1 := Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_left D L)
      (by simpa [Nat.add_comm] using hbudget))
    refine ⟨L, hL, D, hD, ?_⟩
    exact (boundedSuccess_eq_true_iff success I bound L D).mpr
      ⟨hbudget, hsuccess⟩

/-!
The next theorem is the exact conditional decision statement.  Both
hypotheses are quantified over the same fixed finite input type `Instance k`.
The first direction uses only test soundness.  The reverse direction uses
only existential bounded coverage.
-/
theorem finiteBudgetDecision_correct
    (size : Instance k → Nat)
    (F : Nat → Nat)
    (success : Instance k → Nat → Nat → Bool)
    (sound : ∀ (I : Instance k) (L D : Nat),
      success I L D = true → ∃ w, Witness I w)
    (coverage : ∀ (I : Instance k),
      (∃ w, Witness I w) →
        ∃ L D, L + D ≤ budgetLimit size F I ∧ success I L D = true)
    (I : Instance k) :
    finiteBudgetDecision size F success I = true ↔ ∃ w, Witness I w := by
  constructor
  · intro h
    obtain ⟨L, D, _, hsuccess⟩ :=
      (finiteBudgetDecision_eq_true_iff size F success I).mp h
    exact sound I L D hsuccess
  · intro hw
    exact (finiteBudgetDecision_eq_true_iff size F success I).mpr
      (coverage I hw)

/-!
Axiom audit (Lean 4.33.1):

Command:
`lake env lean Subtail/Conditional.lean`

The command also checks the `#print axioms` declaration at the end of this
file.  With Lean 4.33.1, the output is:

`'Subtail.finiteBudgetDecision_correct' depends on axioms: [propext, Quot.sound]`

Neither `sorryAx` nor a custom axiom occurs in the output.
-/
#print axioms finiteBudgetDecision_correct

end Subtail
