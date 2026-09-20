import FOnlyAstra
import Subtail.SmallerCompilerAstra

/-!
# Original F: checked composition using a separately owned compiler

F-only contribution, 2026-09-20. The independent one-fewer-promotion ordinary
proof is in notes/2026-09-20-f-only-astra.md and does NOT use this dependency.

This second route imports SmallerCompilerAstra at the exact read-only source
acf0524ffdbc9f407797b68b8953a39e1f79cf5d. That contributor owns the compiler
construction, filter, coverage count and size proof. Here only its exported
contract and concrete-diagram membership are consumed. Neither that source
nor any original core definition is changed.

A semantic-and-weight contract alone is not used to assert a length estimate.
Every emitted clause is traced to an existing concrete diagram; compile_bounded
then reconstructs ONE common extension and preserves the whole conjunction.
-/
namespace Subtail.FOnlyCompilerBridge
open RankQuery RankQueryCompiler RankQueryEnumeration RankQueryUnwind
open FOnlyAstra

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

variable {k : Nat}

/-- Exact old-U length factor, justified by common concrete reconstruction,
not by independent per-atom witnesses or clause size alone. -/
theorem small_preimage_bounded (I : Instance k) (phi : Query k) (B : Reference k)
    (hB : SafeReference I B)
    (hsat : Sat (prefixGraph I B) (SmallerCompilerAstra.preSmall I phi)) :
    ∃ C : Reference k, FirstReturnExt I B C ∧ Sat (prefixGraph I C) phi ∧
      C.word.length + 1 <= (B.word.length + 1) * (closureBound k (weight phi) + 2) := by
  obtain ⟨P, hP, hsP⟩ := hsat
  have hw := (SmallerCompilerAstra.closureFor I).2 phi P hP
  unfold SmallerCompilerAstra.preSmall at hP
  obtain ⟨c, hc, hPc⟩ := List.mem_flatMap.mp hP
  obtain ⟨D, _, _, hD⟩ := (SmallerCompilerAstra.mem_preClause I c P).mp hPc
  obtain ⟨C, hC, hsC, hlen⟩ :=
    RankQueryLengthBound.compile_bounded I c D B hB hD hsP
  exact ⟨C, hC, ⟨c, hc, hsC⟩, Nat.le_trans hlen
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw 2))⟩

theorem oldGrowth_step (k h : Nat) : oldGrowth k h <= oldGrowth k (h + 1) := by
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- The original T recurrence bounds shared-reference quantitative unwind. -/
theorem promoted_finish_original_bound (I : Instance k) : forall h (B : Reference k),
    SafeReference I B ->
    Sat (prefixGraph I B) (promote (SmallerCompilerAstra.preSmall I) (finishQuery I) h) ->
    ∃ w : Word, Witness I w ∧
      w.length + 1 <= (B.word.length + 1) * (k + 1) * oldGrowth k h := by
  intro h
  induction h with
  | zero =>
    intro B hB hs
    simpa only [promote, oldGrowth, Nat.mul_one] using
      RankQueryLengthBound.finish_bounded I B hB hs
  | succ h ih =>
    intro B hB hs
    rw [promote, sat_append] at hs
    rcases hs with hprev | hpre
    . obtain ⟨w, hw, hlen⟩ := ih B hB hprev
      exact ⟨w, hw, Nat.le_trans hlen (Nat.mul_le_mul_left _ (oldGrowth_step k h))⟩
    . obtain ⟨C, hC, hsat, hlen⟩ := small_preimage_bounded I _ B hB hpre
      have hweight := closureBound_mono k
        (weight_promote_finish_le I (SmallerCompilerAstra.preSmall I)
          (SmallerCompilerAstra.closureFor I) h)
      have hCsize : C.word.length + 1 <= (B.word.length + 1) *
          (RankQueryUnwind.weightBudget k (h + 1) + 2) :=
        Nat.le_trans hlen (Nat.mul_le_mul_left _ (Nat.add_le_add_right hweight 2))
      obtain ⟨w, hw, hwlen⟩ := ih C hC.safe hsat
      refine ⟨w, hw, Nat.le_trans hwlen ?_⟩
      calc
        (C.word.length + 1) * (k + 1) * oldGrowth k h <=
            ((B.word.length + 1) * (RankQueryUnwind.weightBudget k (h + 1) + 2)) *
              (k + 1) * oldGrowth k h :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hCsize)
        _ = (B.word.length + 1) * (k + 1) * oldGrowth k (h + 1) := by
          rw [oldGrowth]
          ac_rfl

/-- The existing qualitative rank coverage transfers through exact chain
semantics. No numerical witness bound is used for this direction. -/
theorem coverage_small (I : Instance k) (B : Reference k) (hB : SafeReference I B)
    (h : Nat)
    (hs : Sat (prefixGraph I B)
      (promote (preimage I RankQueryCoverage.budget) (finishQuery I) h)) :
    Sat (prefixGraph I B) (promote (SmallerCompilerAstra.preSmall I) (finishQuery I) h) := by
  have hc := (RankQuerySemanticUnwind.sat_promote_preimage_iff I
    (finishQuery I) h B hB).mp hs
  exact (sat_promote_iff I (SmallerCompilerAstra.preSmall I)
    (SmallerCompilerAstra.closureFor I) (finishQuery I) h B hB).mpr hc

/-- Exact C080 F, for all original finite binary terminal instances.
No caller compiler contract, witness cap or new semantic premise remains. -/
theorem terminal_witness_original_bounded (I : Instance k)
    (ht : TerminalRank.TerminalFinals I) (h : ∃ w : Word, Witness I w) :
    ∃ w : Word, Witness I w ∧ w.length <= originalF k := by
  by_cases hk : k = 1
  . subst k
    obtain ⟨w, hw⟩ := h
    have he := RankQueryLengthBound.one_state_empty I ht hw
    subst w
    exact ⟨[], hw, by simp [originalF]⟩
  . have hs := (RankQueryDecision.rankDecisionStatement I ht).mp h
    rcases hs with hempty | ⟨a, f, p, hB, hsat⟩
    . exact ⟨[], hempty, Nat.zero_le _⟩
    . have hsmall := coverage_small I (oneLetter a f p) hB (k - 2) hsat
      obtain ⟨w, hw, hlen⟩ :=
        promoted_finish_original_bound I (k - 2) (oneLetter a f p) hB hsmall
      have hn : (oneLetter a f p).word.length + 1 = 2 := rfl
      rw [hn] at hlen
      exact ⟨w, hw, by simp only [originalF, hk, if_false]; omega⟩

/-- The complete original shortest-terminal-witness bound F. -/
theorem original_F (I : Instance k) (ht : TerminalRank.TerminalFinals I) :
    (∃ w : Word, Witness I w) ↔
      ∃ w : Word, Witness I w ∧ w.length <= originalF k :=
  ⟨terminal_witness_original_bounded I ht, fun ⟨w, hw, _⟩ => ⟨w, hw⟩⟩

#guard originalF 1 = 0
#guard originalF 2 = 6
#print original_F
#print axioms small_preimage_bounded
#print axioms oldGrowth_step
#print axioms promoted_finish_original_bound
#print axioms coverage_small
#print axioms terminal_witness_original_bounded
#print axioms original_F
end Subtail.FOnlyCompilerBridge
