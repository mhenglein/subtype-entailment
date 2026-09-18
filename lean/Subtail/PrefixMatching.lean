import Subtail.RankMilestones

/-!
# Literal prefix matching

KMP transitions are finite maxima of literal prefix/suffix candidates.
The matching and fallback equations are proved, not assumed.
-/
namespace Subtail
namespace FirstReturnGraph
open TerminalRank RankMilestones

/-- Reading the next letter, with no out-of-bounds default. -/
def Next (w : Word) (i : Nat) (a : Bool) : Prop :=
  w.take (i + 1) = w.take i ++ [a]

instance (w : Word) (i : Nat) (a : Bool) : Decidable (Next w i a) :=
  inferInstanceAs (Decidable (_ = _))

theorem next_lt {w : Word} {i : Nat} {a : Bool} (h : Next w i a) :
    i < w.length := by
  have e := congrArg List.length h
  simp only [List.length_take, List.length_append, List.length_cons,
    List.length_nil] at e
  omega

theorem next_take {w : Word} {m i : Nat} {a : Bool} (hi : i < m) :
    Next (w.take m) i a ↔ Next w i a := by
  simp only [Next, List.take_take, Nat.min_eq_left (by omega : i + 1 ≤ m),
    Nat.min_eq_left (Nat.le_of_lt hi)]

theorem no_next_end (w : Word) (a : Bool) : ¬ Next w w.length a := by
  intro h
  have := next_lt h
  omega

theorem next_get {w : Word} {i : Nat} (hi : i < w.length) :
    Next w i (w[i]?.getD false) := by
  simp only [Next, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.take_succ_eq_append_getElem hi

/-- Removing a common final letter from a suffix comparison. -/
theorem suffix_snoc_iff (u v : Word) (a b : Bool) :
    (u ++ [a]).IsSuffix (v ++ [b]) ↔ a = b ∧ u.IsSuffix v := by
  constructor
  · rintro ⟨z, hz⟩
    have he := congrArg List.reverse hz
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append] at he
    have hc := List.cons.inj he
    refine ⟨hc.1, z, ?_⟩
    have ht := congrArg List.reverse hc.2
    simpa only [List.reverse_append, List.reverse_reverse] using ht
  · rintro ⟨rfl, z, hz⟩
    exact ⟨z, by simp only [← List.append_assoc, hz]⟩

theorem suffix_next_iff {w u : Word} {i : Nat} {a : Bool}
    (hi : i < w.length) :
    (w.take (i + 1)).IsSuffix (u ++ [a]) ↔
      (w.take i).IsSuffix u ∧ Next w i a := by
  have he := List.take_succ_eq_append_getElem hi
  rw [he, suffix_snoc_iff]
  simp only [Next, he, List.append_cancel_left_eq, List.cons.injEq,
    and_true]
  exact and_comm

/-- Border membership written as a literal suffix relation. -/
theorem border_iff_suffix {w : Word} {j h : Nat}
    (hj : j ≤ w.length) (hh : h ≤ j) :
    h ∈ borderLengths (w.take j) ↔ (w.take h).IsSuffix (w.take j) := by
  have hhw : h ≤ w.length := Nat.le_trans hh hj
  simp only [mem_borderLengths, List.length_take_of_le hj, List.take_take,
    Nat.min_eq_left hh, List.suffix_iff_eq_drop,
    List.length_take_of_le hhw]
  exact and_iff_right hh

/-- All possible next match lengths: zero and extended matching borders. -/
def candidates (w : Word) (j : Nat) (a : Bool) : List Nat :=
  0 :: (((borderLengths (w.take j)).filter fun h => decide (Next w h a)).map
    fun h => h + 1)

/-- KMP edge, defined by a finite maximum, not by the surgery equations. -/
def advance (w : Word) (j : Nat) (a : Bool) : Nat :=
  maxNat (candidates w j a)

theorem mem_candidates {w : Word} {j n : Nat} {a : Bool} :
    n ∈ candidates w j a ↔ n = 0 ∨
      ∃ h, h ∈ borderLengths (w.take j) ∧ Next w h a ∧ n = h + 1 := by
  simp only [candidates, List.mem_cons, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro (h | ⟨r, ⟨hb, ha⟩, hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, hb, ha, hn.symm⟩
  · rintro (h | ⟨r, hb, ha, hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, ⟨hb, ha⟩, hn.symm⟩

theorem advance_mem (w : Word) (j : Nat) (a : Bool) :
    advance w j a ∈ candidates w j a :=
  maxNat_mem (by simp [candidates])

theorem advance_max {w : Word} {j n : Nat} {a : Bool}
    (h : n ∈ candidates w j a) : n ≤ advance w j a := le_maxNat h

theorem advance_le {w : Word} {j b : Nat} {a : Bool}
    (h : ∀ n ∈ candidates w j a, n ≤ b) : advance w j a ≤ b :=
  h _ (advance_mem w j a)

/-- Exact agreement with the literal longest-prefix/suffix definition. -/
theorem candidates_literal {w : Word} {j n : Nat} {a : Bool}
    (hj : j ≤ w.length) :
    n ∈ candidates w j a ↔
      n ≤ w.length ∧ (w.take n).IsSuffix (w.take j ++ [a]) := by
  rw [mem_candidates]
  constructor
  · rintro (rfl | ⟨h, hb, ha, rfl⟩)
    · simp
    · have hlt := next_lt ha
      have hh : h ≤ j := by
        simpa only [List.length_take_of_le hj] using (mem_borderLengths.mp hb).1
      exact ⟨by omega, (suffix_next_iff hlt).mpr
        ⟨(border_iff_suffix hj hh).mp hb, ha⟩⟩
  · rintro ⟨hn, hs⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ h =>
      have hh : h ≤ j := by
        have he := hs.length_le
        simp only [List.length_take_of_le hn, List.length_append,
          List.length_take_of_le hj, List.length_cons, List.length_nil] at he
        omega
      obtain ⟨hpre, hnext⟩ := (suffix_next_iff (by omega : h < w.length)).mp hs
      exact Or.inr ⟨h, (border_iff_suffix hj hh).mpr hpre, hnext, rfl⟩

theorem advance_literal (w : Word) {j : Nat} (hj : j ≤ w.length) (a : Bool) :
    advance w j a ≤ w.length ∧
    (w.take (advance w j a)).IsSuffix (w.take j ++ [a]) ∧
    ∀ n, n ≤ w.length → (w.take n).IsSuffix (w.take j ++ [a]) →
      n ≤ advance w j a := by
  have h := (candidates_literal hj).mp (advance_mem w j a)
  exact ⟨h.1, h.2, fun n hn hs => advance_max ((candidates_literal hj).mpr ⟨hn, hs⟩)⟩

theorem advance_bound (w : Word) (j : Nat) (a : Bool) :
    advance w j a ≤ j + 1 := by
  apply advance_le
  intro n hn
  rcases mem_candidates.mp hn with rfl | ⟨h, hb, _, rfl⟩
  · omega
  · have hh := (mem_borderLengths.mp hb).1
    simp only [List.length_take] at hh
    omega

theorem advance_match {w : Word} {j : Nat} {a : Bool}
    (ha : Next w j a) : advance w j a = j + 1 := by
  apply Nat.le_antisymm (advance_bound w j a)
  have hj : j ≤ w.length := Nat.le_of_lt (next_lt ha)
  apply advance_max
  apply mem_candidates.mpr
  right
  refine ⟨j, ?_, ha, rfl⟩
  simpa only [List.length_take_of_le hj] using full_mem (w.take j)

theorem advance_congr {w v : Word} {i j : Nat} {a : Bool}
    (h : ∀ n, n ∈ candidates w i a ↔ n ∈ candidates v j a) :
    advance w i a = advance v j a := by
  apply Nat.le_antisymm
  · exact advance_max ((h _).mp (advance_mem w i a))
  · exact advance_max ((h _).mpr (advance_mem v j a))

/-- Before the old endpoint, enlarging the reference changes no K edge. -/
theorem advance_prefix {w : Word} {m j : Nat} (hj : j < m) (a : Bool) :
    advance (w.take m) j a = advance w j a := by
  apply advance_congr
  intro n
  simp only [mem_candidates, List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  constructor <;> rintro (hz | ⟨h, hb, ha, hn⟩)
  · exact Or.inl hz
  · right
    have hh : h < m := by
      have hh := (mem_borderLengths.mp hb).1
      simp only [List.length_take] at hh
      omega
    exact ⟨h, hb, (next_take hh).mp ha, hn⟩
  · exact Or.inl hz
  · right
    have hh : h < m := by
      have hh := (mem_borderLengths.mp hb).1
      simp only [List.length_take] at hh
      omega
    exact ⟨h, hb, (next_take hh).mpr ha, hn⟩

/-- Mismatches and the full-prefix endpoint fall back through the failure edge. -/
theorem advance_fallback {w : Word} {j : Nat} {a : Bool}
    (hj : j ≤ w.length) (hp : 0 < j) (ha : ¬ Next w j a) :
    advance w j a = advance w (failureParent (w.take j)) a := by
  have hlen : (w.take j).length = j := List.length_take_of_le hj
  have hpar := failureParent_spec (w.take j) (by omega)
  have hlt : failureParent (w.take j) < j := by omega
  apply advance_congr
  intro n
  simp only [mem_candidates]
  constructor <;> rintro (hz | ⟨h, hb, hn, he⟩)
  · exact Or.inl hz
  · right
    rcases (border_decomposition (w.take j) (by omega) h).mp hb with hh | hh
    · have hhj : h = j := by omega
      exact False.elim (ha (hhj ▸ hn))
    · have heq : (w.take j).take (failureParent (w.take j)) =
          w.take (failureParent (w.take j)) := by
        simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
      rw [heq] at hh
      exact ⟨h, hh, hn, he⟩
  · exact Or.inl hz
  · right
    have hh := (border_decomposition (w.take j) (by omega) h).mpr (Or.inr
      (by simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)] using hb))
    exact ⟨h, hh, hn, he⟩

end FirstReturnGraph
end Subtail
