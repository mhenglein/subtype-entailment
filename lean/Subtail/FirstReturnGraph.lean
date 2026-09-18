import Subtail.RankMilestones

/-!
# First-return prefix graphs

Literal prefix/suffix semantics, followed by a derived local graph update.
No query-closure theorem or word-length bound is assumed.
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

/-- Exact proper-border update under one physical next letter. -/
theorem parent_next {w : Word} {j : Nat} {a : Bool}
    (hp : 0 < j) (ha : Next w j a) :
    failureParent (w.take (j + 1)) = advance w (failureParent (w.take j)) a := by
  have hjlt := next_lt ha
  have hj : j ≤ w.length := by omega
  have hlen : (w.take j).length = j := List.length_take_of_le hj
  have hlen1 : (w.take (j+1)).length = j+1 := List.length_take_of_le (by omega)
  have hs := failureParent_spec (w.take j) (by omega)
  have hplt : failureParent (w.take j) < j := by omega
  have hnext := failureParent_spec (w.take (j+1)) (by omega)
  let p := failureParent (w.take j)
  have hsub : ∀ n, n ∈ candidates w p a ↔
      n ∈ borderLengths (w.take (j+1)) ∧ n < j+1 := by
    intro n
    rw [mem_candidates]
    constructor
    · rintro (rfl | ⟨h, hb, hnextbit, rfl⟩)
      · exact ⟨zero_mem _, by omega⟩
      · have hhp : h ≤ p := by
          simpa only [List.length_take_of_le (by omega : p ≤ w.length)] using
            (mem_borderLengths.mp hb).1
        have hbj : h ∈ borderLengths (w.take j) := by
          apply (borders_below_border hs.1 hhp).mp
          simpa only [List.take_take, Nat.min_eq_left (by omega : p ≤ j)] using hb
        have hsf := (border_iff_suffix hj (by omega : h ≤ j)).mp hbj
        have he := (suffix_next_iff (next_lt hnextbit)).mpr ⟨hsf, hnextbit⟩
        have hsuf : (w.take (h+1)).IsSuffix (w.take (j+1)) := by
          simpa only [ha] using he
        exact ⟨(border_iff_suffix (by omega) (by omega)).mpr hsuf, by omega⟩
    · rintro ⟨hb, hnj⟩
      cases n with
      | zero => exact Or.inl rfl
      | succ h =>
        have hsuf := (border_iff_suffix (by omega : j+1 ≤ w.length)
          (by omega : h+1 ≤ j+1)).mp hb
        rw [ha] at hsuf
        obtain ⟨ht, hn⟩ := (suffix_next_iff (by omega : h < w.length)).mp hsuf
        have hbj := (border_iff_suffix hj (by omega : h ≤ j)).mpr ht
        have hhp : h ≤ p := hs.2.2 h hbj (by omega)
        have hbp := (borders_below_border hs.1 hhp).mpr hbj
        have hbp' : h ∈ borderLengths (w.take p) := by
          simpa only [List.take_take, Nat.min_eq_left (by omega : p ≤ j)] using hbp
        exact Or.inr ⟨h, hbp', hn, rfl⟩
  apply Nat.le_antisymm
  · apply advance_max
    exact (hsub _).mpr ⟨hnext.1, by omega⟩
  · have hh := (hsub _).mp (advance_mem w p a)
    exact hnext.2.2 _ hh.1 (by omega)

/-- Generator cursor: reads extension letters in the OLD graph only.
The old word is w.take m; new failure parents are never evaluated here. -/
def cursor (w : Word) (m : Nat) : Nat → Nat
  | 0 => failureParent (w.take m)
  | d + 1 => advance (w.take m) (cursor w m d) (w[m+d]?.getD false)

/-- The old-graph generator computes exactly the new failure targets. -/
theorem cursor_eq_parent {w : Word} {m : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length) {d : Nat}
    (hd : m + d ≤ w.length) :
    cursor w m d = failureParent (w.take (m+d)) := by
  induction d with
  | zero => simp only [cursor, Nat.add_zero]
  | succ d ih =>
    have hd' : m+d ≤ w.length := by omega
    have hpos : 0 < m+d := by omega
    have hlt : m+d < w.length := by omega
    have hp : failureParent (w.take (m+d)) < m := by
      by_cases hz : d = 0
      · subst d
        simpa only [Nat.add_zero, List.length_take_of_le (by omega : m ≤ w.length)]
          using (failureParent_spec (w.take m)
            (by simpa only [List.length_take_of_le (by omega : m ≤ w.length)] using hm)).2.1
      · exact first_return_internal_parent_lt hr (by omega) hlt
    rw [cursor, ih hd', advance_prefix hp]
    have he := parent_next hpos (next_get hlt)
    simpa only [Nat.add_assoc] using he.symm

/-- The computed cursor first reaches the old endpoint exactly at the return. -/
theorem cursor_first_hit {w : Word} {m : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length) :
    cursor w m (w.length-m) = m ∧
    ∀ d, 0 < d → d < w.length-m → cursor w m d < m := by
  constructor
  · rw [cursor_eq_parent hm hr (by omega)]
    have he : m + (w.length-m) = w.length := by omega
    rw [he]
    exact first_return_parent hr
  · intro d hd hdn
    rw [cursor_eq_parent hm hr (by omega)]
    exact first_return_internal_parent_lt hr (by omega) (by omega)

/-- Complete first-return K edge specification. Old K edges are reused. -/
def surgeryK (w : Word) (m j : Nat) (a : Bool) : Nat :=
  if j < m then advance (w.take m) j a
  else if j = m then
    if Next w m a then m+1 else advance (w.take m) m a
  else if j < w.length then
    if Next w j a then j+1 else advance (w.take m) (cursor w m (j-m)) a
  else if Next w m a then m+1 else advance (w.take m) m a

/-- All K edges agree, including full-endpoint fallback and singleton wraps. -/
theorem surgeryK_correct {w : Word} {m : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length) {j : Nat}
    (hj : j ≤ w.length) (a : Bool) : surgeryK w m j a = advance w j a := by
  have hmlt : m < w.length := hr.1
  have hmlen : (w.take m).length = m := List.length_take_of_le (by omega)
  have hold : ∀ a, advance w m a =
      if Next w m a then m+1 else advance (w.take m) m a := by
    intro b
    by_cases hb : Next w m b
    · simp only [hb, if_true, advance_match hb]
    · simp only [hb, if_false]
      have hpb := failureParent_spec (w.take m) (by omega)
      have hp : failureParent (w.take m) < m := by omega
      rw [advance_fallback (by omega) hm hb]
      have hb' : ¬ Next (w.take m) m b := by
        simpa only [hmlen] using no_next_end (w.take m) b
      rw [advance_fallback (by omega : m ≤ (w.take m).length) hm hb']
      simp only [List.take_take, Nat.min_self]
      exact (advance_prefix hp b).symm
  by_cases h0 : j < m
  · simp only [surgeryK, h0, if_true]
    exact advance_prefix h0 a
  · by_cases h1 : j = m
    · subst j
      simp only [surgeryK, Nat.lt_irrefl, if_false, if_true]
      exact (hold a).symm
    · by_cases h2 : j < w.length
      · simp only [surgeryK, h0, h1, h2, if_false, if_true]
        by_cases hn : Next w j a
        · simp only [hn, if_true]
          exact (advance_match hn).symm
        · simp only [hn, if_false]
          have hp := first_return_internal_parent_lt hr (by omega : m < j) h2
          rw [cursor_eq_parent hm hr (by omega)]
          have he : m+(j-m) = j := by omega
          rw [he, advance_prefix hp, advance_fallback hj (by omega) hn]
      · have he : j = w.length := by omega
        subst j
        simp only [surgeryK, h0, h1, Nat.lt_irrefl, if_false]
        rw [advance_fallback (Nat.le_refl _) (by omega) (no_next_end w a)]
        rw [first_return_parent hr]
        exact (hold a).symm

end FirstReturnGraph
end Subtail
