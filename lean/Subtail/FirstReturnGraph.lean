import Subtail.PrefixMatching

namespace Subtail
namespace FirstReturnGraph
open TerminalRank RankMilestones

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
          simpa only [p, List.take_take, Nat.min_eq_left (Nat.le_of_lt hplt)] using hb
        have hsf := (border_iff_suffix hj (by omega : h ≤ j)).mp hbj
        have he := (suffix_next_iff (next_lt hnextbit)).mpr ⟨hsf, hnextbit⟩
        have hsuf : (w.take (h+1)).IsSuffix (w.take (j+1)) := by
          rw [ha]
          exact he
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
          simpa only [p, List.take_take, Nat.min_eq_left (Nat.le_of_lt hplt)] using hbp
        exact Or.inr ⟨h, hbp', hn, rfl⟩
  change failureParent (w.take (j+1)) = advance w p a
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
  have hmlt : m < w.length := hr.1
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
