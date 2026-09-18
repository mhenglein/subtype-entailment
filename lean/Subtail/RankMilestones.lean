import Subtail.TerminalRank

/-!
# Literal border ranks and first-return milestones

This proves the combinatorial interface between terminal border cardinality
and the candidate's rank milestones. It does not assume or prove uniform query
closure. Ranks and failure parents are computable from finite binary words.
-/
namespace Subtail
namespace RankMilestones
open TerminalRank

/-- Maximum of a finite list of naturals, with zero for the empty list. -/
def maxNat : List Nat → Nat
  | [] => 0
  | a :: l => max a (maxNat l)

theorem le_maxNat {l : List Nat} {a : Nat} (ha : a ∈ l) : a ≤ maxNat l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ha) (Nat.le_max_right _ _)

theorem maxNat_mem {l : List Nat} (hz : 0 ∈ l) : maxNat l ∈ l := by
  have aux : ∀ l : List Nat, maxNat l = 0 ∨ maxNat l ∈ l := by
    intro l
    induction l with
    | nil => exact Or.inl rfl
    | cons a l ih =>
      by_cases h : maxNat l ≤ a
      · right
        simp [maxNat, Nat.max_eq_left h]
      · rcases ih with he | hm
        · omega
        · right
          simp [maxNat, Nat.max_eq_right (by omega : a ≤ maxNat l), hm]
  rcases aux l with he | hm
  · simpa [he] using hz
  · exact hm

/-- The longest proper border; it is zero when the word is empty. -/
def failureParent (w : Word) : Nat :=
  maxNat ((borderLengths w).filter fun n => n < w.length)

/-- Number of nonempty borders, including the whole word when nonempty. -/
def rank (w : Word) : Nat := positiveBorderCount w

theorem zero_mem (w : Word) : 0 ∈ borderLengths w := by
  simp [mem_borderLengths]

theorem full_mem (w : Word) : w.length ∈ borderLengths w := by
  simp [mem_borderLengths]

theorem borders_nodup (w : Word) : (borderLengths w).Nodup := by
  exact List.Pairwise.filter _ List.nodup_range

theorem borders_length_pos (w : Word) : 0 < (borderLengths w).length := by
  have h := zero_mem w
  cases he : borderLengths w with
  | nil => simp [he] at h
  | cons a l => simp

@[simp] theorem rank_nil : rank [] = 0 := by
  simp [rank, positiveBorderCount, borderLengths]

@[simp] theorem failureParent_nil : failureParent [] = 0 := by
  simp [failureParent, borderLengths, maxNat]

theorem failureParent_spec (w : Word) (hw : 0 < w.length) :
    failureParent w ∈ borderLengths w ∧ failureParent w < w.length ∧
      ∀ n ∈ borderLengths w, n < w.length → n ≤ failureParent w := by
  have hz : 0 ∈ (borderLengths w).filter (fun n => n < w.length) := by
    simp [List.mem_filter, zero_mem, hw]
  have hm := maxNat_mem hz
  have hm' : failureParent w ∈ borderLengths w ∧ failureParent w < w.length := by
    simpa only [List.mem_filter, decide_eq_true_eq] using hm
  refine ⟨hm'.1, hm'.2, ?_⟩
  intro n hn hb
  exact le_maxNat (by simp [List.mem_filter, hn, hb])

/-- Borders below a border p are exactly the borders of its prefix. -/
theorem borders_below_border {w : Word} {p n : Nat}
    (hp : p ∈ borderLengths w) (hnp : n ≤ p) :
    n ∈ borderLengths (w.take p) ↔ n ∈ borderLengths w := by
  obtain ⟨hpb, hpw⟩ := mem_borderLengths.mp hp
  have hnpw : n ≤ w.length := Nat.le_trans hnp hpb
  have hlen : (w.take p).length = p := List.length_take_of_le hpb
  have hd : (w.take p).drop (p - n) = w.drop (w.length - n) := by
    rw [hpw, List.drop_drop]
    congr 1
    omega
  simp only [mem_borderLengths, hlen, List.take_take, Nat.min_eq_left hnp, hd]
  exact ⟨fun h => ⟨hnpw, h.2⟩, fun h => ⟨hnp, h.2⟩⟩

/-- Exact finite-set decomposition at the longest proper border. -/
theorem border_decomposition (w : Word) (hw : 0 < w.length) (n : Nat) :
    n ∈ borderLengths w ↔
      n = w.length ∨ n ∈ borderLengths (w.take (failureParent w)) := by
  obtain ⟨hp, hplt, hmax⟩ := failureParent_spec w hw
  constructor
  · intro hn
    by_cases he : n = w.length
    · exact Or.inl he
    · have hb := (mem_borderLengths.mp hn).1
      have hnp := hmax n hn (by omega)
      exact Or.inr ((borders_below_border hp hnp).mpr hn)
  · rintro (rfl | hn)
    · exact full_mem w
    · have hnp : n ≤ failureParent w := by
        have h := (mem_borderLengths.mp hn).1
        simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hplt)] using h
      exact (borders_below_border hp hnp).mp hn

/-- The recursive rank equation is proved from the literal border list. -/
theorem rank_recurrence (w : Word) (hw : 0 < w.length) :
    rank w = rank (w.take (failureParent w)) + 1 := by
  obtain ⟨hp, hplt, _⟩ := failureParent_spec w hw
  have hnot : w.length ∉ borderLengths (w.take (failureParent w)) := by
    intro hm
    have h := (mem_borderLengths.mp hm).1
    simp only [List.length_take] at h
    omega
  have hn : (w.length :: borderLengths (w.take (failureParent w))).Nodup :=
    List.nodup_cons.mpr ⟨hnot, borders_nodup _⟩
  have heq := (List.perm_ext_iff_of_nodup (borders_nodup w) hn).mpr
    (fun n => by simpa only [List.mem_cons] using border_decomposition w hw n)
  have hlen := heq.length_eq
  have hpos := borders_length_pos (w.take (failureParent w))
  simp only [rank, positiveBorderCount, List.length_cons] at *
  omega

/-- Every proper border has strictly smaller rank, not merely the longest one. -/
theorem rank_lt_of_proper_border {w : Word} {p : Nat}
    (hp : p ∈ borderLengths w) (hplt : p < w.length) :
    rank (w.take p) < rank w := by
  have hpb := (mem_borderLengths.mp hp).1
  have hnot : w.length ∉ borderLengths (w.take p) := by
    intro hm
    have h := (mem_borderLengths.mp hm).1
    simp only [List.length_take] at h
    omega
  have hn : (w.length :: borderLengths (w.take p)).Nodup :=
    List.nodup_cons.mpr ⟨hnot, borders_nodup _⟩
  have hsub : w.length :: borderLengths (w.take p) ⊆ borderLengths w := by
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact full_mem w
    · have hnp : n ≤ p := by
        simpa [List.length_take, Nat.min_eq_left hpb] using (mem_borderLengths.mp hn).1
      exact (borders_below_border hp hnp).mp hn
  have hle := hn.length_le_of_subset hsub
  have hpos := borders_length_pos (w.take p)
  simp only [rank, positiveBorderCount, List.length_cons] at *
  omega

/-- A first rank threshold, with a bounded physical prefix position. -/
def FirstMilestone (w : Word) (h m : Nat) : Prop :=
  m ≤ w.length ∧ h ≤ rank (w.take m) ∧
    ∀ i, i < m → rank (w.take i) < h

/-- A first positive threshold cannot skip a rank. -/
theorem first_milestone_exact {w : Word} {h m : Nat}
    (hh : 0 < h) (hm : FirstMilestone w h m) : rank (w.take m) = h := by
  obtain ⟨hmb, hr, hfirst⟩ := hm
  have hmpos : 0 < m := by
    by_cases hz : m = 0
    · simp [hz] at hr
      omega
    · omega
  have hlen : (w.take m).length = m := List.length_take_of_le hmb
  have hs := failureParent_spec (w.take m) (by omega)
  have hprior := hfirst (failureParent (w.take m)) (by omega)
  have hrec := rank_recurrence (w.take m) (by omega)
  have hp_le : failureParent (w.take m) ≤ m := by omega
  simp only [List.take_take, Nat.min_eq_left hp_le] at hrec
  omega

/-- Truncating the final occurrence of a border yields an earlier border.
The new end position is n-p+m; overlap is allowed. -/
theorem shifted_border {w : Word} {n p m : Nat}
    (hn : n ≤ w.length) (hp : p ∈ borderLengths (w.take n)) (hmp : m ≤ p) :
    m ∈ borderLengths (w.take (n - p + m)) := by
  have hnlen : (w.take n).length = n := List.length_take_of_le hn
  obtain ⟨hpb, hpw⟩ := mem_borderLengths.mp hp
  rw [hnlen] at hpb hpw
  have hp_le : p ≤ n := hpb
  have hm_le : m ≤ n := by omega
  have he := congrArg (List.take m) hpw
  simp only [List.take_take, Nat.min_eq_left hmp, Nat.min_eq_left hm_le,
    List.drop_take] at he
  have hpm : n - (n - p) = p := by omega
  simp only [hpm, List.take_take, Nat.min_eq_left hmp] at he
  have hj : n - p + m ≤ w.length := by omega
  have hmj : m ≤ n - p + m := by omega
  apply mem_borderLengths.mpr
  constructor
  · simpa [List.length_take, Nat.min_eq_left hj] using hmj
  · simp only [List.length_take, Nat.min_eq_left hj, List.take_take,
      Nat.min_eq_left hmj, List.drop_take]
    have ha : n - p + m - m = n - p := by omega
    rw [ha]
    have hb : n - p + m - (n - p) = m := by omega
    rw [hb]
    exact he

/-- Successive first rank milestones have exactly the preceding milestone
as their longest proper border. No automaton or witness hypothesis is needed. -/
theorem first_milestones_parent {w : Word} {h m n : Nat}
    (hh : 0 < h) (hm : FirstMilestone w h m)
    (hn : FirstMilestone w (h + 1) n) : failureParent (w.take n) = m := by
  have hmexact := first_milestone_exact hh hm
  have hnexact := first_milestone_exact (by omega : 0 < h + 1) hn
  have hnpos : 0 < n := by
    by_cases hz : n = 0
    · simp [hz] at hnexact
    · omega
  have hnlen : (w.take n).length = n := List.length_take_of_le hn.1
  have hs := failureParent_spec (w.take n) (by omega)
  have hp_lt : failureParent (w.take n) < n := by omega
  have hrec := rank_recurrence (w.take n) (by omega)
  simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hp_lt)] at hrec
  have hprank : rank (w.take (failureParent (w.take n))) = h := by omega
  have hmp : m ≤ failureParent (w.take n) := by
    by_cases hz : m ≤ failureParent (w.take n)
    · exact hz
    · have hb := hm.2.2 (failureParent (w.take n)) (by omega)
      omega
  by_cases hne : failureParent (w.take n) = m
  · exact hne
  · exfalso
    have hpgt : m < failureParent (w.take n) := by omega
    let j := n - failureParent (w.take n) + m
    have hmj : m < j := by dsimp [j]; omega
    have hjn : j < n := by dsimp [j]; omega
    have hjb : j ≤ w.length := by omega
    have hborder : m ∈ borderLengths (w.take j) := shifted_border hn.1 hs.1 hmp
    have hlt := rank_lt_of_proper_border hborder
      (by simpa [List.length_take, Nat.min_eq_left hjb] using hmj)
    simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hmj)] at hlt
    have hbad := hn.2.2 j hjn
    omega

/-- The next milestone is literally the first complete return of the old one.
Every possible intermediate ending position is covered, including overlaps. -/
theorem first_milestones_first_return {w : Word} {h m n : Nat}
    (hh : 0 < h) (hm : FirstMilestone w h m)
    (hn : FirstMilestone w (h + 1) n) :
    m < n ∧ m ∈ borderLengths (w.take n) ∧
      ∀ j, m < j → j < n → m ∉ borderLengths (w.take j) := by
  have he := first_milestones_parent hh hm hn
  have hnpos : 0 < n := by
    have h := hn.2.1
    by_cases hz : n = 0
    · simp [hz] at h
    · omega
  have hs := failureParent_spec (w.take n)
    (by simpa [List.length_take, Nat.min_eq_left hn.1] using hnpos)
  rw [he] at hs
  have hmn : m < n := by
    simpa [List.length_take, Nat.min_eq_left hn.1] using hs.2.1
  refine ⟨hmn, hs.1, ?_⟩
  intro j hmj hjn hb
  have hjb : j ≤ w.length := by omega
  have hlt := rank_lt_of_proper_border hb
    (by simpa [List.length_take, Nat.min_eq_left hjb] using hmj)
  simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hmj)] at hlt
  have heq := first_milestone_exact hh hm
  have hbad := hn.2.2 j hjn
  omega

/-- Once a milestone is of maximal rank, even a return exactly at the final
position is impossible. The end of a word is not an uncharged extra return. -/
theorem no_return_after_maximal_rank {w : Word} {h m : Nat}
    (hm : rank (w.take m) = h)
    (hmax : ∀ j, j ≤ w.length → rank (w.take j) ≤ h)
    {j : Nat} (hmj : m < j) (hj : j ≤ w.length) :
    m ∉ borderLengths (w.take j) := by
  intro hb
  have hlt := rank_lt_of_proper_border hb
    (by simpa [List.length_take, Nat.min_eq_left hj] using hmj)
  simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hmj)] at hlt
  have hle := hmax j hj
  omega

end RankMilestones
end Subtail
