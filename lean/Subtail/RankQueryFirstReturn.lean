import Subtail.FirstReturnColours
import Subtail.RankQueryPaths

/-!
# First-return graphs in the query semantics, and bounded fresh intervals

Issues #26/#28. The graph and query modules are kept unchanged. This file proves
that their literal matching definitions agree, transfers the complete graph
surgery to RankQuery, and bounds maximal forward fresh intervals of an accepted
observer path. No diagram compiler or closure theorem is assumed or proved.
-/
namespace Subtail
namespace RankQueryFirstReturn
open TerminalRank RankMilestones RankQuery

/-- The literal query maximum and the proved border-based maximum coincide. -/
theorem advance_eq {w : Word} {j : Nat} (hj : j ≤ w.length) (a : Bool) :
    RankQuery.advance w j a = FirstReturnGraph.advance w j a := by
  let xs := (List.range (w.length + 1)).filter fun h =>
    (w.take h).isSuffixOf (w.take j ++ [a])
  have hz : 0 ∈ xs := by simp [xs]
  have spec : ∀ n, n ∈ xs ↔ n ∈ FirstReturnGraph.candidates w j a := by
    intro n
    rw [FirstReturnGraph.candidates_literal hj]
    simp [xs, Nat.lt_succ_iff]
  apply Nat.le_antisymm
  · exact FirstReturnGraph.advance_max ((spec _).mp (maxNat_mem hz))
  · exact le_maxNat ((spec _).mpr (FirstReturnGraph.advance_mem w j a))

/-- Boolean-mask representation agreement; no flag-column convention changes. -/
theorem mask_get_eq (I : Instance k) (B : Reference k) (j : Nat) (q : Fin k) :
    (RankQuery.mask I B j).get q =
      FirstReturnGraph.mask B.word (fun p t => (I.flags.get p).get t) B.label j q := by
  simp [RankQuery.mask, FirstReturnGraph.mask, Vector.get]

/-- Repackage a graph-surgery colour without changing any of its five fields. -/
def toQueryColour (c : FirstReturnGraph.Colour k) : RankQuery.Colour k :=
  ⟨c.1, Vector.ofFn c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2⟩

def rowTarget (row : FirstReturnGraph.Edges) : Label → Option Nat
  | .F => some row.1
  | .S => row.2.1
  | .K false => some row.2.2.1
  | .K true => some row.2.2.2

/-- Every query-graph colour is the previously verified surgery colour. -/
theorem colour_eq_surgery (I : Instance k) (B : Reference k) {m : Nat}
    (hm : 0 < m) (hr : FirstReturn B.word m B.word.length)
    (j : Fin (B.word.length + 1)) :
    (prefixGraph I B).colour j = toQueryColour
      (FirstReturnGraph.surgeryColour B.word m
        (fun p t => (I.flags.get p).get t) B.label j.val) := by
  rw [FirstReturnGraph.surgeryColour_correct hm hr (by have := j.isLt; omega)]
  rfl

/-- Every directed query-graph edge agrees with the verified surgery row. -/
theorem edge_eq_surgery (I : Instance k) (B : Reference k) {m : Nat}
    (hm : 0 < m) (hr : FirstReturn B.word m B.word.length)
    (j : Fin (B.word.length + 1)) (l : Label) :
    ((prefixGraph I B).edge j l).map Fin.val =
      rowTarget (FirstReturnGraph.surgeryEdges B.word m j.val) l := by
  have hj : j.val ≤ B.word.length := by have := j.isLt; omega
  rw [FirstReturnGraph.surgeryEdges_correct hm hr hj]
  cases l with
  | F => rfl
  | S => simp [prefixGraph, rowTarget, FirstReturnGraph.literalEdges]
  | K a =>
    cases a <;>
      simp [prefixGraph, rowTarget, FirstReturnGraph.literalEdges, advance_eq hj]

/-- Failure links of the whole first-return graph never land in its fresh part. -/
theorem parent_le_old {w : Word} {m j : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length) (hj : j ≤ w.length) :
    failureParent (w.take j) ≤ m := by
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases hold : j ≤ m
    · have hlen : (w.take j).length = j := List.length_take_of_le hj
      have hp := (failureParent_spec (w.take j) (by omega)).2.1
      omega
    · by_cases hend : j = w.length
      · subst j
        rw [first_return_parent hr]
        exact Nat.le_refl _
      · exact Nat.le_of_lt (first_return_internal_parent_lt hr (by omega) (by omega))

/-- A fresh-target K edge is a physical successor or the exceptional end wrap. -/
theorem fresh_K_shape {w : Word} {m j : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length) (hj : j ≤ w.length)
    (a : Bool) (hfresh : m < FirstReturnGraph.advance w j a) :
    FirstReturnGraph.advance w j a = j + 1 ∨
      (j = w.length ∧ FirstReturnGraph.advance w j a = m + 1) := by
  have hmlt : m < w.length := hr.1
  have hlen : (w.take m).length = m := List.length_take_of_le (by omega)
  have oldBound (h : Nat) (hh : h ≤ m) :
      FirstReturnGraph.advance (w.take m) h a ≤ m := by
    simpa only [hlen] using (FirstReturnGraph.advance_literal (w.take m)
      (by omega : h ≤ (w.take m).length) a).1
  rw [← FirstReturnGraph.surgeryK_correct hm hr hj a] at hfresh ⊢
  unfold FirstReturnGraph.surgeryK at hfresh ⊢
  by_cases h0 : j < m
  · simp only [h0, if_true] at hfresh ⊢
    have := oldBound j (by omega)
    omega
  · simp only [h0, if_false] at hfresh ⊢
    by_cases h1 : j = m
    · subst j
      simp only [if_true] at hfresh ⊢
      by_cases ha : FirstReturnGraph.Next w m a
      · simp [ha]
      · simp only [ha, if_false] at hfresh ⊢
        have := oldBound m (Nat.le_refl _)
        omega
    · simp only [h1, if_false] at hfresh ⊢
      by_cases h2 : j < w.length
      · simp only [h2, if_true] at hfresh ⊢
        by_cases ha : FirstReturnGraph.Next w j a
        · simp [ha]
        · simp only [ha, if_false] at hfresh ⊢
          have hc := FirstReturnGraph.cursor_eq_parent hm hr
            (d := j-m) (by omega)
          have hjm : m + (j-m) = j := by omega
          rw [hjm] at hc
          have hp := parent_le_old hm hr hj
          have hh : FirstReturnGraph.cursor w m (j-m) ≤ m := by omega
          have := oldBound _ hh
          omega
      · simp only [h2, if_false] at hfresh ⊢
        by_cases ha : FirstReturnGraph.Next w m a
        · simp only [ha, if_true]
          exact Or.inr ⟨by omega, True.intro⟩
        · simp only [ha, if_false] at hfresh ⊢
          have := oldBound m (Nat.le_refl _)
          omega

/-- Complete directed-edge shape, now stated on the query author's literal graph. -/
theorem fresh_edge_shape (I : Instance k) (B : Reference k) {m : Nat}
    (hm : 0 < m) (hr : FirstReturn B.word m B.word.length)
    {u v : Fin (prefixGraph I B).size} {l : Label}
    (he : (prefixGraph I B).edge u l = some v) (hv : m < v.val) :
    v.val = u.val + 1 ∨ (u.val = B.word.length ∧ v.val = m+1) := by
  have hu : u.val ≤ B.word.length := by have := u.isLt; change u.val < B.word.length+1 at this; omega
  cases l with
  | F =>
    have hval : failureParent (B.word.take u.val) = v.val := by
      exact congrArg Fin.val (Option.some.inj he)
    have := parent_le_old hm hr hu
    omega
  | S =>
    simp only [prefixGraph] at he
    split at he
    · have hval := congrArg Fin.val (Option.some.inj he)
      exact Or.inl hval.symm
    · contradiction
  | K a =>
    have hval : RankQuery.advance B.word u.val a = v.val := by
      exact congrArg Fin.val (Option.some.inj he)
    rw [advance_eq hu a] at hval
    have hs := fresh_K_shape hm hr hu a (by omega)
    simpa only [hval] using hs

/-- The only old-to-fresh entrance is the edge from m to m+1. -/
theorem old_to_fresh (I : Instance k) (B : Reference k) {m : Nat}
    (hm : 0 < m) (hr : FirstReturn B.word m B.word.length)
    {u v : Fin (prefixGraph I B).size} {l : Label}
    (he : (prefixGraph I B).edge u l = some v)
    (hu : u.val ≤ m) (hv : m < v.val) :
    u.val = m ∧ v.val = m+1 := by
  have hmlt : m < B.word.length := hr.1
  rcases fresh_edge_shape I B hm hr he hv with h | ⟨h, _⟩ <;> omega

/-- At an entry or wrap into the fresh part, the destination is m+1. -/
theorem fresh_break_target (I : Instance k) (B : Reference k) {m : Nat}
    (hm : 0 < m) (hr : FirstReturn B.word m B.word.length)
    {u v : Fin (prefixGraph I B).size} {l : Label}
    (he : (prefixGraph I B).edge u l = some v)
    (hb : m < v.val ∧ ¬ (m < u.val ∧ v.val = u.val+1)) :
    v.val = m+1 := by
  rcases fresh_edge_shape I B hm hr he hb.1 with h | ⟨_, h⟩
  · by_cases hu : m < u.val
    · exact False.elim (hb.2 ⟨hu, h⟩)
    · omega
  · exact h

/-- Count new maximal forward fresh intervals AFTER a preceding node.
A wrap starts a new interval, including a one-vertex self-wrap. -/
def breaksAfter {α : Type} (position : α → Nat) (m : Nat) (previous : α) : List α → Nat
  | [] => 0
  | y :: ys =>
      (if m < position y ∧ ¬ (m < position previous ∧ position y = position previous+1)
        then 1 else 0) + breaksAfter position m y ys

/-- Number of maximal physical-forward intervals in the fresh part. -/
def freshIntervals {α : Type} (position : α → Nat) (m : Nat) : List α → Nat
  | [] => 0
  | x :: xs => (if m < position x then 1 else 0) + breaksAfter position m x xs

theorem visits_tail_le (G : Graph k) (O : Observer k) (x : Node G O)
    (xs : List (Node G O)) (v : Fin G.size) :
    visits G O xs v ≤ visits G O (x :: xs) v := by
  by_cases h : x.1 = v <;> simp [visits, h]

/-- Each fresh-interval break is charged to a later visit of the unique entrance. -/
theorem breaksAfter_le_visits (I : Instance k) (B : Reference k) {m : Nat}
    (hm : 0 < m) (hr : FirstReturn B.word m B.word.length) (O : Observer k)
    (entry : Fin (prefixGraph I B).size) (hentry : entry.val = m+1)
    (x : Node (prefixGraph I B) O) (xs : List (Node (prefixGraph I B) O))
    (hchain : Chain (prefixGraph I B) O (x :: xs)) :
    breaksAfter (fun n : Node (prefixGraph I B) O => n.1.val) m x xs ≤
      visits (prefixGraph I B) O xs entry := by
  induction xs generalizing x with
  | nil => simp [breaksAfter, visits]
  | cons y ys ih =>
    have hpair : Step (prefixGraph I B) O x y ∧ Chain (prefixGraph I B) O (y :: ys) := hchain
    have hrest := ih y hpair.2
    by_cases hb : m < y.1.val ∧ ¬ (m < x.1.val ∧ y.1.val = x.1.val+1)
    · obtain ⟨l, he, _, _⟩ := hpair.1
      have hval := fresh_break_target I B hm hr he hb
      have hye : y.1 = entry := Fin.ext (hval.trans hentry.symm)
      simp only [breaksAfter, if_pos hb]
      have hv : visits (prefixGraph I B) O (y :: ys) entry =
          1 + visits (prefixGraph I B) O ys entry := by
        simp [visits, hye, Nat.add_comm]
      rw [hv]
      exact Nat.add_le_add_left hrest 1
    · simp only [breaksAfter, hb, if_false, Nat.zero_add]
      exact Nat.le_trans hrest (visits_tail_le _ O y ys entry)

/-- Product-simple accepted paths have at most s+1 maximal forward fresh intervals.
The bound does not mention the old word length or extension length. -/
theorem accepts_bounded_fresh_intervals (I : Instance k) (B : Reference k) {m : Nat}
    (hm : 0 < m) (hr : FirstReturn B.word m B.word.length) (O : Observer k)
    {u v : Fin (prefixGraph I B).size} (h : Accepts (prefixGraph I B) O u v) :
    ∃ q ∈ O.initial, ∃ p ∈ O.final, ∃ xs : List (Node (prefixGraph I B) O),
      Chain (prefixGraph I B) O ((u,q) :: xs) ∧
      ((u,q) :: xs).getLast? = some (v,p) ∧ ((u,q) :: xs).Nodup ∧
      (∀ x ∈ (u,q) :: xs, Allowed (prefixGraph I B) O x) ∧
      freshIntervals (fun n : Node (prefixGraph I B) O => n.1.val) m ((u,q) :: xs)
        ≤ O.size + 1 := by
  have hmlt : m < B.word.length := hr.1
  let entry : Fin (prefixGraph I B).size := ⟨m+1, by change m+1 < B.word.length+1; omega⟩
  obtain ⟨q,hq,p,hp,xs,hchain,hlast,hnd,hallowed,hvis⟩ :=
    accepts_bounded_visits (prefixGraph I B) O h entry
  refine ⟨q,hq,p,hp,xs,hchain,hlast,hnd,hallowed,?_⟩
  have hbreak := breaksAfter_le_visits I B hm hr O entry rfl (u,q) xs hchain
  have htail := visits_tail_le (prefixGraph I B) O (u,q) xs entry
  change (if m < u.val then 1 else 0) +
    breaksAfter (fun n : Node (prefixGraph I B) O => n.1.val) m (u,q) xs ≤ O.size+1
  split <;> omega

end RankQueryFirstReturn
end Subtail
