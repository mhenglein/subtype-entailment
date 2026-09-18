import Subtail.FirstReturnGenerator

/-! Exact coloured graph surgery; no observer/query closure is assumed. -/
namespace Subtail
namespace FirstReturnGraph
open TerminalRank RankMilestones

/-- Incoming flags from all literal borders, including empty and full borders. -/
def mask (w : Word) (col : Fin k → Fin k → Bool) (r : Nat → Fin k)
    (j : Nat) (q : Fin k) : Bool :=
  (borderLengths (w.take j)).any fun h => col q (r h)

theorem mask_prefix {w : Word} {m j : Nat} (hj : j ≤ m)
    (col : Fin k → Fin k → Bool) (r : Nat → Fin k) :
    mask (w.take m) col r j = mask w col r j := by
  funext q
  simp only [mask, List.take_take, Nat.min_eq_left hj]

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The full border contributes its column; all others are borders of its parent. -/
theorem mask_decomposition {w : Word} {j : Nat} (hj : j ≤ w.length)
    (hp : 0 < j) (col : Fin k → Fin k → Bool) (r : Nat → Fin k) (q : Fin k) :
    mask w col r j q = (col q (r j) || mask w col r (failureParent (w.take j)) q) := by
  have hlen : (w.take j).length = j := List.length_take_of_le hj
  have hs := failureParent_spec (w.take j) (by omega)
  have hplt : failureParent (w.take j) < j := by omega
  have heq : (w.take j).take (failureParent (w.take j)) =
      w.take (failureParent (w.take j)) := by
    simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt hplt)]
  apply bool_ext
  simp only [mask, List.any_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨h, hb, hc⟩
    rcases (border_decomposition (w.take j) (by omega) h).mp hb with hfull | hb'
    · left
      have he : h = j := by omega
      simpa only [he] using hc
    · right
      rw [heq] at hb'
      exact ⟨h, hb', hc⟩
  · rintro (hc | ⟨h, hb, hc⟩)
    · refine ⟨j, ?_, hc⟩
      simpa only [hlen] using full_mem (w.take j)
    · refine ⟨h, (border_decomposition (w.take j) (by omega) h).mpr (Or.inr ?_), hc⟩
      rwa [heq]

/-- New masks use only the old graph at the computed origin and the new column. -/
theorem fresh_mask {w : Word} {m j : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length)
    (hmj : m < j) (hjn : j ≤ w.length)
    (col : Fin k → Fin k → Bool) (r : Nat → Fin k) (q : Fin k) :
    mask w col r j q =
      (col q (r j) || mask (w.take m) col r (cursor w m (j-m)) q) := by
  have he : m+(j-m) = j := by omega
  have hcur : cursor w m (j-m) = failureParent (w.take j) := by
    simpa only [he] using cursor_eq_parent hm hr (d := j-m) (by omega)
  have hpm : failureParent (w.take j) ≤ m := by
    by_cases hje : j = w.length
    · subst j
      rw [first_return_parent hr]
      exact Nat.le_refl m
    · exact Nat.le_of_lt (first_return_internal_parent_lt hr hmj (by omega))
  rw [hcur, mask_prefix hpm]
  exact mask_decomposition hjn (by omega) col r q

/-- The compiler's local flag guard checks exactly the new full mask. -/
theorem fresh_clear_iff {w : Word} {m j : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length)
    (hmj : m < j) (hjn : j ≤ w.length)
    (col : Fin k → Fin k → Bool) (r : Nat → Fin k) :
    mask w col r j (r j) = false ↔
      col (r j) (r j) = false ∧
      mask (w.take m) col r (cursor w m (j-m)) (r j) = false := by
  rw [fresh_mask hm hr hmj hjn]
  exact Bool.or_eq_false_iff

/-- Row order: F, optional S, K0, K1. -/
abbrev Edges := Nat × Option Nat × Nat × Nat

def literalEdges (w : Word) (j : Nat) : Edges :=
  (failureParent (w.take j), if j < w.length then some (j+1) else none,
    advance w j false, advance w j true)

def surgeryEdges (w : Word) (m j : Nat) : Edges :=
  (if j ≤ m then failureParent ((w.take m).take j) else cursor w m (j-m),
    if j < m then (if j < (w.take m).length then some (j+1) else none)
      else if j < w.length then some (j+1) else none,
    surgeryK w m j false, surgeryK w m j true)

theorem surgeryEdges_correct {w : Word} {m j : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length) (hj : j ≤ w.length) :
    surgeryEdges w m j = literalEdges w j := by
  have hmlt : m < w.length := hr.1
  have hlen : (w.take m).length = m := List.length_take_of_le (by omega)
  have hf : (if j ≤ m then failureParent ((w.take m).take j)
      else cursor w m (j-m)) = failureParent (w.take j) := by
    by_cases h : j ≤ m
    · simp only [h, if_true, List.take_take, Nat.min_eq_left h]
    · simp only [h, if_false]
      have he : m+(j-m) = j := by omega
      simpa only [he] using cursor_eq_parent hm hr (d := j-m) (by omega)
  have hs : (if j < m then (if j < (w.take m).length then some (j+1) else none)
      else if j < w.length then some (j+1) else none) =
      (if j < w.length then some (j+1) else none) := by
    by_cases h : j < m
    · simp only [h, hlen, if_true, if_pos (by omega : j < w.length)]
    · simp only [h, if_false]
  simp only [surgeryEdges, literalEdges, hf, hs, surgeryK_correct hm hr hj]

/-- All edge destinations belong to the finite prefix vertex set. -/
theorem literalEdges_bounded {w : Word} {j : Nat} (hj : j ≤ w.length) :
    (literalEdges w j).1 ≤ w.length ∧
    (∀ t, (literalEdges w j).2.1 = some t → t ≤ w.length) ∧
    (literalEdges w j).2.2.1 ≤ w.length ∧
    (literalEdges w j).2.2.2 ≤ w.length := by
  have hf : failureParent (w.take j) ≤ w.length := by
    by_cases hz : j = 0
    · simp [hz]
    · have hlen : (w.take j).length = j := List.length_take_of_le hj
      have h := (failureParent_spec (w.take j) (by omega)).2.1
      omega
  refine ⟨hf, ?_, (advance_literal w hj false).1, (advance_literal w hj true).1⟩
  intro t ht
  simp only [literalEdges] at ht
  split at ht
  · have he : j+1 = t := Option.some.inj ht
    omega
  · contradiction

/-- Colour order: original state, incoming mask, next bit, Root, End.
No numeric word position is included in a colour. -/
abbrev Colour (k : Nat) := Fin k × (Fin k → Bool) × Option Bool × Bool × Bool

def literalColour (w : Word) (col : Fin k → Fin k → Bool) (r : Nat → Fin k)
    (j : Nat) : Colour k :=
  (r j, mask w col r j, w[j]?, decide (j = 0), decide (j = w.length))

def surgeryColour (w : Word) (m : Nat) (col : Fin k → Fin k → Bool)
    (r : Nat → Fin k) (j : Nat) : Colour k :=
  if j < m then literalColour (w.take m) col r j
  else if j = m then
    (r m, mask (w.take m) col r m, w[m]?, decide (m = 0), false)
  else (r j, (fun q => col q (r j) || mask (w.take m) col r (cursor w m (j-m)) q),
    w[j]?, false, decide (j = w.length))

theorem surgeryColour_correct {w : Word} {m j : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length) (hj : j ≤ w.length)
    (col : Fin k → Fin k → Bool) (r : Nat → Fin k) :
    surgeryColour w m col r j = literalColour w col r j := by
  have hmlt : m < w.length := hr.1
  have hlen : (w.take m).length = m := List.length_take_of_le (by omega)
  by_cases h0 : j < m
  · have hjm : j ≠ m := by omega
    have hjn : j ≠ w.length := by omega
    simp only [surgeryColour, h0, if_true, literalColour,
      mask_prefix (Nat.le_of_lt h0), List.getElem?_take, if_true,
      hlen, hjm, hjn, decide_false]
  · by_cases h1 : j = m
    · subst j
      have hmn : m ≠ w.length := by omega
      simp only [surgeryColour, Nat.lt_irrefl, if_false, if_true, literalColour,
        mask_prefix (Nat.le_refl m), hmn, decide_false]
    · have hj0 : j ≠ 0 := by omega
      have hmj : m < j := by omega
      have he : (fun q => col q (r j) || mask (w.take m) col r (cursor w m (j-m)) q)
          = mask w col r j := by
        funext q
        exact (fresh_mask hm hr hmj hj col r q).symm
      simp only [surgeryColour, h0, h1, if_false, literalColour, he,
        hj0, decide_false]

/-- Literal finite labelled graph, with exactly length(w)+1 vertices. -/
def literalGraph (w : Word) (col : Fin k → Fin k → Bool) (r : Nat → Fin k) :
    Fin (w.length+1) → Colour k × Edges :=
  fun j => (literalColour w col r j.val, literalEdges w j.val)

/-- Local construction: OLD prefix matching/masks and one generated cursor walk. -/
def surgeryGraph (w : Word) (m : Nat) (col : Fin k → Fin k → Bool) (r : Nat → Fin k) :
    Fin (w.length+1) → Colour k × Edges :=
  fun j => (surgeryColour w m col r j.val, surgeryEdges w m j.val)

/-- Extensional equality of every vertex colour and every F/S/K0/K1 edge. -/
theorem first_return_graph_exact {w : Word} {m : Nat}
    (hm : 0 < m) (hr : FirstReturn w m w.length)
    (col : Fin k → Fin k → Bool) (r : Nat → Fin k) :
    surgeryGraph w m col r = literalGraph w col r := by
  funext j
  have hj : j.val ≤ w.length := by have := j.isLt; omega
  exact Prod.ext (surgeryColour_correct hm hr hj col r) (surgeryEdges_correct hm hr hj)

/-- The exact graph theorem also holds on the compiler's generator-side premise. -/
theorem generated_graph_exact {w : Word} {m : Nat}
    (hm : 0 < m) (hg : GeneratorFirstHit w m)
    (col : Fin k → Fin k → Bool) (r : Nat → Fin k) :
    surgeryGraph w m col r = literalGraph w col r :=
  first_return_graph_exact hm ((generator_first_hit_iff hm).mp hg) col r

end FirstReturnGraph
end Subtail
