import Subtail.FirstReturnGraph

/-! Both directions between literal first returns and the old-graph generator. -/
namespace Subtail
namespace FirstReturnGraph
open TerminalRank RankMilestones

/-- No earlier cursor hits: a generator-side condition, not a word-border premise. -/
def GeneratorFirstHit (w : Word) (m : Nat) : Prop :=
  m < w.length ∧ cursor w m (w.length-m) = m ∧
    ∀ d, d < w.length-m → cursor w m d < m

/-- Before its first full hit, the generator computes the literal failure parent.
Unlike cursor_eq_parent, this does NOT assume a literal first return. -/
theorem cursor_eq_parent_until {w : Word} {m d : Nat} (hm : 0 < m)
    (hd : m+d ≤ w.length) (hg : ∀ e, e < d → cursor w m e < m) :
    cursor w m d = failureParent (w.take (m+d)) := by
  induction d with
  | zero => simp only [cursor, Nat.add_zero]
  | succ d ih =>
    have hd' : m+d ≤ w.length := by omega
    have hg' : ∀ e, e < d → cursor w m e < m := by
      intro e he
      exact hg e (by omega)
    have he := ih hd' hg'
    have hp : failureParent (w.take (m+d)) < m := by
      rw [← he]
      exact hg d (by omega)
    rw [cursor, he, advance_prefix hp]
    have hnext := parent_next (by omega : 0 < m+d) (next_get (by omega : m+d < w.length))
    simpa only [Nat.add_assoc] using hnext.symm

/-- Exact correspondence, needed when reconstructing a word from compiled queries. -/
theorem generator_first_hit_iff {w : Word} {m : Nat} (hm : 0 < m) :
    GeneratorFirstHit w m ↔ FirstReturn w m w.length := by
  constructor
  · rintro ⟨hmlt, hend, hguard⟩
    have hsum : m+(w.length-m) = w.length := by omega
    have he : cursor w m (w.length-m) = failureParent w := by
      simpa only [hsum, List.take_length] using
        cursor_eq_parent_until hm (d := w.length-m) (by omega) hguard
    have hp : failureParent w = m := he.symm.trans hend
    have hs := failureParent_spec w (by omega)
    refine ⟨hmlt, Nat.le_refl _, ?_, ?_⟩
    · simpa only [List.take_length, hp] using hs.1
    · intro j hmj hjn hb
      have hd : j-m < w.length-m := by omega
      have hsumj : m+(j-m) = j := by omega
      have hgj : ∀ e, e < j-m → cursor w m e < m := by
        intro e he
        exact hguard e (by omega)
      have hc : cursor w m (j-m) = failureParent (w.take j) := by
        simpa only [hsumj] using cursor_eq_parent_until hm (d := j-m) (by omega) hgj
      have hsmall : failureParent (w.take j) < m := by
        rw [← hc]
        exact hguard (j-m) hd
      have hjlen : (w.take j).length = j := List.length_take_of_le (by omega)
      have hmax := (failureParent_spec (w.take j) (by omega)).2.2 m hb (by omega)
      omega
  · intro hr
    have hmlt : m < w.length := hr.1
    have hs := cursor_first_hit hm hr
    refine ⟨hmlt, hs.1, ?_⟩
    intro d hd
    by_cases hz : d = 0
    · subst d
      have hlen : (w.take m).length = m := List.length_take_of_le (by omega)
      have h := (failureParent_spec (w.take m) (by omega)).2.1
      simpa only [cursor, hlen] using h
    · exact hs.2 d (by omega) hd

end FirstReturnGraph
end Subtail
