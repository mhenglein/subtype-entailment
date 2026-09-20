import Subtail.StackReachability

/-!
# Acyclic consumed paths have bounded word length

The `Pop` relation separates balanced excursions from the letters consumed by
the stack.  A consumed path therefore exposes one boundary control per letter.
If a boundary control repeats, the intervening consumed subword is a nonempty
`Pop` loop.  This module records that finite-control argument independently of
any executable cycle classifier.
-/

namespace Subtail
namespace PopAcyclic

open StackSummary StackReachability

private theorem pop_trace
    (M : System n)
    (hloop : ∀ p w, Pop M p w p → w = [])
    {p q : Fin n} {w : Word} (h : Pop M p w q) :
    ∃ xs : List (Fin n × Word),
      xs.length = w.length + 1 ∧
      (∀ x ∈ xs, Pop M p x.2 x.1) ∧
      (xs.map Prod.fst).Nodup := by
  induction w generalizing p q with
  | nil =>
      refine ⟨[(p, [])], by simp, ?_, by simp⟩
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact Balanced.refl p
  | cons a w ih =>
      obtain ⟨r, s, hbal, hletter, hrest⟩ := h
      obtain ⟨xs, hlen, hprefix, hnodup⟩ := ih hrest
      let f : Fin n × Word → Fin n × Word := fun x => (x.1, a :: x.2)
      refine ⟨(p, []) :: xs.map f, ?_, ?_, ?_⟩
      · simp only [List.length_cons, List.length_map]
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · change Pop M p [] p
          exact Balanced.refl p
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
          cases z with
          | mk c u =>
              exact ⟨r, s, hbal, hletter, hprefix (c, u) hz⟩
      · have htail : (List.map Prod.fst (xs.map f)).Nodup := by
          simpa [f, List.map_map, Function.comp_def] using hnodup
        have hnot : p ∉ List.map Prod.fst (xs.map f) := by
          intro hp
          have hmap : List.map Prod.fst (xs.map f) = xs.map Prod.fst := by
            simp [f, List.map_map, Function.comp_def]
          rw [hmap] at hp
          obtain ⟨z, hz, hzp⟩ := List.mem_map.mp hp
          rcases z with ⟨c, u⟩
          have hcp : c = p := by simpa using hzp
          subst c
          have hpop : Pop M p (a :: u) p :=
            ⟨r, s, hbal, hletter, hprefix (p, u) hz⟩
          have hempty := hloop p (a :: u) hpop
          simp at hempty
        simpa only [List.map_cons, List.nodup_cons] using And.intro hnot htail

theorem pop_length_lt_of_no_nonempty_loop
    (M : StackSummary.System n)
    (hloop : ∀ p w, StackReachability.Pop M p w p → w = [])
    {p q : Fin n} {w : Word}
    (h : StackReachability.Pop M p w q) :
    w.length < n := by
  obtain ⟨xs, hlen, _, hnodup⟩ := pop_trace M hloop h
  have hle := hnodup.length_le_of_subset
    (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  have hle' : xs.length ≤ (List.finRange n).length := by
    simpa only [List.length_map] using hle
  rw [hlen] at hle'
  simp only [List.length_finRange] at hle'
  omega

end PopAcyclic
end Subtail
