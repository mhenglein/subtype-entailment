import Subtail.RankQuery

/-!
# Product-simple runs and bounded visits

The graph-independent core of the rank-query candidate's Lemma 3 ("bounded strip
entrances"), in the `RankQuery` semantics: every accepted run of an observer has
a witness list of `(vertex, control)` nodes without repetition and with the same
endpoints, and such a list visits any fixed vertex at most `O.size` times.

This does NOT model the old/fresh split of a first-return graph, excursions,
marks or diagrams; it is the finiteness fact those constructions rest on.
No `sorry`, no custom axiom.
-/
namespace Subtail
namespace RankQuery

section Paths
variable (G : Graph k) (O : Observer k)

/-- Consecutive nodes are joined by steps; short lists are trivially chains. -/
def Chain : List (Node G O) → Prop
  | [] => True
  | [_] => True
  | x :: y :: l => Step G O x y ∧ Chain (y :: l)

theorem chain_tail {x : Node G O} {l : List (Node G O)} (h : Chain G O (x :: l)) :
    Chain G O l := by
  cases l with
  | nil => trivial
  | cons y l => exact h.2

theorem chain_cons_cons {x y : Node G O} {l : List (Node G O)} :
    Chain G O (x :: y :: l) ↔ Step G O x y ∧ Chain G O (y :: l) := Iff.rfl

theorem chain_append_right {a b : List (Node G O)} (h : Chain G O (a ++ b)) :
    Chain G O b := by
  induction a with
  | nil => simpa using h
  | cons x a ih => exact ih (chain_tail G O (by simpa using h))

theorem chain_append_left {a b : List (Node G O)} (h : Chain G O (a ++ b)) :
    Chain G O a := by
  induction a with
  | nil => trivial
  | cons x a ih =>
    cases a with
    | nil => trivial
    | cons y a' =>
      have h' : Step G O x y ∧ Chain G O (y :: (a' ++ b)) := h
      exact ⟨h'.1, ih h'.2⟩

theorem chain_glue {a c : List (Node G O)} {z : Node G O}
    (ha : Chain G O (a ++ [z])) (hc : Chain G O (z :: c)) : Chain G O (a ++ z :: c) := by
  induction a with
  | nil => simpa using hc
  | cons x a ih =>
    cases a with
    | nil =>
      have h' : Step G O x z ∧ Chain G O [z] := ha
      exact ⟨h'.1, hc⟩
    | cons y a' =>
      have h' : Step G O x y ∧ Chain G O (y :: (a' ++ [z])) := ha
      exact ⟨h'.1, ih h'.2⟩

theorem chain_snoc {p : List (Node G O)} {y z : Node G O}
    (hp : Chain G O p) (hl : p.getLast? = some y) (hs : Step G O y z) :
    Chain G O (p ++ [z]) := by
  induction p with
  | nil => simp at hl
  | cons x p ih =>
    cases p with
    | nil =>
      simp at hl
      subst hl
      exact ⟨hs, trivial⟩
    | cons y' p' =>
      have h' : Step G O x y' ∧ Chain G O (y' :: p') := hp
      have hl' : (y' :: p').getLast? = some y := by simpa using hl
      exact ⟨h'.1, ih h'.2 hl'⟩

/-- Every node of a chain from an allowed start is allowed. -/
theorem chain_allowed {x : Node G O} {l : List (Node G O)} (hx : Allowed G O x)
    (h : Chain G O (x :: l)) : ∀ n ∈ x :: l, Allowed G O n := by
  induction l generalizing x with
  | nil => intro n hn; simp at hn; subst hn; exact hx
  | cons y l ih =>
    intro n hn
    have h' : Step G O x y ∧ Chain G O (y :: l) := h
    obtain ⟨_, _, _, hy⟩ := h'.1
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hx
    · exact ih hy h'.2 n hn

theorem run_prepend {x y z : Node G O} (hx : Allowed G O x) (hs : Step G O x y)
    (hr : Run G O y z) : Run G O x z := by
  induction hr with
  | refl _ => exact Run.step (Run.refl hx) hs
  | step _ hs' ih => exact Run.step ih hs'

/-- Runs are exactly chains from an allowed start, read off by their last node. -/
theorem run_iff_chain {x y : Node G O} :
    Run G O x y ↔ Allowed G O x ∧
      ∃ l : List (Node G O), Chain G O (x :: l) ∧ (x :: l).getLast? = some y := by
  constructor
  · intro hr
    refine ⟨allowed_of_run G O hr, ?_⟩
    induction hr with
    | refl h => exact ⟨[], trivial, by simp⟩
    | @step y' z' _ hs ih =>
      obtain ⟨l, hl, hlast⟩ := ih
      refine ⟨l ++ [z'], chain_snoc G O hl hlast hs, ?_⟩
      rw [show x :: (l ++ [z']) = (x :: l) ++ [z'] from rfl, List.getLast?_append]
      simp
  · rintro ⟨hx, l, hl, hlast⟩
    induction l generalizing x with
    | nil =>
      simp at hlast
      subst hlast
      exact Run.refl hx
    | cons y' l ih =>
      have h' : Step G O x y' ∧ Chain G O (y' :: l) := hl
      obtain ⟨_, _, _, hy'⟩ := h'.1
      have hlast' : (y' :: l).getLast? = some y := by simpa using hlast
      exact run_prepend G O hx h'.1 (ih hy' h'.2 hlast')

/-- A list with a repetition splits around the repeated node. -/
theorem exists_dup_of_not_nodup {α : Type} : ∀ (p : List α), ¬ p.Nodup →
    ∃ (a b c : List α) (z : α), p = a ++ z :: (b ++ z :: c) := by
  intro p
  induction p with
  | nil => intro h; exact absurd List.nodup_nil h
  | cons x t ih =>
    intro h
    by_cases hx : x ∈ t
    · obtain ⟨s, t', ht⟩ := List.append_of_mem hx
      exact ⟨[], s, t', x, by simp [ht]⟩
    · have ht : ¬ t.Nodup := fun hn => h (List.nodup_cons.mpr ⟨hx, hn⟩)
      obtain ⟨a, b, c, z, hz⟩ := ih ht
      exact ⟨x :: a, b, c, z, by simp [hz]⟩

theorem head?_append_cons {α : Type} (a b b' : List α) (z : α) :
    (a ++ z :: b).head? = (a ++ z :: b').head? := by
  cases a <;> simp

theorem getLast?_append_cons {α : Type} (a a' c : List α) (z : α) :
    (a ++ z :: c).getLast? = (a' ++ z :: c).getLast? := by
  cases c with
  | nil => simp
  | cons y c =>
    simp only [List.getLast?_append]
    cases h : (z :: y :: c).getLast? with
    | none => simp at h
    | some v => simp

/-- Every chain has a repetition-free chain with the same first and last nodes. -/
theorem chain_dedup_aux : ∀ (n : Nat) (p : List (Node G O)), p.length ≤ n → Chain G O p →
    ∃ p' : List (Node G O), Chain G O p' ∧ p'.head? = p.head? ∧
      p'.getLast? = p.getLast? ∧ p'.Nodup ∧ p'.length ≤ p.length := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨[], trivial, rfl, rfl, List.nodup_nil, Nat.le_refl _⟩
  | succ n ih =>
    intro p hpn hp
    by_cases hn : p.Nodup
    · exact ⟨p, hp, rfl, rfl, hn, Nat.le_refl _⟩
    · obtain ⟨a, b, c, z, hz⟩ := exists_dup_of_not_nodup p hn
      let q := a ++ z :: c
      have hq : Chain G O q := by
        have h1 : Chain G O (a ++ [z]) := by
          have := chain_append_left G O (a := a ++ [z]) (b := b ++ z :: c) (by simpa [hz] using hp)
          exact this
        have h2 : Chain G O (z :: c) := by
          have := chain_append_right G O (a := a ++ z :: b) (b := z :: c) (by simpa [hz] using hp)
          exact this
        exact chain_glue G O h1 h2
      have hlen : q.length < p.length := by
        simp only [q, hz, List.length_append, List.length_cons]
        omega
      obtain ⟨p', hp', hh, hl, hnd, hle⟩ := ih q (by omega) hq
      refine ⟨p', hp', ?_, ?_, hnd, ?_⟩
      · rw [hh, hz]
        exact head?_append_cons a c (b ++ z :: c) z
      · rw [hl, hz]
        have := getLast?_append_cons a (a ++ z :: b) c z
        simpa only [List.append_assoc, List.cons_append] using this
      · omega

theorem chain_dedup (p : List (Node G O)) (hp : Chain G O p) :
    ∃ p' : List (Node G O), Chain G O p' ∧ p'.head? = p.head? ∧
      p'.getLast? = p.getLast? ∧ p'.Nodup ∧ p'.length ≤ p.length :=
  chain_dedup_aux G O p.length p (Nat.le_refl _) hp

/-- Number of nodes of a list lying over a fixed graph vertex. -/
def visits (p : List (Node G O)) (v : Fin G.size) : Nat :=
  (p.filter fun n => decide (n.1 = v)).length

theorem nodup_map_snd_on {v : Fin G.size} {l : List (Node G O)} (hl : l.Nodup)
    (hv : ∀ n ∈ l, n.1 = v) : (l.map Prod.snd).Nodup := by
  induction l with
  | nil => simp
  | cons n l ih =>
    obtain ⟨hn, hl'⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl' (fun m hm => hv m (List.mem_cons_of_mem _ hm))⟩
    intro hm
    obtain ⟨m, hm', he⟩ := List.mem_map.mp hm
    have h1 : m.1 = n.1 := by rw [hv m (List.mem_cons_of_mem _ hm'), hv n (List.mem_cons_self ..)]
    have : m = n := Prod.ext h1 he
    exact hn (this ▸ hm')

/-- A repetition-free list visits a vertex at most once per observer control. -/
theorem visits_le_of_nodup {p : List (Node G O)} (hp : p.Nodup) (v : Fin G.size) :
    visits G O p v ≤ O.size := by
  have hf : (p.filter fun n => decide (n.1 = v)).Nodup := List.Pairwise.filter _ hp
  have hv : ∀ n ∈ p.filter (fun n => decide (n.1 = v)), n.1 = v := by
    intro n hn
    exact of_decide_eq_true (List.mem_filter.mp hn).2
  have hm := nodup_map_snd_on G O hf hv
  have hle := hm.length_le_of_subset (l₂ := List.finRange O.size)
    (fun x _ => List.mem_finRange x)
  simpa [visits, List.length_map] using hle

/-- **Bounded visits.** Every accepted path has a product-simple witness chain from an
initial to a final control that visits any fixed vertex at most `O.size` times.
This is the graph-size-independent ingredient of the candidate's mark bound. -/
theorem accepts_bounded_visits {u w : Fin G.size} (h : Accepts G O u w) (v : Fin G.size) :
    ∃ q ∈ O.initial, ∃ p ∈ O.final, ∃ l : List (Node G O),
      Chain G O ((u, q) :: l) ∧ ((u, q) :: l).getLast? = some (w, p) ∧
      ((u, q) :: l).Nodup ∧ (∀ n ∈ (u, q) :: l, Allowed G O n) ∧
      visits G O ((u, q) :: l) v ≤ O.size := by
  obtain ⟨q, hq, p, hp, hr⟩ := h
  obtain ⟨hx, l, hl, hlast⟩ := (run_iff_chain G O).mp hr
  obtain ⟨p', hp', hh, hl', hnd, -⟩ := chain_dedup G O ((u, q) :: l) hl
  cases p' with
  | nil => simp at hh
  | cons x l' =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    refine ⟨q, hq, p, hp, l', hp', hl'.trans hlast, hnd, chain_allowed G O hx hp',
      visits_le_of_nodup G O hnd v⟩

end Paths

end RankQuery
end Subtail
