import Subtail.Basic

/-!
# Terminal accepting paths: prefix freeness and the border-count bound

This formalizes a structural dependency of the rank-query candidate, not its
uniform query-preimage theorem. It uses the existing partial-DFA run and witness
semantics. No global witness-length bound or decision oracle is assumed.
-/
namespace Subtail
namespace TerminalRank

/-- Every accepting state has no outgoing transition, on either letter. -/
def TerminalFinals (I : Instance k) : Prop :=
  ∀ f : Fin k, I.final.get f = true → ∀ a : Bool, step I f a = none

/-- A terminal accepting state cannot read a nonempty word. -/
theorem runFrom_terminal (I : Instance k) (ht : TerminalFinals I)
    {f g : Fin k} (hf : I.final.get f = true) (w : Word) :
    runFrom I f w = some g ↔ w = [] ∧ f = g := by
  cases w with
  | nil => simp [Subtail.runFrom]
  | cons a w => simp [Subtail.runFrom, ht f hf a]

/-- Accepted words from one state form a prefix-free language. The initial
state here is arbitrary, and the two final states need not be identical. -/
theorem accepted_prefix_eq (I : Instance k) (ht : TerminalFinals I)
    {q f g : Fin k} {u v : Word}
    (hu : runFrom I q u = some f) (hf : I.final.get f = true)
    (hv : runFrom I q v = some g) (hp : u.IsPrefix v) : u = v := by
  rcases hp with ⟨z, rfl⟩
  have hz : runFrom I f z = some g := by
    simpa [runFrom_append, hu] using hv
  have hz0 : z = [] := ((runFrom_terminal I ht hf z).mp hz).1
  simp [hz0]

/-- Total executable cut label. On a defined full run its fallback is unused. -/
def cutState (I : Instance k) (q : Fin k) (w : Word) (i : Nat) : Fin k :=
  (runFrom I q (w.take i)).getD q

/-- Every suffix of a defined accepting run has the original accepting endpoint. -/
theorem runFrom_cutState_drop (I : Instance k) {q f : Fin k} {w : Word}
    (hw : runFrom I q w = some f) (i : Nat) :
    runFrom I (cutState I q w i) (w.drop i) = some f := by
  have hs : (runFrom I q (w.take i)).bind
      (fun r => runFrom I r (w.drop i)) = some f := by
    rw [← runFrom_append, List.take_append_drop]
    exact hw
  cases hp : runFrom I q (w.take i) with
  | none => simp [hp] at hs
  | some r => simpa [cutState, hp] using hs

/-- A proper suffix agreement on a terminal accepting run has distinct starting
states. This includes the empty terminal suffix and does not need flag safety. -/
theorem agreement_distinct (I : Instance k) (ht : TerminalFinals I)
    {q f : Fin k} {w : Word} (hw : runFrom I q w = some f)
    (hf : I.final.get f = true) {i j : Nat}
    (hij : i < j) (hj : j ≤ w.length) (ha : Agrees w i j) :
    cutState I q w i ≠ cutState I q w j := by
  intro he
  have hiRun := runFrom_cutState_drop I hw i
  have hjRun := runFrom_cutState_drop I hw j
  rw [he] at hiRun
  have eqWords := accepted_prefix_eq I ht hjRun hf hiRun ha
  have eqLengths := congrArg List.length eqWords
  simp only [List.length_drop] at eqLengths
  omega

/-- All border lengths, including zero and the full word. This is a finite,
computable enumeration; equality is exactly prefix equals suffix at that length. -/
def borderLengths (w : Word) : List Nat :=
  (List.range (w.length + 1)).filter fun n =>
    w.take n == w.drop (w.length - n)

theorem mem_borderLengths {w : Word} {n : Nat} :
    n ∈ borderLengths w ↔
      n ≤ w.length ∧ w.take n = w.drop (w.length - n) := by
  simp [borderLengths, List.mem_filter, List.mem_range, Nat.lt_succ_iff]

def borderState (I : Instance k) (q : Fin k) (w : Word) (n : Nat) : Fin k :=
  cutState I q w (w.length - n)

private theorem borderState_injective_le
    (I : Instance k) (ht : TerminalFinals I)
    {q f : Fin k} {w : Word} (hw : runFrom I q w = some f)
    (hf : I.final.get f = true) {i j : Nat}
    (hi : i ∈ borderLengths w) (hj : j ∈ borderLengths w) (hij : i ≤ j)
    (he : borderState I q w i = borderState I q w j) : i = j := by
  obtain ⟨hib, hiw⟩ := mem_borderLengths.mp hi
  obtain ⟨hjb, hjw⟩ := mem_borderLengths.mp hj
  have hir : runFrom I (borderState I q w i) (w.take i) = some f := by
    rw [hiw]
    exact runFrom_cutState_drop I hw (w.length - i)
  have hjr : runFrom I (borderState I q w j) (w.take j) = some f := by
    rw [hjw]
    exact runFrom_cutState_drop I hw (w.length - j)
  rw [he] at hir
  have hp : (w.take i).IsPrefix (w.take j) := by
    simpa [List.take_take, Nat.min_eq_left hij] using List.take_prefix i (w.take j)
  have heq := accepted_prefix_eq I ht hir hf hjr hp
  have hlen := congrArg List.length heq
  simpa [List.length_take, Nat.min_eq_left hib, Nat.min_eq_left hjb] using hlen

/-- Distinct borders of any accepted suffix must carry different original states. -/
theorem borderState_injective
    (I : Instance k) (ht : TerminalFinals I)
    {q f : Fin k} {w : Word} (hw : runFrom I q w = some f)
    (hf : I.final.get f = true) {i j : Nat}
    (hi : i ∈ borderLengths w) (hj : j ∈ borderLengths w)
    (he : borderState I q w i = borderState I q w j) : i = j := by
  by_cases hij : i ≤ j
  · exact borderState_injective_le I ht hw hf hi hj hij he
  · exact (borderState_injective_le I ht hw hf hj hi (by omega) he.symm).symm

private theorem nodup_map_on {α β : Type} (g : α → β) (l : List α)
    (hn : l.Nodup)
    (hi : ∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y) : (l.map g).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      have hba := hi b (by simp [hb]) a (by simp) he
      exact ha (hba ▸ hb)
    · exact ih hl (fun x hx y hy h => hi x (by simp [hx]) y (by simp [hy]) h)

/-- At most k borders INCLUDING zero and the full word. In particular this is
not a bound on word length, source visits, or a complete decision procedure. -/
theorem border_count_le (I : Instance k) (ht : TerminalFinals I)
    {q f : Fin k} {w : Word} (hw : runFrom I q w = some f)
    (hf : I.final.get f = true) : (borderLengths w).length ≤ k := by
  have hn : (borderLengths w).Nodup := by
    exact List.Pairwise.filter _ (List.nodup_range (w.length + 1))
  have hm : ((borderLengths w).map (borderState I q w)).Nodup := by
    apply nodup_map_on _ _ hn
    intro i hi j hj he
    exact borderState_injective I ht hw hf hi hj he
  have hb := hm.length_le_of_subset
    (l₂ := List.finRange k) (fun x _ => List.mem_finRange x)
  simpa using hb

/-- Number of nonempty borders; zero is always listed exactly once. -/
def positiveBorderCount (w : Word) : Nat := (borderLengths w).length - 1

theorem positive_border_count_le (I : Instance k) (ht : TerminalFinals I)
    {q f : Fin k} {w : Word} (hw : runFrom I q w = some f)
    (hf : I.final.get f = true) : positiveBorderCount w ≤ k - 1 := by
  have h := border_count_le I ht hw hf
  simp only [positiveBorderCount]
  omega

/-- Uniform bound at EVERY suffix of an accepted run, not just at its initial
state. This is the orientation used for reversed-prefix rank arguments. -/
theorem suffix_positive_border_count_le (I : Instance k) (ht : TerminalFinals I)
    {q f : Fin k} {w : Word} (hw : runFrom I q w = some f)
    (hf : I.final.get f = true) (i : Nat) :
    positiveBorderCount (w.drop i) ≤ k - 1 := by
  exact positive_border_count_le I ht (runFrom_cutState_drop I hw i) hf

#guard borderLengths ([] : Word) == [0]
#guard borderLengths [false, false, false] == [0, 1, 2, 3]
#guard borderLengths [false, true, false] == [0, 1, 3]
#guard positiveBorderCount ([] : Word) == 0

end TerminalRank
end Subtail
