import Subtail.SummaryBridge

/-!
# An effective two-summary automaton for normalized subtype separation

Every physical state is an explicitly enumerated pair of subsets.
All comparisons use the same candidate word. No model-finiteness assumption.
-/
namespace Subtail.SummaryAutomaton

open TreeSemantics CanonicalModel CanonicalReachability StackSummary StackReachability SummaryBridge

variable {n : Nat}

@[simp] theorem vector_get_ofFn {k : Nat} {α : Type} (f : Fin k → α) (q : Fin k) :
    (Vector.ofFn f).get q = f q := by
  change (Vector.ofFn f)[q.val] = f q
  exact Vector.getElem_ofFn q.isLt

abbrev Summary (n : Nat) := List (Fin n) × List (Fin n)

def states (n : Nat) : List (Summary n) :=
  (subsets (List.finRange n)).flatMap fun B =>
    (subsets (List.finRange n)).map fun A => (B, A)

theorem pair_mem_states {B A : List (Fin n)}
    (hB : B ∈ subsets (List.finRange n)) (hA : A ∈ subsets (List.finRange n)) :
    (B, A) ∈ states n := by
  exact List.mem_flatMap.mpr ⟨B, hB, List.mem_map.mpr ⟨A, hA, rfl⟩⟩

def encode (s : Summary n) (hs : s ∈ states n) : Fin (states n).length :=
  ⟨(states n).idxOf s, List.idxOf_lt_length_of_mem hs⟩

def decode (q : Fin (states n).length) : Summary n := (states n)[q.val]

@[simp] theorem decode_encode (s : Summary n) (hs : s ∈ states n) :
    decode (encode s hs) = s := List.getElem_idxOf _

def popSet (M : System n) (p : Fin n) (w : Word) : List (Fin n) :=
  (List.finRange n).filter fun q => popCheck M p w q

@[simp] theorem mem_popSet (M : System n) (p q : Fin n) (w : Word) :
    q ∈ popSet M p w ↔ Pop M p w q := by
  simp [popSet]

def nextSet (M : System n) (S : List (Fin n)) (a : Bool) : List (Fin n) :=
  (List.finRange n).filter fun q =>
    S.any fun p => (List.finRange n).any fun r => M.pop a p r && balancedCheck M r q

@[simp] theorem mem_nextSet (M : System n) (S : List (Fin n)) (a : Bool) (q : Fin n) :
    q ∈ nextSet M S a ↔ ∃ p, p ∈ S ∧ ∃ r, M.pop a p r = true ∧ Balanced M r q := by
  simp [nextSet, List.any_eq_true]

theorem pop_snoc_iff (M : System n) (p q : Fin n) (w : Word) (a : Bool) :
    Pop M p (w ++ [a]) q ↔
      ∃ r s, Pop M p w r ∧ M.pop a r s = true ∧ Balanced M s q := by
  induction w generalizing p with
  | nil => simp [Pop]
  | cons b w ih =>
    change (∃ r s, Balanced M p r ∧ M.pop b r s = true ∧
      Pop M s (w ++ [a]) q) ↔ _
    constructor
    · rintro ⟨r, s, hr, hp, hs⟩
      obtain ⟨t, u, ht, htu, hu⟩ := (ih s).mp hs
      exact ⟨t, u, ⟨r, s, hr, hp, ht⟩, htu, hu⟩
    · rintro ⟨t, u, ⟨r, s, hr, hp, ht⟩, htu, hu⟩
      exact ⟨r, s, hr, hp, (ih s).mpr ⟨t, u, ht, htu, hu⟩⟩

theorem popSet_snoc (M : System n) (p : Fin n) (w : Word) (a : Bool) :
    popSet M p (w ++ [a]) = nextSet M (popSet M p w) a := by
  apply List.filter_congr
  intro q _
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true, pop_snoc_iff]

def summaryAt (C : List (Constraint n)) (a b : Fin n) (w : Word) : Summary n :=
  (popSet (systemOf C) a w, popSet (reverse (systemOf C)) b w)

theorem summaryAt_mem (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    summaryAt C a b w ∈ states n :=
  pair_mem_states (filter_mem_subsets _ _) (filter_mem_subsets _ _)

def code (C : List (Constraint n)) (a b : Fin n) (w : Word) : Fin (states n).length :=
  encode (summaryAt C a b w) (summaryAt_mem C a b w)

def advancePair (C : List (Constraint n)) (s : Summary n) (x : Bool) : Summary n :=
  (nextSet (systemOf C) s.1 x, nextSet (reverse (systemOf C)) s.2 x)

theorem advancePair_mem (C : List (Constraint n)) (s : Summary n) (x : Bool) :
    advancePair C s x ∈ states n :=
  pair_mem_states (filter_mem_subsets _ _) (filter_mem_subsets _ _)

def advance (C : List (Constraint n)) (q : Fin (states n).length) (x : Bool) :
    Fin (states n).length :=
  encode (advancePair C (decode q) x) (advancePair_mem C (decode q) x)

theorem advance_code (C : List (Constraint n)) (a b : Fin n) (w : Word) (x : Bool) :
    advance C (code C a b w) x = code C a b (w ++ [x]) := by
  simp [advance, code, summaryAt, advancePair, popSet_snoc]

/-- UNSAT is retained as a global Bad bit; no classical SAT branch is used. -/
def summaryInstance (C : List (Constraint n)) (a b : Fin n) :
    Instance (states n).length where
  initial := code C a b []
  transitions := Vector.ofFn fun q => (some (advance C q false), some (advance C q true))
  bad := Vector.ofFn fun q =>
    !(CanonicalReachability.satCheck C) || (decode q).1.any (dangerCheck C)
  final := Vector.ofFn fun q =>
    !((decode q).2.any fun f => decide (∃ l r, Constraint.lower l r f ∈ C))
  flags := Vector.ofFn fun p => Vector.ofFn fun q =>
    (decode p).1.any fun m => decide (m ∈ (decode q).2)

@[simp] theorem summary_step (C : List (Constraint n)) (a b : Fin n)
    (q : Fin (states n).length) (x : Bool) :
    step (summaryInstance C a b) q x = some (advance C q x) := by
  cases x <;> simp [step, summaryInstance]

theorem summary_run (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    runFrom (summaryInstance C a b) (summaryInstance C a b).initial w =
      some (code C a b w) := by
  have aux : ∀ v : Word,
      runFrom (summaryInstance C a b) (summaryInstance C a b).initial v.reverse =
        some (code C a b v.reverse) := by
    intro v
    induction v with
    | nil => rfl
    | cons x v ih =>
      rw [List.reverse_cons, runFrom_append, ih]
      simp [runFrom, advance_code]
  simpa only [List.reverse_reverse] using aux w.reverse

@[simp] theorem summary_stateAt (C : List (Constraint n)) (a b : Fin n)
    (w : Word) (i : Nat) :
    stateAt (summaryInstance C a b) w i = some (code C a b (w.take i)) :=
  summary_run C a b (w.take i)

@[simp] theorem code_safe (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    Subtail.safeCheck (summaryInstance C a b) (some (code C a b w)) = true ↔
      Satisfiable C ∧ ¬ ∃ m, Pop (systemOf C) a w m ∧ Danger C m := by
  simp [Subtail.safeCheck, summaryInstance, code, summaryAt,
    Bool.eq_false_iff, List.any_eq_true, dangerCheck_correct, satCheck_correct]

@[simp] theorem code_final (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    finalCheck (summaryInstance C a b) (some (code C a b w)) = true ↔
      ¬ ForcedConflict C b w := by
  simp [finalCheck, summaryInstance, code, summaryAt,
    Bool.eq_false_iff, List.any_eq_true, ForcedConflict, Forced, and_comm]

@[simp] theorem code_unflagged (C : List (Constraint n)) (a b : Fin n) (u v : Word) :
    unflaggedCheck (summaryInstance C a b) (some (code C a b u))
        (some (code C a b v)) = true ↔
      ¬ ∃ m, Pop (systemOf C) a u m ∧ Pop (reverse (systemOf C)) b v m := by
  simp [unflaggedCheck, summaryInstance, code, summaryAt,
    Bool.eq_false_iff, List.any_eq_true]

theorem witness_iff_conditions (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    Witness (summaryInstance C a b) w ↔
      Satisfiable C ∧ ¬ UnsafeCut C a w ∧
        ¬ ForcedConflict C b w ∧ ¬ CutConflict C a b w := by
  constructor
  · rintro ⟨hs, hf, hg⟩
    have hs' : ∀ i, i ≤ w.length → Satisfiable C ∧
        ¬ ∃ m, Pop (systemOf C) a (w.take i) m ∧ Danger C m := by
      intro i hi
      simpa only [summary_stateAt, code_safe] using hs i hi
    refine ⟨(hs' 0 (Nat.zero_le _)).1, ?_, ?_, ?_⟩
    · rintro ⟨i, hi, m, hm, hd⟩
      exact (hs' i hi).2 ⟨m, hm, hd⟩
    · simpa only [summary_stateAt, List.take_length, code_final] using hf
    · rintro ⟨i, j, hj, hi, ha, m, hm, hn⟩
      have hu := hg j hj i hi ha
      rw [summary_stateAt, summary_stateAt, code_unflagged] at hu
      exact hu ⟨m, hm, hn⟩
  · rintro ⟨hs, hu, hf, hg⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [summary_stateAt, code_safe]
      refine ⟨hs, ?_⟩
      intro hm
      exact hu ⟨i, hi, hm⟩
    · simpa only [summary_stateAt, List.take_length, code_final] using hf
    · intro j hj i hi ha
      rw [summary_stateAt, summary_stateAt, code_unflagged]
      intro hm
      exact hg ⟨i, j, hj, hi, ha, hm⟩

/-- Exact equivalence at the same word, including its empty and diagonal cuts. -/
theorem witness_iff_separation (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    Witness (summaryInstance C a b) w ↔ separationCheck C a b w = true :=
  (witness_iff_conditions C a b w).trans (separation_iff_summaries C a b w).symm

/-- Arbitrary prefix-closed tree semantics; no finite or regular model premise. -/
theorem not_entails_iff_witness (C : List (Constraint n)) (a b : Fin n) :
    ¬ Entails C a b ↔ ∃ w, Witness (summaryInstance C a b) w := by
  rw [not_entails_iff_exists_check]
  exact exists_congr fun w => (witness_iff_separation C a b w).symm

/-- Every reverse pop starts at the parent of a lower constraint. -/
theorem reverse_pop_source_forced (C : List (Constraint n)) (x : Bool) (p q : Fin n)
    (h : (reverse (systemOf C)).pop x p q = true) : Forced C p := by
  cases x with
  | false =>
    obtain ⟨r, hr⟩ := (push_left_spec C q p).mp h
    exact ⟨q, r, hr⟩
  | true =>
    obtain ⟨l, hl⟩ := (push_right_spec C q p).mp h
    exact ⟨l, q, hl⟩

theorem reverse_next_empty (C : List (Constraint n)) (A : List (Fin n)) (x : Bool)
    (h : ¬ ∃ p, p ∈ A ∧ Forced C p) : nextSet (reverse (systemOf C)) A x = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q hq
  obtain ⟨p, hp, r, hr, _⟩ := (mem_nextSet _ _ _ _).mp hq
  exact h ⟨p, hp, reverse_pop_source_forced C x p r hr⟩

theorem final_decode (C : List (Constraint n)) (a b : Fin n)
    (q : Fin (states n).length) :
    (summaryInstance C a b).final.get q = true ↔
      ¬ ∃ f, f ∈ (decode q).2 ∧ Forced C f := by
  simp [summaryInstance, Bool.eq_false_iff, List.any_eq_true, Forced]

/-- Strong absorption, including transitions from unreachable enumerated states. -/
theorem summary_absorbs (C : List (Constraint n)) (a b : Fin n)
    (q : Fin (states n).length) (x : Bool)
    (hq : (summaryInstance C a b).final.get q = true) :
    (summaryInstance C a b).final.get (advance C q x) = true ∧
      ∀ p, ((summaryInstance C a b).flags.get p).get (advance C q x) = false := by
  have he : (decode (advance C q x)).2 = [] := by
    simp only [advance, decode_encode, advancePair]
    exact reverse_next_empty C (decode q).2 x ((final_decode C a b q).mp hq)
  constructor
  · rw [final_decode, he]
    simp
  · intro p
    simp [summaryInstance, he]

end Subtail.SummaryAutomaton

