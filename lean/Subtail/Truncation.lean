import Subtail.Basic

namespace Subtail

/-- Whether the suffix of length `l` has an occurrence starting earlier. -/
def repeatedCheck (w : Word) (l : Nat) : Bool :=
  (List.range (w.length - l)).any (fun i =>
    (w.drop (w.length - l)).isPrefixOf (w.drop i))

theorem repeatedCheck_iff (w : Word) (l : Nat) :
    repeatedCheck w l = true ↔
      ∃ i, i < w.length - l ∧
        (w.drop (w.length - l)).IsPrefix (w.drop i) := by
  simp [repeatedCheck, List.any_eq_true, List.mem_range]

/-- Largest repeated-suffix length at most `n`, defaulting to zero. -/
def lrsAux (w : Word) : Nat → Nat
  | 0 => 0
  | n + 1 => if repeatedCheck w (n + 1) then n + 1 else lrsAux w n

def lrs (w : Word) : Nat := lrsAux w w.length

theorem lrsAux_le (w : Word) (n : Nat) : lrsAux w n ≤ n := by
  induction n with
  | zero => simp [lrsAux]
  | succ n ih => simp only [lrsAux]; split <;> omega

theorem lrs_le_length (w : Word) : lrs w ≤ w.length := lrsAux_le w w.length

theorem lrsAux_zero_or_repeated (w : Word) (n : Nat) :
    lrsAux w n = 0 ∨ repeatedCheck w (lrsAux w n) = true := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    simp only [lrsAux]
    split
    · rename_i hr
      exact Or.inr hr
    · exact ih

theorem repeated_le_lrsAux (w : Word) {l n : Nat}
    (hl : l ≤ n) (hr : repeatedCheck w l = true) : l ≤ lrsAux w n := by
  induction n with
  | zero => simp only [lrsAux]; omega
  | succ n ih =>
    simp only [lrsAux]
    split
    · omega
    · rename_i hn
      have hne : l ≠ n + 1 := by intro he; subst l; exact hn hr
      exact ih (by omega)

/-- The computed value is the greatest repeated-suffix length, with zero
as the default when there is no repeated suffix. -/
theorem lrs_spec (w : Word) :
    lrs w ≤ w.length ∧
    (lrs w = 0 ∨ repeatedCheck w (lrs w) = true) ∧
    ∀ l, l ≤ w.length → repeatedCheck w l = true → l ≤ lrs w := by
  exact ⟨lrs_le_length w, lrsAux_zero_or_repeated w w.length,
    fun _ hl hr => repeated_le_lrsAux w hl hr⟩

theorem repeated_of_agrees (w : Word) {i j : Nat}
    (hij : i < j) (hj : j ≤ w.length) (ha : Agrees w i j) :
    repeatedCheck w (w.length - j) = true := by
  have hsub : w.length - (w.length - j) = j := by omega
  simp only [repeatedCheck, hsub, List.any_eq_true, List.mem_range]
  exact ⟨i, hij, List.isPrefixOf_iff_prefix.mpr ha⟩

theorem agrees_length_le_lrs (w : Word) {i j : Nat}
    (hij : i < j) (hj : j ≤ w.length) (ha : Agrees w i j) :
    w.length - j ≤ lrs w :=
  repeated_le_lrsAux w (Nat.sub_le _ _) (repeated_of_agrees w hij hj ha)

/-- Every source state allowed at the old target is allowed at the new target.
For defined targets, this is precisely incoming forbidden-set inclusion in
the opposite presentation: Pred(new) is a subset of Pred(old). -/
def IncomingLe (I : Instance k) (new old : Option (Fin k)) : Prop :=
  ∀ r, unflaggedCheck I r old = true → unflaggedCheck I r new = true

theorem IncomingLe.refl (I : Instance k) (q : Option (Fin k)) :
    IncomingLe I q q := by intro r h; exact h

theorem incomingLe_iff_flags (I : Instance k) (new old : Fin k) :
    IncomingLe I (some new) (some old) ↔
      ∀ q, (I.flags.get q).get new = true → (I.flags.get q).get old = true := by
  constructor
  · intro hp q hn
    cases ho : (I.flags.get q).get old with
    | false =>
      have hh := hp (some q) (by simp [unflaggedCheck, ho])
      simp [unflaggedCheck, hn] at hh
    | true => rfl
  · intro hp r hr
    cases r with
    | none => simp [unflaggedCheck] at hr
    | some q =>
      cases hn : (I.flags.get q).get new with
      | false => simp [unflaggedCheck, hn]
      | true =>
        have ho := hp q hn
        simp [unflaggedCheck, ho] at hr

theorem suffix_transfer (w v : Word) {h l : Nat}
    (hhv : h ≤ v.length) (hhw : h ≤ w.length) (hl : l ≤ h)
    (hs : v.drop (v.length - h) = w.drop (w.length - h)) :
    v.drop (v.length - l) = w.drop (w.length - l) := by
  have he := congrArg (List.drop (h - l)) hs
  simp only [List.drop_drop] at he
  have hv : v.length - h + (h - l) = v.length - l := by omega
  have hw : w.length - h + (h - l) = w.length - l := by omega
  simpa only [hv, hw] using he

/-- A015: incoming flag dominance only needs sources visited in the retained
prefix. The shorter endpoint must still be accepting. -/
theorem visited_profile_truncation (I : Instance k) (w : Word) {e : Nat}
    (he : e < w.length) (hw : Witness I w)
    (hs : (w.take e).drop (e - lrs (w.take e)) =
      w.drop (w.length - lrs (w.take e)))
    (hf : finalCheck I (stateAt I w e) = true)
    (hp : ∀ l, l ≤ lrs (w.take e) → ∀ i, i ≤ e →
      unflaggedCheck I (stateAt I w i) (stateAt I w (w.length - l)) = true →
      unflaggedCheck I (stateAt I w i) (stateAt I w (e - l)) = true) :
    Witness I (w.take e) := by
  have hlen : (w.take e).length = e := List.length_take_of_le (by omega)
  have hle : lrs (w.take e) ≤ e := by simpa only [hlen] using lrs_le_length (w.take e)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    rw [stateAt_take I w hi]
    exact hw.1 i (by omega)
  · rw [hlen, stateAt_take I w (Nat.le_refl e)]
    exact hf
  · intro j hj i hij ha
    rw [hlen] at hj
    rw [stateAt_take I w (by omega : i ≤ e), stateAt_take I w hj]
    by_cases heq : i = j
    · subst i
      exact hw.2.2 j (by omega) j (Nat.le_refl j) (List.prefix_refl _)
    · have hij' : i < j := by omega
      have hl : e - j ≤ lrs (w.take e) := by
        simpa only [hlen] using agrees_length_le_lrs (w.take e) hij' (by omega) ha
      have hsmall : (w.take e).drop j = w.drop (w.length - (e - j)) := by
        have hh := suffix_transfer w (w.take e) (by omega : lrs (w.take e) ≤ (w.take e).length)
          (by omega : lrs (w.take e) ≤ w.length) hl (by simpa only [hlen] using hs)
        have hback : e - (e - j) = j := by omega
        simpa only [hlen, hback] using hh
      have hprefix : ((w.take e).drop i).IsPrefix (w.drop i) := by
        rw [List.drop_take]
        exact List.take_prefix _ _
      have hold : Agrees w i (w.length - (e - j)) := by
        unfold Agrees
        rw [← hsmall]
        exact ha.trans hprefix
      have hu := hw.2.2 (w.length - (e - j)) (by omega) i (by omega) hold
      have hb : e - (e - j) = j := by omega
      have hp' := hp (e - j) hl
      rw [hb] at hp'
      exact hp' i (by omega) hu

/-- C009 is the special case that compares every possible source state. -/
theorem profile_truncation (I : Instance k) (w : Word) {e : Nat}
    (he : e < w.length) (hw : Witness I w)
    (hs : (w.take e).drop (e - lrs (w.take e)) =
      w.drop (w.length - lrs (w.take e)))
    (hf : finalCheck I (stateAt I w e) = true)
    (hp : ∀ l, l ≤ lrs (w.take e) →
      IncomingLe I (stateAt I w (e - l)) (stateAt I w (w.length - l))) :
    Witness I (w.take e) := by
  apply visited_profile_truncation I w he hw hs hf
  intro l hl i _ hi
  exact hp l hl (stateAt I w i) hi

/-- Determinism transports the state at the start of a shared suffix to
every later position in that suffix. -/
theorem state_suffix_transfer (I : Instance k) (w : Word) {e h l : Nat}
    (he : e ≤ w.length) (hh : h ≤ e) (hl : l ≤ h)
    (hs : (w.take e).drop (e - h) = w.drop (w.length - h))
    (hq : stateAt I w (e - h) = stateAt I w (w.length - h)) :
    stateAt I w (e - l) = stateAt I w (w.length - l) := by
  have heq : e - h + (h - l) = e - l := by omega
  have hnq : w.length - h + (h - l) = w.length - l := by omega
  have heh : e - (e - h) = h := by omega
  rw [List.drop_take, heh] at hs
  have hp := congrArg (List.take (h - l)) hs
  rw [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)] at hp
  rw [← heq, ← hnq, stateAt_add, stateAt_add, hq, hp]

/-- C008: equal states at the shared repeated suffix suffice for a cut. -/
theorem suffix_trace_truncation (I : Instance k) (w : Word) {e : Nat}
    (he : e < w.length) (hw : Witness I w)
    (hs : (w.take e).drop (e - lrs (w.take e)) =
      w.drop (w.length - lrs (w.take e)))
    (hq : stateAt I w (e - lrs (w.take e)) =
      stateAt I w (w.length - lrs (w.take e))) :
    Witness I (w.take e) := by
  have hle : lrs (w.take e) ≤ e := by
    have hh := lrs_le_length (w.take e)
    rw [List.length_take_of_le (by omega)] at hh
    exact hh
  have ht : ∀ l, l ≤ lrs (w.take e) →
      stateAt I w (e - l) = stateAt I w (w.length - l) := by
    intro l hl
    exact state_suffix_transfer I w (by omega) hle hl hs hq
  apply profile_truncation I w he hw hs
  · have hend := ht 0 (Nat.zero_le _)
    simp only [Nat.sub_zero] at hend
    rw [hend]
    exact hw.2.1
  · intro l hl
    rw [ht l hl]
    exact IncomingLe.refl I _

end Subtail
