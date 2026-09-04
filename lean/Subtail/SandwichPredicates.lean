import Subtail.Truncation

/-!
# Finite necessary and sufficient sandwich predicates

This file formalizes the direct word predicates from memo Definition 8.6.
`Necessary` checks the border obligations whose border length or induced
period is within the finite budget.  `Sufficient` adds the occurrence bound
that rules out every remaining long border.

The predicates use the direct forward-word form of the occurrence bound.  A
suffix of length `L + 1` may occur at a start `t`; its last possible start is
`w.length - (L + 1)`, so the condition says that this last start is at most
`t + D`.  The reversal lemma below connects this form to the memo/Python form
that searches for late occurrences of a prefix in `reverse w`.

These results concern an arbitrary finite annotated binary instance.  They do
not formalize the construction of that instance from subtype constraints,
and they do not establish a global computable budget bound.
-/

namespace Subtail

/-- The safety and final-state part shared by `Witness` and `Necessary`. -/
def Admissible (I : Instance k) (w : Word) : Prop :=
  (∀ i, i ≤ w.length → safeCheck I (stateAt I w i) = true) ∧
  finalCheck I (stateAt I w w.length) = true

/-!
`Necessary I w L D` keeps the admissibility checks and checks only agreement
pairs with border length `w.length - j ≤ L` or induced period `j - i ≤ D`.
The endpoints, diagonal pairs, and empty-suffix pairs remain included when
their corresponding inequality holds.
-/
def Necessary (I : Instance k) (w : Word) (L D : Nat) : Prop :=
  Admissible I w ∧
  ∀ j, j ≤ w.length → ∀ i, i ≤ j → Agrees w i j →
    (w.length - j ≤ L ∨ j - i ≤ D) →
    unflaggedCheck I (stateAt I w i) (stateAt I w j) = true

/--
The occurrence side-condition in the direct forward-word presentation of
`S''(L,D)`.  When `w.length ≤ L` there is no unchecked border.  Otherwise,
every occurrence of the final suffix of length `L + 1` must start within `D`
positions of its last possible start.
-/
def SuffixBound (w : Word) (L D : Nat) : Prop :=
  w.length ≤ L ∨
    ∀ t, t + (L + 1) ≤ w.length →
      (w.drop (w.length - (L + 1))).IsPrefix (w.drop t) →
      w.length - (L + 1) ≤ t + D

/-- The memo's sufficient predicate: the finite checks plus `SuffixBound`. -/
def Sufficient (I : Instance k) (w : Word) (L D : Nat) : Prop :=
  Necessary I w L D ∧ SuffixBound w L D

/-- Dropping the same prefix from a shorter list preserves a prefix relation. -/
theorem prefix_drop_of_le {α : Type} {u v : List α} {r : Nat}
    (h : u <+: v) (hr : r ≤ u.length) : u.drop r <+: v.drop r := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  rw [← ht, List.drop_append]
  simp [Nat.sub_eq_zero_of_le hr]

/-- Reversing an `h`-letter block identifies its location in the reversed word. -/
theorem reverse_block (w : Word) {t h : Nat}
    (ht : t + h ≤ w.length) :
    ((w.drop t).take h).reverse =
      (w.reverse.drop (w.length - h - t)).take h := by
  rw [List.reverse_take, List.reverse_drop, List.drop_take]
  simp only [List.length_drop]
  have hsub : w.length - t - h = w.length - h - t := by
    rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]
  rw [hsub]
  have hht : h ≤ w.length - t := Nat.le_sub_of_add_le (by
    simpa [Nat.add_comm] using ht)
  have hinner : w.length - t - (w.length - h - t) = h := by
    rw [show w.length - h - t = (w.length - t) - h by
      rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]]
    exact Nat.sub_sub_self hht
  rw [hinner]

/--
An occurrence of the final `h`-letter suffix is exactly an occurrence of the
reversed prefix in the reversed word.  The index `w.length - h - t` is the
corresponding reverse-reading start.
-/
theorem reverse_occurrence_iff (w : Word) {t h : Nat}
    (ht : t + h ≤ w.length) :
    (w.drop (w.length - h)).IsPrefix (w.drop t) ↔
      ((w.reverse.drop (w.length - h - t)).take h =
        w.reverse.take h) := by
  have hh : h ≤ w.length := by omega
  rw [List.prefix_iff_eq_take]
  have hsuf : (w.drop (w.length - h)).length = h := by
    simp only [List.length_drop]
    exact Nat.sub_sub_self hh
  rw [hsuf]
  have hrev_take : (w.reverse.take h).reverse = w.drop (w.length - h) := by
    rw [List.reverse_take]
    simp only [List.length_reverse, List.reverse_reverse]
  have hblock : ((w.drop t).take h).reverse =
      (w.reverse.drop (w.length - h - t)).take h :=
    reverse_block w ht
  constructor
  · intro heq
    have hr : (w.drop (w.length - h)).reverse =
        ((w.drop t).take h).reverse := congrArg List.reverse heq
    have hleft : (w.drop (w.length - h)).reverse = w.reverse.take h := by
      rw [← hrev_take, List.reverse_reverse]
    calc
      (w.reverse.drop (w.length - h - t)).take h =
          ((w.drop t).take h).reverse := hblock.symm
      _ = (w.drop (w.length - h)).reverse := hr.symm
      _ = w.reverse.take h := hleft
  · intro heq
    have hr : ((w.reverse.drop (w.length - h - t)).take h).reverse =
        (w.reverse.take h).reverse := congrArg List.reverse heq
    have htarget : ((w.reverse.drop (w.length - h - t)).take h).reverse =
        (w.drop t).take h := by
      calc
        ((w.reverse.drop (w.length - h - t)).take h).reverse =
            ((w.drop t).take h).reverse.reverse := by rw [hblock]
        _ = (w.drop t).take h := List.reverse_reverse _
    calc
      w.drop (w.length - h) = (w.reverse.take h).reverse := hrev_take.symm
      _ = ((w.reverse.drop (w.length - h - t)).take h).reverse := hr.symm
      _ = (w.drop t).take h := htarget

/--
The direct occurrence bound is equivalent to the reversed-prefix formulation
used by the Python checker: no occurrence of `reverse w`'s first `L + 1`
letters may start at a position greater than `D`.
-/
def ReverseSuffixBound (w : Word) (L D : Nat) : Prop :=
  w.length ≤ L ∨
    ∀ s, D < s → s + (L + 1) ≤ w.length →
      (w.reverse.drop s).take (L + 1) ≠ w.reverse.take (L + 1)

theorem suffixBound_iff_reverseSuffixBound (w : Word) (L D : Nat) :
    SuffixBound w L D ↔ ReverseSuffixBound w L D := by
  by_cases hshort : w.length ≤ L
  · simp [SuffixBound, ReverseSuffixBound, hshort]
  · have hh : L + 1 ≤ w.length := by omega
    constructor
    · intro hside
      right
      intro s hs hsl heq
      have hsle : s ≤ w.length - (L + 1) := by
        apply Nat.le_sub_of_add_le
        simpa [Nat.add_comm] using hsl
      let t := w.length - (L + 1) - s
      have hsum : t + s = w.length - (L + 1) := by
        dsimp [t]
        exact Nat.sub_add_cancel hsle
      have htbound : t + (L + 1) ≤ w.length := by
        have htle : t ≤ w.length - (L + 1) := by
          dsimp [t]
          exact Nat.sub_le _ _
        calc
          t + (L + 1) ≤ (w.length - (L + 1)) + (L + 1) :=
            Nat.add_le_add_right htle _
          _ = w.length := Nat.sub_add_cancel hh
      have hindex : w.length - (L + 1) - t = s := by
        dsimp [t]
        exact Nat.sub_sub_self hsle
      have heq' :
          (w.reverse.drop (w.length - (L + 1) - t)).take (L + 1) =
            w.reverse.take (L + 1) := by
        simpa [hindex] using heq
      have hocc := (reverse_occurrence_iff w (t := t) (h := L + 1)
        htbound).mpr heq'
      have hlast := hside.resolve_left hshort
      have hbound := hlast t htbound hocc
      omega
    · intro hside
      right
      intro t ht hocc
      have htle : t ≤ w.length - (L + 1) := by
        apply Nat.le_sub_of_add_le
        simpa [Nat.add_comm] using ht
      by_cases hbound : w.length - (L + 1) ≤ t + D
      · exact hbound
      · let s := w.length - (L + 1) - t
        have hsum : t + s = w.length - (L + 1) := by
          dsimp [s]
          exact Nat.add_sub_of_le htle
        have hsl : s + (L + 1) ≤ w.length := by
          have hsle : s ≤ w.length - (L + 1) := by
            dsimp [s]
            exact Nat.sub_le _ _
          calc
            s + (L + 1) ≤ (w.length - (L + 1)) + (L + 1) :=
              Nat.add_le_add_right hsle _
            _ = w.length := Nat.sub_add_cancel hh
        have hs : D < s := by omega
        have heq :
            (w.reverse.drop s).take (L + 1) = w.reverse.take (L + 1) := by
          have heq' := (reverse_occurrence_iff w (t := t) (h := L + 1)
            ht).mp hocc
          simpa [s] using heq'
        have hlate := hside.resolve_left hshort
        exact False.elim (hlate s hs hsl heq)

/--
An unchecked agreement produces a late occurrence of the final suffix.  This
is the key combinatorial step in `Sufficient -> Witness`.
-/
theorem occurrence_from_agrees (w : Word) {i j L : Nat}
    (hi : i ≤ j) (hj : j ≤ w.length) (ha : Agrees w i j)
    (hlong : L < w.length - j) :
    let h := L + 1
    let t := i + (w.length - j) - h
    t + h ≤ w.length ∧
      (w.drop (w.length - h)).IsPrefix (w.drop t) := by
  dsimp
  let a := w.length - j
  let h := L + 1
  have hha : h ≤ a := by dsimp [h, a]; omega
  have hja : j + a = w.length := by dsimp [a]; omega
  have hp := prefix_drop_of_le ha (r := a - h) (by simp [a])
  have hleft : j + (a - h) = w.length - h := by omega
  have hright : i + (a - h) = i + a - h := by omega
  have hp' : (w.drop (w.length - h)).IsPrefix (w.drop (i + a - h)) := by
    simpa only [List.drop_drop, hleft, hright] using hp
  have ht : i + a - h + h ≤ w.length := by omega
  exact ⟨ht, hp'⟩

/-- Every witness satisfies every finite necessary budget. -/
theorem witness_implies_necessary (I : Instance k) (w : Word)
    (L D : Nat) (hw : Witness I w) : Necessary I w L D := by
  refine ⟨⟨hw.1, hw.2.1⟩, ?_⟩
  intro j hj i hi ha _
  exact hw.2.2 j hj i hi ha

/-- The sufficient predicate implies the full direct witness condition. -/
theorem sufficient_implies_witness (I : Instance k) (w : Word) (L D : Nat)
    (hs : Sufficient I w L D) : Witness I w := by
  rcases hs with ⟨hn, ho⟩
  refine ⟨hn.1.1, hn.1.2, ?_⟩
  intro j hj i hi ha
  by_cases hsmall : w.length - j ≤ L ∨ j - i ≤ D
  · exact hn.2 j hj i hi ha hsmall
  have hlong : L < w.length - j := by omega
  have hperiod : D < j - i := by omega
  have hnotshort : ¬ w.length ≤ L := by omega
  rcases ho with hshort | ho
  · exact False.elim (hnotshort hshort)
  have horc := occurrence_from_agrees w hi hj ha hlong
  dsimp at horc
  let t := i + (w.length - j) - (L + 1)
  have ht := horc.1
  have hocc := horc.2
  have hbound := ho t ht hocc
  exfalso
  omega

/--
Every witness satisfies the sufficient predicate at its own longest repeated
suffix, with zero distance allowance.  This is the individual coverage fact
used by the memo; it is not a bound on `lrs` as a function of the instance.
-/
theorem witness_implies_sufficient_lrs (I : Instance k) (w : Word)
    (hw : Witness I w) : Sufficient I w (lrs w) 0 := by
  refine ⟨witness_implies_necessary I w (lrs w) 0 hw, ?_⟩
  by_cases hshort : w.length ≤ lrs w
  · exact Or.inl hshort
  · right
    intro t ht hocc
    by_cases hbound : w.length - (lrs w + 1) ≤ t + 0
    · exact hbound
    · have hlt : t < w.length - (lrs w + 1) := by omega
      have hrep : repeatedCheck w (lrs w + 1) = true := by
        apply (repeatedCheck_iff w (lrs w + 1)).mpr
        exact ⟨t, hlt, hocc⟩
      have hle : lrs w + 1 ≤ lrs w := by
        apply (lrs_spec w).2.2 (lrs w + 1)
        · omega
        · exact hrep
      omega

/-!
## Executable checks

The Boolean definitions mirror the propositions above.  They use only finite
`List.range`/`List.all` computations and the computable natural-number
decider.  Their correctness theorems are separate from the mathematical
statement so a bounded native run cannot be mistaken for the proof.
-/

def admissibleCheck (I : Instance k) (w : Word) : Bool :=
  (List.range (w.length + 1)).all (fun i => safeCheck I (stateAt I w i)) &&
    finalCheck I (stateAt I w w.length)

theorem admissibleCheck_correct (I : Instance k) (w : Word) :
    admissibleCheck I w = true ↔ Admissible I w := by
  simp [admissibleCheck, Admissible, List.all_eq_true, List.mem_range,
    Nat.lt_succ_iff]

def necessaryCheck (I : Instance k) (w : Word) (L D : Nat) : Bool :=
  admissibleCheck I w &&
    (List.range (w.length + 1)).all (fun j =>
      (List.range (j + 1)).all (fun i =>
        if (w.drop j).isPrefixOf (w.drop i) &&
            decide (w.length - j ≤ L ∨ j - i ≤ D) then
          unflaggedCheck I (stateAt I w i) (stateAt I w j)
        else true))

theorem necessaryCheck_correct (I : Instance k) (w : Word) (L D : Nat) :
    necessaryCheck I w L D = true ↔ Necessary I w L D := by
  rw [necessaryCheck, Bool.and_eq_true, admissibleCheck_correct]
  simp only [List.all_eq_true, List.mem_range, Nat.lt_succ_iff,
    Bool.and_eq_true, List.isPrefixOf_iff_prefix, decide_eq_true_eq,
    Necessary, Agrees]
  constructor
  · rintro ⟨ha, hcheck⟩
    refine ⟨ha, ?_⟩
    intro j hj i hi hag hsmall
    have hji := hcheck j hj i hi
    have hcond : w.drop j <+: w.drop i ∧
        (w.length - j ≤ L ∨ j - i ≤ D) := ⟨hag, hsmall⟩
    rw [if_pos hcond] at hji
    exact hji
  · rintro ⟨ha, hflags⟩
    refine ⟨ha, ?_⟩
    intro j hj i hi
    by_cases hp : (w.drop j).IsPrefix (w.drop i)
    · by_cases hb : w.length - j ≤ L ∨ j - i ≤ D
      · have hcond : w.drop j <+: w.drop i ∧
            (w.length - j ≤ L ∨ j - i ≤ D) := ⟨hp, hb⟩
        rw [if_pos hcond]
        exact hflags j hj i hi hp hb
      · have hcond : ¬ (w.drop j <+: w.drop i ∧
            (w.length - j ≤ L ∨ j - i ≤ D)) := by
          intro hcond
          exact hb hcond.2
        rw [if_neg hcond]
    · have hcond : ¬ (w.drop j <+: w.drop i ∧
          (w.length - j ≤ L ∨ j - i ≤ D)) := by
        intro hcond
        exact hp hcond.1
      rw [if_neg hcond]

def suffixBoundCheck (w : Word) (L D : Nat) : Bool :=
  if w.length ≤ L then true else
    (List.range (w.length - (L + 1) + 1)).all (fun t =>
      if (w.drop (w.length - (L + 1))).isPrefixOf (w.drop t) then
        decide (w.length - (L + 1) ≤ t + D)
      else true)

theorem suffixBoundCheck_correct (w : Word) (L D : Nat) :
    suffixBoundCheck w L D = true ↔ SuffixBound w L D := by
  by_cases hshort : w.length ≤ L
  · simp [suffixBoundCheck, SuffixBound, hshort]
  · have hh : L + 1 ≤ w.length := by omega
    rw [suffixBoundCheck, if_neg hshort]
    constructor
    · intro h
      right
      intro t ht hocc
      have htrange : t < w.length - (L + 1) + 1 := by omega
      have hall := (List.all_eq_true.mp h) t (List.mem_range.mpr htrange)
      have hpbool : (w.drop (w.length - (L + 1))).isPrefixOf (w.drop t) = true :=
        List.isPrefixOf_iff_prefix.mpr hocc
      simp only [hpbool, if_true, decide_eq_true_eq] at hall
      exact hall
    · intro h
      have hside := h.resolve_left hshort
      apply List.all_eq_true.mpr
      intro t ht
      have ht' : t < w.length - (L + 1) + 1 := List.mem_range.mp ht
      have htle : t ≤ w.length - (L + 1) := by
        exact Nat.lt_succ_iff.mp ht'
      have htrange : t + (L + 1) ≤ w.length := by
        calc
          t + (L + 1) ≤ (w.length - (L + 1)) + (L + 1) :=
            Nat.add_le_add_right htle _
          _ = w.length := Nat.sub_add_cancel hh
      by_cases hp : (w.drop (w.length - (L + 1))).IsPrefix (w.drop t)
      · have hpbool : (w.drop (w.length - (L + 1))).isPrefixOf (w.drop t) = true :=
          List.isPrefixOf_iff_prefix.mpr hp
        simp only [hpbool, if_true, decide_eq_true_eq]
        exact hside t htrange hp
      · have hpbool : (w.drop (w.length - (L + 1))).isPrefixOf (w.drop t) = false := by
          cases he : (w.drop (w.length - (L + 1))).isPrefixOf (w.drop t) with
          | false => rfl
          | true => exact False.elim (hp (List.isPrefixOf_iff_prefix.mp he))
        simp [hpbool]

def sufficientCheck (I : Instance k) (w : Word) (L D : Nat) : Bool :=
  necessaryCheck I w L D && suffixBoundCheck w L D

theorem sufficientCheck_correct (I : Instance k) (w : Word) (L D : Nat) :
    sufficientCheck I w L D = true ↔ Sufficient I w L D := by
  simp [sufficientCheck, necessaryCheck_correct, suffixBoundCheck_correct,
    Sufficient]

/-!
The theorem `sufficient_implies_witness` is the main semantic result here.
The Boolean checkers are exact finite implementations of the displayed
predicates.  No finite-state automaton construction or global budget theorem
is claimed.
-/

end Subtail
