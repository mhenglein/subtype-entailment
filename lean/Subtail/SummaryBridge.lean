import Subtail.CanonicalReachability

/-!
# Exact ordered-cut form of the arbitrary-tree separating-address criterion

A010/A018, issue #31. No tree-size, stack-height or word-length bound is used.
-/
namespace Subtail.SummaryBridge

open TreeSemantics CanonicalModel CanonicalReachability StackSummary StackReachability

variable {n : Nat}

/-- Membership caused by a forced root. -/
def ForcedConflict (C : List (Constraint n)) (b : Fin n) (w : Word) : Prop :=
  ∃ f, Forced C f ∧ Pop (reverse (systemOf C)) b w f

/-- The ordered pair retains diagonals and the empty terminal suffix. -/
def CutConflict (C : List (Constraint n)) (a b : Fin n) (w : Word) : Prop :=
  ∃ i j, j ≤ w.length ∧ i ≤ j ∧ Agrees w i j ∧
    ∃ m, Pop (systemOf C) a (w.take i) m ∧
      Pop (reverse (systemOf C)) b (w.take j) m

theorem prefix_take_eq {u w : Word} (hu : u <+: w) {i : Nat}
    (hi : i ≤ u.length) : u.take i = w.take i := by
  obtain ⟨z, rfl⟩ := hu
  simp [List.take_append_of_le_length hi]

theorem forced_reaches_iff (C : List (Constraint n)) (b : Fin n) (w : Word) :
    (∃ f, Forced C f ∧ Reaches (systemOf C) (f, []) (b, w)) ↔
      ForcedConflict C b w := by
  constructor
  · rintro ⟨f, hf, hr⟩
    exact ⟨f, hf, (pop_iff_reaches_empty _ _ _ _).mpr (reaches_reverse hr)⟩
  · rintro ⟨f, hf, hp⟩
    refine ⟨f, hf, ?_⟩
    have hr := reaches_reverse ((pop_iff_reaches_empty _ _ _ _).mp hp)
    simpa only [reverse_reverse] using hr

/-- Minimum-stack factorization of a prefix seed is exactly an ordered cut pair. -/
theorem prefix_reaches_iff_cut (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    (∃ u, u <+: w ∧ Reaches (systemOf C) (a, u) (b, w)) ↔
      CutConflict C a b w := by
  constructor
  · rintro ⟨u, hu, hr⟩
    obtain ⟨i, hi, j, hj, m, he, hp, hq⟩ :=
      (normal_iff_cut _ _ _ _ _).mp (reaches_normal hr)
    change i ≤ u.length at hi
    change j ≤ w.length at hj
    change u.drop i = w.drop j at he
    have hlen := congrArg List.length he
    have hul := List.IsPrefix.length_le hu
    simp only [List.length_drop] at hlen
    have hij : i ≤ j := by omega
    refine ⟨i, j, hj, hij, ?_, m, ?_, hq⟩
    · obtain ⟨z, hz⟩ := hu
      refine ⟨z, ?_⟩
      rw [← he, ← hz, List.drop_append_of_le_length hi]
    · rw [← prefix_take_eq hu hi]
      exact hp
  · rintro ⟨i, j, hj, _, hag, m, hp, hq⟩
    refine ⟨w.take i ++ w.drop j, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hag
      refine ⟨z, ?_⟩
      rw [List.append_assoc, hz, List.take_append_drop]
    · exact normal_sound
        ⟨w.take i, w.take j, w.drop j, m, rfl,
          (List.take_append_drop j w).symm, hp, hq⟩

/-- All canonical sources, with no satisfiability assumption omitted. -/
theorem derived_iff_conflict (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    Derived C (pathSeeds C a w) b w ↔
      ForcedConflict C b w ∨ CutConflict C a b w := by
  rw [derived_iff_reaches]
  constructor
  · rintro ⟨p, u, hs, hr⟩
    rcases hs with ⟨hp, rfl⟩ | ⟨hpa, hu⟩
    · exact Or.inl ((forced_reaches_iff C b w).mp ⟨p, hp, hr⟩)
    · subst p
      exact Or.inr ((prefix_reaches_iff_cut C a b w).mp ⟨u, hu, hr⟩)
  · rintro (hf | hc)
    · obtain ⟨f, hf, hr⟩ := (forced_reaches_iff C b w).mpr hf
      exact ⟨f, [], Or.inl ⟨hf, rfl⟩, hr⟩
    · obtain ⟨u, hu, hr⟩ := (prefix_reaches_iff_cut C a b w).mpr hc
      exact ⟨a, u, Or.inr ⟨rfl, hu⟩, hr⟩


/-- A denial can be reached after consuming some word in the reversed system. -/
def Danger (C : List (Constraint n)) (m : Fin n) : Prop :=
  ∃ d, Denied C d ∧ ∃ v, Pop (reverse (systemOf C)) d v m

/-- One prefix summary already suffices to witness a denial violation. -/
def UnsafeCut (C : List (Constraint n)) (a : Fin n) (w : Word) : Prop :=
  ∃ i, i ≤ w.length ∧ ∃ m, Pop (systemOf C) a (w.take i) m ∧ Danger C m

theorem prefix_denial_iff (C : List (Constraint n)) (a : Fin n) (w : Word) :
    (∃ u, u <+: w ∧ ∃ d v, Denied C d ∧
      Reaches (systemOf C) (a, u) (d, v)) ↔ UnsafeCut C a w := by
  constructor
  · rintro ⟨u, hu, d, v, hd, hr⟩
    obtain ⟨i, hi, j, _, m, _, hp, hq⟩ :=
      (normal_iff_cut _ _ _ _ _).mp (reaches_normal hr)
    change i ≤ u.length at hi
    refine ⟨i, Nat.le_trans hi hu.length_le, m, ?_, d, hd, v.take j, hq⟩
    rw [← prefix_take_eq hu hi]
    exact hp
  · rintro ⟨i, _, m, hp, d, hd, v, hq⟩
    refine ⟨w.take i, List.take_prefix i w, d, v, hd, ?_⟩
    exact normal_sound
      ⟨w.take i, v, [], m, by simp, by simp, hp, hq⟩

/-- Separates forced-root satisfiability from safety of every prefix seed. -/
theorem avoids_iff (C : List (Constraint n)) (a : Fin n) (w : Word) :
    AvoidsDenials C (pathSeeds C a w) ↔ Satisfiable C ∧ ¬ UnsafeCut C a w := by
  constructor
  · intro hs
    constructor
    · apply (satisfiable_iff_forced_safe C).mpr
      intro d hd v hv
      apply hs d hd v
      obtain ⟨p, u, hp, hr⟩ := (derived_iff_reaches C _ d v).mp hv
      exact (derived_iff_reaches C _ d v).mpr ⟨p, u, Or.inl hp, hr⟩
    · intro hu
      obtain ⟨u, hup, d, v, hd, hr⟩ := (prefix_denial_iff C a w).mpr hu
      exact hs d hd v ((derived_iff_reaches C _ d v).mpr
        ⟨a, u, Or.inr ⟨rfl, hup⟩, hr⟩)
  · rintro ⟨hSat, hsafe⟩ d hd v hv
    obtain ⟨p, u, hp, hr⟩ := (derived_iff_reaches C _ d v).mp hv
    rcases hp with hf | ⟨hpa, hu⟩
    · exact (satisfiable_iff_forced_safe C).mp hSat d hd v
        ((derived_iff_reaches C _ d v).mpr ⟨p, u, hf, hr⟩)
    · subst p
      exact hsafe ((prefix_denial_iff C a w).mp ⟨u, hu, d, v, hd, hr⟩)

theorem separation_iff_summaries (C : List (Constraint n)) (a b : Fin n) (w : Word) :
    separationCheck C a b w = true ↔
      Satisfiable C ∧ ¬ UnsafeCut C a w ∧
        ¬ ForcedConflict C b w ∧ ¬ CutConflict C a b w := by
  rw [separationCheck_correct, avoids_iff, derived_iff_conflict]
  simp only [not_or, and_assoc]

/-- A total finite test for the fixed control-level danger set. -/
def dangerCheck (C : List (Constraint n)) (m : Fin n) : Bool :=
  (List.finRange n).any fun d =>
    decide (Constraint.denial d ∈ C) && pathCheck (controlEdge (reverse (systemOf C))) d m

theorem dangerCheck_correct (C : List (Constraint n)) (m : Fin n) :
    dangerCheck C m = true ↔ Danger C m := by
  simp [dangerCheck, Danger, Denied, List.any_eq_true, ← exists_pop_iff_path]

end Subtail.SummaryBridge
