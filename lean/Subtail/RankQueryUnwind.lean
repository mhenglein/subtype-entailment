import Subtail.RankQuery

/-!
# Promotion unwind under the pinned ClosureFor contract

Stage-5 support for A018 issue #30.  This file does not assume ClosureStatement
globally and does not implement a compiler.  It proves the exact semantic
meaning of RankQuery.promote for any particular preimage map that satisfies
the already-pinned ClosureFor contract.
-/
namespace Subtail
namespace RankQueryUnwind

open RankQuery

variable {k : Nat}

/-- Exactly n safe first-return promotions from B to C. -/
inductive Promotes (I : Instance k) : Nat → Reference k → Reference k → Prop
  | refl (B : Reference k) : Promotes I 0 B B
  | step {n : Nat} {B C D : Reference k} :
      FirstReturnExt I B C → Promotes I n C D → Promotes I (n + 1) B D

/-- A zero-length promotion chain changes no reference. -/
theorem promotes_zero_eq {I : Instance k} {B C : Reference k}
    (h : Promotes I 0 B C) : C = B := by
  cases h
  rfl

/-- A positive chain exposes its first safe first-return promotion. -/
theorem promotes_succ_iff {I : Instance k} {n : Nat} {B D : Reference k} :
    Promotes I (n + 1) B D ↔
      ∃ C : Reference k, FirstReturnExt I B C ∧ Promotes I n C D := by
  constructor
  · intro h
    cases h with
    | step hBC hrest => exact ⟨_, hBC, hrest⟩
  · rintro ⟨C, hBC, hrest⟩
    exact Promotes.step hBC hrest

/-- First-return chains preserve safety at their endpoint. -/
theorem promotes_safe {I : Instance k} {n : Nat} {B C : Reference k}
    (hB : SafeReference I B) (h : Promotes I n B C) : SafeReference I C := by
  induction h with
  | refl => exact hB
  | step hBC _ ih => exact ih hBC.safe

/-- Query union has the expected disjunctive semantics. -/
theorem sat_append {G : Graph k} {φ ψ : Query k} :
    Sat G (φ ++ ψ) ↔ Sat G φ ∨ Sat G ψ := by
  constructor
  · rintro ⟨c, hc, hs⟩
    rcases List.mem_append.mp hc with hφ | hψ
    · exact Or.inl ⟨c, hφ, hs⟩
    · exact Or.inr ⟨c, hψ, hs⟩
  · rintro (⟨c, hc, hs⟩ | ⟨c, hc, hs⟩)
    · exact ⟨c, List.mem_append_left _ hc, hs⟩
    · exact ⟨c, List.mem_append_right _ hc, hs⟩

/-- Semantic unwind of Φ_h.  Under ClosureFor, satisfying promote pre φ h at
P(B) is exactly the existence of at most h safe first-return promotions from
B to one reference whose literal prefix graph satisfies φ. -/
theorem sat_promote_iff (I : Instance k) (pre : Query k → Query k)
    (hclosure : ClosureFor I pre) (φ : Query k) :
    ∀ (h : Nat) (B : Reference k), SafeReference I B →
      (Sat (prefixGraph I B) (promote pre φ h) ↔
        ∃ n : Nat, n ≤ h ∧ ∃ C : Reference k,
          Promotes I n B C ∧ Sat (prefixGraph I C) φ) := by
  intro h
  induction h with
  | zero =>
    intro B hB
    constructor
    · intro hs
      exact ⟨0, Nat.le_refl 0, B, Promotes.refl B, hs⟩
    · rintro ⟨n, hn, C, hchain, hs⟩
      have hn0 : n = 0 := by omega
      subst n
      have hCB : C = B := promotes_zero_eq hchain
      subst C
      exact hs
  | succ h ih =>
    intro B hB
    rw [promote, sat_append]
    constructor
    · intro hs
      rcases hs with hprev | hpre
      · obtain ⟨n, hn, C, hchain, hφ⟩ := (ih B hB).mp hprev
        exact ⟨n, by omega, C, hchain, hφ⟩
      · obtain ⟨C, hBC, hprevC⟩ :
          ∃ C : Reference k, FirstReturnExt I B C ∧
            Sat (prefixGraph I C) (promote pre φ h) :=
          (hclosure.1 (promote pre φ h) B hB).mp hpre
        obtain ⟨n, hn, D, hchain, hφ⟩ := (ih C hBC.safe).mp hprevC
        exact ⟨n + 1, by omega, D, Promotes.step hBC hchain, hφ⟩
    · rintro ⟨n, hn, D, hchain, hφ⟩
      cases n with
      | zero =>
        have hDB : D = B := promotes_zero_eq hchain
        subst D
        exact Or.inl ((ih B hB).mpr ⟨0, Nat.zero_le _, B, Promotes.refl B, hφ⟩)
      | succ n =>
        have hn' : n ≤ h := by omega
        obtain ⟨C, hBC, hrest⟩ := (promotes_succ_iff).mp hchain
        have hprevC : Sat (prefixGraph I C) (promote pre φ h) :=
          (ih C hBC.safe).mpr ⟨n, hn', D, hrest, hφ⟩
        have hpre : Sat (prefixGraph I B) (pre (promote pre φ h)) :=
          (hclosure.1 (promote pre φ h) B hB).mpr ⟨C, hBC, hprevC⟩
        exact Or.inr hpre

/-- A convenient exact-h corollary: an n-step chain is always represented at
promotion budget n. -/
theorem sat_promote_of_chain (I : Instance k) (pre : Query k → Query k)
    (hclosure : ClosureFor I pre) (φ : Query k)
    {n : Nat} {B C : Reference k} (hB : SafeReference I B)
    (hchain : Promotes I n B C) (hφ : Sat (prefixGraph I C) φ) :
    Sat (prefixGraph I B) (promote pre φ n) :=
  (sat_promote_iff I pre hclosure φ n B hB).mpr
    ⟨n, Nat.le_refl _, C, hchain, hφ⟩

/-! ## Query-weight consequences of ClosureFor -/

/-- Maximum distributes over list append. -/
theorem maxNat_append (xs ys : List Nat) :
    RankMilestones.maxNat (xs ++ ys) =
      max (RankMilestones.maxNat xs) (RankMilestones.maxNat ys) := by
  induction xs with
  | nil => simp [RankMilestones.maxNat]
  | cons x xs ih =>
    simp only [List.cons_append, RankMilestones.maxNat, ih]
    omega

/-- Query union has maximum clause weight equal to the maximum of the two sides. -/
theorem weight_append (φ ψ : Query k) :
    weight (φ ++ ψ) = max (weight φ) (weight ψ) := by
  simp only [weight, List.map_append, maxNat_append]

/-- A pointwise upper bound on a finite list bounds its maximum. -/
theorem maxNat_le_of_forall {xs : List Nat} {N : Nat}
    (h : ∀ x ∈ xs, x ≤ N) : RankMilestones.maxNat xs ≤ N := by
  induction xs with
  | nil => simp [RankMilestones.maxNat]
  | cons x xs ih =>
    simp only [RankMilestones.maxNat]
    have hx := h x (List.mem_cons_self ..)
    have hrest : ∀ y ∈ xs, y ≤ N := fun y hy => h y (List.mem_cons_of_mem _ hy)
    exact Nat.max_le hx (ih hrest)

/-- The clause-wise bound stored in ClosureFor also bounds the entire preimage query. -/
theorem weight_pre_le (I : Instance k) (pre : Query k → Query k)
    (hclosure : ClosureFor I pre) (φ : Query k) :
    weight (pre φ) ≤ closureBound k (weight φ) := by
  unfold weight
  apply maxNat_le_of_forall
  intro n hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
  exact hclosure.2 φ c hc

/-- One promotion step grows query weight by at most the old weight or the
ClosureFor preimage bound, whichever is larger. -/
theorem weight_promote_succ_le (I : Instance k) (pre : Query k → Query k)
    (hclosure : ClosureFor I pre) (φ : Query k) (h : Nat) :
    weight (promote pre φ (h + 1)) ≤
      max (weight (promote pre φ h))
        (closureBound k (weight (promote pre φ h))) := by
  rw [promote, weight_append]
  exact Nat.max_le (Nat.le_refl _) (weight_pre_le I pre hclosure _)


end RankQueryUnwind
end Subtail
