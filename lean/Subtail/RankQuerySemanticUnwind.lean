import Subtail.RankQueryCoverage
import Subtail.RankQueryUnwind

/-!
# Semantic promotion unwind without a query-weight hypothesis

A018 / issue #30. The induction is adapted from
`RankQueryUnwind.sat_promote_iff`, retaining its exact conclusion and using
only semantic closure. The concrete corollary uses the current executable
preimage compiler and its checked coverage theorem. Neither result proves
the terminal decision schema, finishing correctness, or a witness bound.
-/
namespace Subtail.RankQuerySemanticUnwind

open RankQuery RankQueryUnwind RankQueryEnumeration

variable {k : Nat}

/-- Query promotion represents at most h first-return extensions. Only the
semantic closure equivalence is required; no clause-weight bound is assumed. -/
theorem sat_promote_iff (I : Instance k) (pre : Query k → Query k)
    (hclosure : ∀ (ψ : Query k) (C : Reference k), SafeReference I C →
      (Sat (prefixGraph I C) (pre ψ) ↔
        ∃ D : Reference k, FirstReturnExt I C D ∧ Sat (prefixGraph I D) ψ)) (φ : Query k) :
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
          (hclosure (promote pre φ h) B hB).mp hpre
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
          (hclosure (promote pre φ h) B hB).mpr ⟨C, hBC, hprevC⟩
        exact Or.inr hpre

/-- The concrete finite compiler has the promotion-chain semantics with no
undischarged closure or weight hypothesis. Base safety remains essential. -/
theorem sat_promote_preimage_iff (I : Instance k) (φ : Query k)
    (h : Nat) (B : Reference k) (hB : SafeReference I B) :
    Sat (prefixGraph I B)
        (promote (preimage I RankQueryCoverage.budget) φ h) ↔
      ∃ n : Nat, n ≤ h ∧ ∃ C : Reference k,
        Promotes I n B C ∧ Sat (prefixGraph I C) φ := by
  exact sat_promote_iff I (preimage I RankQueryCoverage.budget) (fun ψ C hC => RankQueryCoverage.closure_iff I C hC ψ) φ h B hB

end Subtail.RankQuerySemanticUnwind
