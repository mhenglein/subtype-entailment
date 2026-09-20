import Subtail.StackSummary
import Subtail.FiniteSearch

/-!
An executable finite saturation for `StackSummary.Balanced`.

The reference implementation in `StackSummary` intersects all finite
relations.  This module instead starts with the four Horn bases and repeatedly
adds all transitive and push/pop consequences.  The carrier is the finite list
of all control pairs, so the proof can stop after one more round than the
carrier length.  The extra round is a termination bound, not a bound on stack
height.
-/
namespace Subtail
namespace StackSummaryFast

open StackSummary

abbrev Pair (n : Nat) := Fin n × Fin n

/-! The one-round consequences of a relation. -/
inductive Derivable (M : System n) (R : List (Pair n)) :
    Fin n → Fin n → Prop where
  | refl (p) : Derivable M R p p
  | eps {p q} : M.eps p q = true → Derivable M R p q
  | trans {p q r} : (p, q) ∈ R → (q, r) ∈ R → Derivable M R p r
  | wrap {a p q r s} : M.push a p q = true → (q, r) ∈ R →
      M.pop a r s = true → Derivable M R p s

def relationMember (R : List (Pair n)) (p q : Fin n) : Bool :=
  decide ((p, q) ∈ R)

def transStep (R : List (Pair n)) (p q : Fin n) : Bool :=
  (List.finRange n).any fun r =>
    relationMember R p r && relationMember R r q

def wrapLetter (M : System n) (R : List (Pair n)) (a : Bool)
    (p q : Fin n) : Bool :=
  (List.finRange n).any fun r =>
    (List.finRange n).any fun s =>
      decide (M.push a p r = true) && relationMember R r s &&
        decide (M.pop a s q = true)

@[simp] theorem wrapLetter_eq_true (M : System n) (R : List (Pair n))
    (a : Bool) (p q : Fin n) :
    wrapLetter M R a p q = true ↔
      ∃ r s, M.push a p r = true ∧ (r, s) ∈ R ∧ M.pop a s q = true := by
  simp [wrapLetter, relationMember, List.any_eq_true]
  constructor
  · rintro ⟨r, s, ⟨h₁, h₂⟩, h₃⟩
    exact ⟨r, h₁, s, h₂, h₃⟩
  · rintro ⟨r, h₁, s, h₂, h₃⟩
    exact ⟨r, s, ⟨h₁, h₂⟩, h₃⟩

def wrapStep (M : System n) (R : List (Pair n)) (p q : Fin n) : Bool :=
  wrapLetter M R false p q || wrapLetter M R true p q

def derivable (M : System n) (R : List (Pair n)) (p q : Fin n) : Bool :=
  decide (p = q) || (M.eps p q || (transStep R p q || wrapStep M R p q))

@[simp] theorem transStep_eq_true (R : List (Pair n)) (p q : Fin n) :
    transStep R p q = true ↔ ∃ r, (p, r) ∈ R ∧ (r, q) ∈ R := by
  simp [transStep, relationMember, List.any_eq_true]

@[simp] theorem wrapStep_eq_true (M : System n) (R : List (Pair n))
    (p q : Fin n) :
    wrapStep M R p q = true ↔
    ∃ a r s, M.push a p r = true ∧ (r, s) ∈ R ∧ M.pop a s q = true := by
  simp only [wrapStep, Bool.or_eq_true, wrapLetter_eq_true]
  constructor
  · rintro (h | h)
    · rcases h with ⟨r, s, h₁, h₂, h₃⟩
      exact ⟨false, r, s, h₁, h₂, h₃⟩
    · rcases h with ⟨r, s, h₁, h₂, h₃⟩
      exact ⟨true, r, s, h₁, h₂, h₃⟩
  · rintro ⟨a, r, s, h₁, h₂, h₃⟩
    cases a
    · exact Or.inl ⟨r, s, h₁, h₂, h₃⟩
    · exact Or.inr ⟨r, s, h₁, h₂, h₃⟩

theorem derivable_eq_true_iff (M : System n) (R : List (Pair n))
    (p q : Fin n) : derivable M R p q = true ↔ Derivable M R p q := by
  constructor
  · intro h
    have h' : p = q ∨ M.eps p q = true ∨
        (∃ r, (p, r) ∈ R ∧ (r, q) ∈ R) ∨
        (∃ a r s, M.push a p r = true ∧ (r, s) ∈ R ∧
          M.pop a s q = true) := by
      simpa [derivable, transStep_eq_true, wrapStep_eq_true, or_assoc] using h
    rcases h' with rfl | he | ⟨r, h₁, h₂⟩ | ⟨a, r, s, h₁, h₂, h₃⟩
    · exact .refl _
    · exact .eps he
    · exact .trans h₁ h₂
    · exact .wrap h₁ h₂ h₃
  · intro h
    cases h with
    | refl => simp [derivable]
    | eps he => simp [derivable, he]
    | trans h₁ h₂ =>
        have ht : transStep R p q = true :=
          (transStep_eq_true R p q).mpr ⟨_, h₁, h₂⟩
        simp [derivable, ht]
    | wrap h₁ h₂ h₃ =>
        have hw : wrapStep M R p q = true :=
          (wrapStep_eq_true M R p q).mpr ⟨_, _, _, h₁, h₂, h₃⟩
        simp [derivable, hw]

def candidates (M : System n) (R : List (Pair n)) : List (Pair n) :=
  (pairs n).filter fun x => derivable M R x.1 x.2

def close (M : System n) (R : List (Pair n)) : List (Pair n) :=
  FiniteSearch.addNew R (candidates M R)

def iter (M : System n) : Nat → List (Pair n) → List (Pair n)
  | 0, R => R
  | k + 1, R => iter M k (close M R)

/-! Stop at a fixed point when one is reached early. -/
def saturate (M : System n) : Nat → List (Pair n) → List (Pair n)
  | 0, R => R
  | k + 1, R =>
    let next := close M R
    if next = R then R else saturate M k next

theorem mem_close_iff (M : System n) (R : List (Pair n)) (p q : Fin n) :
    (p, q) ∈ close M R ↔
      (p, q) ∈ R ∨ Derivable M R p q := by
  simp [close, candidates, derivable_eq_true_iff,
    FiniteSearch.mem_addNew]

theorem close_subset (M : System n) {R : List (Pair n)} {p q : Fin n}
    (h : (p, q) ∈ R) : (p, q) ∈ close M R := by
  exact (mem_close_iff M R p q).mpr (Or.inl h)

theorem close_nodup (M : System n) {R : List (Pair n)} (hR : R.Nodup) :
    (close M R).Nodup := by
  exact FiniteSearch.nodup_addNew hR

theorem close_length_mono (M : System n) (R : List (Pair n)) :
    R.length ≤ (close M R).length := by
  exact FiniteSearch.length_addNew_le

theorem close_subset_pairs (M : System n) {R : List (Pair n)}
    (hR : ∀ x ∈ R, x ∈ pairs n) :
    ∀ x ∈ close M R, x ∈ pairs n := by
  intro x hx
  change x ∈ FiniteSearch.addNew R (candidates M R) at hx
  rw [FiniteSearch.mem_addNew] at hx
  rcases hx with hx | hx
  · exact hR x hx
  · exact (List.mem_filter.mp hx).1

theorem mem_iter (M : System n) {R : List (Pair n)} (k : Nat)
    {p q : Fin n} (h : (p, q) ∈ R) :
    (p, q) ∈ iter M k R := by
  induction k generalizing R with
  | zero => exact h
  | succ k ih => exact ih (close_subset M h)

theorem nodup_iter (M : System n) {R : List (Pair n)} (hR : R.Nodup) :
    ∀ k, (iter M k R).Nodup := by
  intro k
  induction k generalizing R with
  | zero => exact hR
  | succ k ih => exact ih (close_nodup M hR)

theorem subset_iter_pairs (M : System n) (R : List (Pair n))
    (hR : ∀ x ∈ R, x ∈ pairs n) :
    ∀ k x, x ∈ iter M k R → x ∈ pairs n := by
  intro k
  induction k generalizing R with
  | zero => exact hR
  | succ k ih =>
    intro x hx
    rw [iter] at hx
    exact ih (R := close M R) (close_subset_pairs M hR) x hx

theorem iter_of_fixed (M : System n) {R : List (Pair n)}
    (h : close M R = R) : ∀ k, iter M k R = R := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [iter, h, ih]

theorem saturate_eq_iter (M : System n) (k : Nat) (R : List (Pair n)) :
    saturate M k R = iter M k R := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    simp only [saturate]
    split
    · next h => rw [iter, h, iter_of_fixed M h]
    · exact ih _

/-! A fixed relation satisfies all four clauses of `Closed`. -/
theorem closed_of_fixed (M : System n) {R : List (Pair n)}
    (h : close M R = R) : Closed M (fun p q => (p, q) ∈ R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    have hmem := (mem_close_iff M R p p).mpr (.inr (.refl p))
    rw [h] at hmem
    exact hmem
  · intro p q he
    have hmem := (mem_close_iff M R p q).mpr (.inr (.eps he))
    rw [h] at hmem
    exact hmem
  · intro p q r hpq hqr
    have hmem :=
      (mem_close_iff M R p r).mpr (.inr (.trans hpq hqr))
    rw [h] at hmem
    exact hmem
  · intro a p q r s hpq hqr hrs
    have hd : Derivable M R p s := .wrap hpq hqr hrs
    have hmem := (mem_close_iff M R p s).mpr (Or.inr hd)
    rw [h] at hmem
    exact hmem

/-! Every generated relation is contained in the inductive balanced closure. -/
theorem derivable_sound (M : System n) {R : List (Pair n)}
    (hR : ∀ p q, (p, q) ∈ R → Balanced M p q) {p q : Fin n}
    (h : Derivable M R p q) : Balanced M p q := by
  cases h with
  | refl p => exact .refl p
  | eps he => exact .eps he
  | trans hpr hrq => exact .trans (hR _ _ hpr) (hR _ _ hrq)
  | wrap hpush hrs hpop => exact .wrap hpush (hR _ _ hrs) hpop

theorem close_sound (M : System n) {R : List (Pair n)}
    (hR : ∀ p q, (p, q) ∈ R → Balanced M p q) :
    ∀ p q, (p, q) ∈ close M R → Balanced M p q := by
  intro p q hpq
  rcases (mem_close_iff M R p q).mp hpq with hR' | hd
  · exact hR _ _ hR'
  · exact derivable_sound M hR hd

theorem iter_sound (M : System n) :
    ∀ k R, (∀ p q, (p, q) ∈ R → Balanced M p q) →
      ∀ p q, (p, q) ∈ iter M k R → Balanced M p q := by
  intro k
  induction k with
  | zero =>
    intro R hR p q hpq
    exact hR p q hpq
  | succ k ih =>
    intro R hR p q hpq
    rw [iter] at hpq
    exact ih (close M R) (close_sound M hR) p q hpq

/-! A non-fixed round strictly grows the duplicate-free relation. -/
theorem close_ne_length_lt (M : System n) {R : List (Pair n)}
    (h : close M R ≠ R) : R.length < (close M R).length := by
  exact FiniteSearch.addNew_ne_lt h

theorem closed_or_grow (M : System n) {R : List (Pair n)} :
    ∀ k,
      Closed M (fun p q => (p, q) ∈ iter M k R) ∨
        R.length + k ≤ (iter M k R).length := by
  intro k
  induction k generalizing R with
  | zero => exact Or.inr (by simp [iter])
  | succ k ih =>
    by_cases hf : close M R = R
    · left
      rw [iter, hf, iter_of_fixed M hf]
      exact closed_of_fixed M hf
    · rcases ih (R := close M R) with hc | hg
      · left
        exact hc
      · right
        have hlt := close_ne_length_lt M hf
        simp only [iter]
        change R.length + (k + 1) ≤ (iter M k (close M R)).length
        change R.length < (close M R).length at hlt
        omega

theorem closed_saturate (M : System n) :
    Closed M (fun p q => (p, q) ∈ saturate M ((pairs n).length + 1) []) := by
  rw [saturate_eq_iter]
  rcases closed_or_grow M (R := []) ((pairs n).length + 1) with hc | hg
  · exact hc
  · have hn := nodup_iter M (R := []) (by simp) ((pairs n).length + 1)
    have hsub : ∀ x ∈ iter M ((pairs n).length + 1) [], x ∈ pairs n := by
      exact subset_iter_pairs M [] (by simp) _
    have hle := hn.length_le_of_subset hsub
    simp only [List.length_nil, Nat.zero_add] at hg
    omega

def balancedTable (M : System n) : List (Pair n) :=
  saturate M ((pairs n).length + 1) []

theorem balancedTable_closed (M : System n) :
    Closed M (fun p q => (p, q) ∈ balancedTable M) := by
  exact closed_saturate M

theorem balancedTable_sound (M : System n) {p q : Fin n}
    (h : (p, q) ∈ balancedTable M) : Balanced M p q := by
  exact iter_sound M ((pairs n).length + 1) [] (by simp) p q
    (by simpa [balancedTable, saturate_eq_iter] using h)

theorem balancedTable_complete (M : System n) {p q : Fin n}
    (h : Balanced M p q) : (p, q) ∈ balancedTable M := by
  exact balanced_least (R := fun p q => (p, q) ∈ balancedTable M)
    (balancedTable_closed M) h

theorem mem_balancedTable (M : System n) (p q : Fin n) :
    (p, q) ∈ balancedTable M ↔ Balanced M p q := by
  constructor
  · exact balancedTable_sound M
  · intro h
    exact balancedTable_complete M h

def balancedCheck (M : System n) (p q : Fin n) : Bool :=
  decide ((p, q) ∈ balancedTable M)

@[simp] theorem balancedCheck_correct (M : System n) (p q : Fin n) :
    balancedCheck M p q = true ↔ Balanced M p q := by
  simp [balancedCheck, mem_balancedTable]

theorem balancedCheck_eq_reference (M : System n) (p q : Fin n) :
    balancedCheck M p q = StackSummary.balancedCheck M p q := by
  apply Bool.eq_iff_iff.mpr
  rw [balancedCheck_correct, StackSummary.balancedCheck_correct]

end StackSummaryFast
end Subtail
