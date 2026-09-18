import Subtail.Basic

/-!
Finite, executable least-closure tables for push/pop/epsilon systems.
The first implementation enumerates all finite closed tables. This is deliberately
not an efficient saturation engine; its termination requires no stack bound.
Classical reasoning occurs only in completeness proofs, never in definitions.
-/
namespace Subtail
namespace StackSummary

structure System (n : Nat) where
  eps : Fin n -> Fin n -> Bool
  push : Bool -> Fin n -> Fin n -> Bool
  pop : Bool -> Fin n -> Fin n -> Bool

def reverse (M : System n) : System n where
  eps p q := M.eps q p
  push a p q := M.pop a q p
  pop a p q := M.push a q p

@[simp] theorem reverse_reverse (M : System n) : reverse (reverse M) = M := by
  cases M
  rfl

/-- Balanced excursions, never reading below their starting stack. -/
inductive Balanced (M : System n) : Fin n -> Fin n -> Prop where
  | refl (p) : Balanced M p p
  | eps {p q} : M.eps p q = true -> Balanced M p q
  | trans {p q r} : Balanced M p q -> Balanced M q r -> Balanced M p r
  | wrap {a p q r s} : M.push a p q = true -> Balanced M q r ->
      M.pop a r s = true -> Balanced M p s

theorem balanced_reverse {M : System n} {p q} (h : Balanced M p q) :
    Balanced (reverse M) q p := by
  induction h with
  | refl p => exact .refl p
  | eps h => exact .eps h
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1
  | wrap h1 _ h2 ih => exact .wrap h2 ih h1

@[simp] theorem balanced_reverse_iff (M : System n) (p q) :
    Balanced (reverse M) p q ↔ Balanced M q p := by
  constructor
  · intro h
    simpa using balanced_reverse h
  · exact balanced_reverse

/-- An explicit finite powerset enumeration (duplicates do not affect correctness). -/
def subsets {a : Type} : List a -> List (List a)
  | [] => [[]]
  | x :: xs => subsets xs ++ (subsets xs).map (fun ys => x :: ys)

theorem filter_mem_subsets {a : Type} (f : a -> Bool) (xs : List a) :
    xs.filter f ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih =>
    cases hf : f x <;> simp [subsets, hf, ih]

def pairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun p => (List.finRange n).map fun q => (p,q)

@[simp] theorem mem_pairs (p q : Fin n) : (p,q) ∈ pairs n := by
  simp [pairs]

/-- The four finite Horn closure requirements. -/
def Closed (M : System n) (R : Fin n -> Fin n -> Prop) : Prop :=
  (∀ p, R p p) ∧
  (∀ p q, M.eps p q = true -> R p q) ∧
  (∀ p q r, R p q -> R q r -> R p r) ∧
  (∀ a p q r s, M.push a p q = true -> R q r -> M.pop a r s = true -> R p s)

theorem balanced_closed (M : System n) : Closed M (Balanced M) :=
  ⟨Balanced.refl, fun _ _ => Balanced.eps,
    fun _ _ _ => Balanced.trans, fun _ _ _ _ _ => Balanced.wrap⟩

theorem balanced_least {M : System n} {R : Fin n -> Fin n -> Prop}
    (hc : Closed M R) {p q} (h : Balanced M p q) : R p q := by
  induction h with
  | refl p => exact hc.1 p
  | eps h => exact hc.2.1 _ _ h
  | trans _ _ ih1 ih2 => exact hc.2.2.1 _ _ _ ih1 ih2
  | wrap h1 _ h2 ih => exact hc.2.2.2 _ _ _ _ _ h1 ih h2

def closedCheck (M : System n) (R : List (Fin n × Fin n)) : Bool :=
  decide ((∀ p, (p,p) ∈ R) ∧
    (∀ p q, M.eps p q = true -> (p,q) ∈ R) ∧
    (∀ p q r, (p,q) ∈ R -> (q,r) ∈ R -> (p,r) ∈ R) ∧
    (∀ p q r s, M.push false p q = true -> (q,r) ∈ R -> M.pop false r s = true -> (p,s) ∈ R) ∧
    (∀ p q r s, M.push true p q = true -> (q,r) ∈ R -> M.pop true r s = true -> (p,s) ∈ R))

@[simp] theorem closedCheck_correct (M : System n) (R : List (Fin n × Fin n)) :
    closedCheck M R = true ↔ Closed M (fun p q => (p,q) ∈ R) := by
  simp only [closedCheck,decide_eq_true_eq,Closed]
  constructor
  · rintro ⟨hr,he,ht,h0,h1⟩
    refine ⟨hr,he,ht,?_⟩
    intro a
    cases a
    · exact h0
    · exact h1
  · rintro ⟨hr,he,ht,hw⟩
    exact ⟨hr,he,ht,hw false,hw true⟩

/-- Intersection of all finite closed tables; not a classical choice of a table. -/
def balancedCheck (M : System n) (p q : Fin n) : Bool :=
  (subsets (pairs n)).all fun R =>
    if closedCheck M R then decide ((p,q) ∈ R) else true

@[simp] theorem balancedCheck_correct (M : System n) (p q : Fin n) :
    balancedCheck M p q = true ↔ Balanced M p q := by
  constructor
  · intro h
    classical
    let R := (pairs n).filter fun x => decide (Balanced M x.1 x.2)
    have hm : ∀ a b, (a,b) ∈ R ↔ Balanced M a b := by
      intro a b
      simp [R]
    have hc : Closed M (fun a b => (a,b) ∈ R) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a; exact (hm a a).mpr (.refl a)
      · intro a b he; exact (hm a b).mpr (.eps he)
      · intro a b c hab hbc
        exact (hm a c).mpr (.trans ((hm a b).mp hab) ((hm b c).mp hbc))
      · intro a p q r s hp hb hq
        exact (hm p s).mpr (.wrap hp ((hm q r).mp hb) hq)
    have hin : R ∈ subsets (pairs n) := filter_mem_subsets _ _
    have ht := List.all_eq_true.mp h R hin
    have hct := (closedCheck_correct M R).mpr hc
    have hpq : (p,q) ∈ R := by simpa [hct] using ht
    exact (hm p q).mp hpq
  · intro h
    apply List.all_eq_true.mpr
    intro R _
    by_cases hc : closedCheck M R = true
    · have hm := balanced_least ((closedCheck_correct M R).mp hc) h
      simp [hc, hm]
    · have hf : closedCheck M R = false := by cases hh : closedCheck M R <;> simp_all
      simp [hf]

/-- Finite graph reachability, separate from unbounded stacks. -/
inductive Path (edge : Fin n -> Fin n -> Bool) (p : Fin n) : Fin n -> Prop where
  | refl : Path edge p p
  | step {q r} : Path edge p q -> edge q r = true -> Path edge p r

theorem path_trans {edge : Fin n -> Fin n -> Bool} {p q r}
    (h : Path edge p q) (g : Path edge q r) : Path edge p r := by
  induction g with
  | refl => exact h
  | step _ he ih => exact .step ih he

def invariantCheck (edge : Fin n -> Fin n -> Bool) (p : Fin n)
    (R : List (Fin n)) : Bool :=
  decide (p ∈ R ∧ ∀ q r, q ∈ R -> edge q r = true -> r ∈ R)

def pathCheck (edge : Fin n -> Fin n -> Bool) (p q : Fin n) : Bool :=
  (subsets (List.finRange n)).all fun R =>
    if invariantCheck edge p R then decide (q ∈ R) else true

@[simp] theorem pathCheck_correct (edge : Fin n -> Fin n -> Bool) (p q) :
    pathCheck edge p q = true ↔ Path edge p q := by
  constructor
  · intro h
    classical
    let R := (List.finRange n).filter fun r => decide (Path edge p r)
    have hm : ∀ r, r ∈ R ↔ Path edge p r := by intro r; simp [R]
    have hc : invariantCheck edge p R = true := by
      have hi : p ∈ R ∧ ∀ q r, q ∈ R -> edge q r = true -> r ∈ R := by
        refine ⟨(hm p).mpr .refl, ?_⟩
        intro q r hq he
        exact (hm r).mpr (.step ((hm q).mp hq) he)
      simpa [invariantCheck] using hi
    have hh := List.all_eq_true.mp h R (filter_mem_subsets _ _)
    have hq : q ∈ R := by simpa [hc] using hh
    exact (hm q).mp hq
  · intro h
    apply List.all_eq_true.mpr
    intro R _
    by_cases hc : invariantCheck edge p R = true
    · have hi : p ∈ R ∧ ∀ q r, q ∈ R -> edge q r = true -> r ∈ R := by
        simpa [invariantCheck] using hc
      have hq : q ∈ R := by
        induction h with
        | refl => exact hi.1
        | step _ he ih => exact hi.2 _ _ ih he
      simp [hc, hq]
    · have hf : invariantCheck edge p R = false := by
        cases hh : invariantCheck edge p R <;> simp_all
      simp [hf]

end StackSummary
end Subtail
