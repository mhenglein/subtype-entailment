import Std

/-!
# Critical all-word lifting theorem for explicit top (issue #71)

This module is independent of the existing bottom/product semantics.
Languages are arbitrary predicates on finite binary words: neither regularity
nor decidable membership is assumed. The accompanying ordinary proof identifies
paired prefix-closed covering languages with arity-consistent labelled trees,
and instantiates the final decomposition using finite naming and C081.
Those two identification/compiler steps are not claimed formalized here.
-/
namespace Subtail.ExplicitTopDualProjection

abbrev Word := List Bool
abbrev Languages (V : Type u) := V -> Word -> Prop

def PrefixClosed (L : Word -> Prop) : Prop :=
  forall u v, L (u ++ v) -> L u

def Included (L M : Word -> Prop) : Prop := forall w, L w -> M w

/-- A normalized system. Finite input is represented by the membership
relations of its four clause forms. The lifting result needs no finiteness. -/
structure System (V : Type u) where
  leq : V -> V -> Prop
  bot : V -> Prop
  top : V -> Prop
  prod : V -> V -> V -> Prop

def System.dual (S : System V) : System V where
  leq x y := S.leq y x
  bot := S.top
  top := S.bot
  prod := S.prod

@[simp] theorem System.dual_dual (S : System V) : S.dual.dual = S := by
  cases S
  rfl

/-- Positive top-free projection; named top constants denote the full
product-address language. In C081 this is forced by omega = omega * omega. -/
structure Model (S : System V) (P : Languages V) : Prop where
  closed : forall x, PrefixClosed (P x)
  leq : forall {x y}, S.leq x y -> Included (P x) (P y)
  bot : forall {x}, S.bot x -> forall w, Not (P x w)
  top : forall {x}, S.top x -> forall w, P x w
  prodRoot : forall {x l r}, S.prod x l r -> P x []
  prodLeft : forall {x l r}, S.prod x l r -> forall w,
    P x (false :: w) <-> P l w
  prodRight : forall {x l r}, S.prod x l r -> forall w,
    P x (true :: w) <-> P r w

def Cover (P Q : Languages V) : Prop := forall x w, Or (P x w) (Q x w)

def PairedModel (S : System V) (P Q : Languages V) : Prop :=
  And (Model S P) (And (Model S.dual Q) (Cover P Q))

/-- Least forced-top language. Every seed contains ALL right extensions.
Products have push and pop rules but NO unconditional root-top fact. -/
inductive ForcedTop (S : System V) : V -> Word -> Prop
  | seed {x} (hx : S.top x) (w : Word) : ForcedTop S x w
  | leq {x y w} (hxy : S.leq x y) (h : ForcedTop S x w) : ForcedTop S y w
  | push0 {x l r w} (hp : S.prod x l r) (h : ForcedTop S l w) :
      ForcedTop S x (false :: w)
  | pop0 {x l r w} (hp : S.prod x l r) (h : ForcedTop S x (false :: w)) :
      ForcedTop S l w
  | push1 {x l r w} (hp : S.prod x l r) (h : ForcedTop S r w) :
      ForcedTop S x (true :: w)
  | pop1 {x l r w} (hp : S.prod x l r) (h : ForcedTop S x (true :: w)) :
      ForcedTop S r w

/-- Stability under appending one shared suffix, with no bound on the
suffix or on the original derivation, including recurrent systems. -/
theorem forcedTop_suffix {S : System V} {x w} (h : ForcedTop S x w) (v : Word) :
    ForcedTop S x (w ++ v) := by
  induction h with
  | seed hx w => exact ForcedTop.seed hx (w ++ v)
  | leq hxy h ih => exact ForcedTop.leq hxy ih
  | push0 hp h ih => exact ForcedTop.push0 hp ih
  | pop0 hp h ih => exact ForcedTop.pop0 hp ih
  | push1 hp h ih => exact ForcedTop.push1 hp ih
  | pop1 hp h ih => exact ForcedTop.pop1 hp ih

theorem forcedTop_in_positive {S : System V} {P : Languages V}
    (M : Model S P) {x w} (h : ForcedTop S x w) : P x w := by
  induction h with
  | seed hx w => exact M.top hx w
  | leq hxy h ih => exact M.leq hxy _ ih
  | push0 hp h ih => exact (M.prodLeft hp _).mpr ih
  | pop0 hp h ih => exact (M.prodLeft hp _).mp ih
  | push1 hp h ih => exact (M.prodRight hp _).mpr ih
  | pop1 hp h ih => exact (M.prodRight hp _).mp ih

theorem forcedTop_disjoint_negative {S : System V} {Q : Languages V}
    (M : Model S.dual Q) {x w} (h : ForcedTop S x w) : Not (Q x w) := by
  induction h with
  | seed hx w => exact M.bot hx w
  | leq hxy h ih =>
      intro hq
      exact ih (M.leq hxy _ hq)
  | push0 hp h ih =>
      intro hq
      exact ih ((M.prodLeft hp _).mp hq)
  | pop0 hp h ih =>
      intro hq
      exact ih ((M.prodLeft hp _).mpr hq)
  | push1 hp h ih =>
      intro hq
      exact ih ((M.prodRight hp _).mp hq)
  | pop1 hp h ih =>
      intro hq
      exact ih ((M.prodRight hp _).mpr hq)

def Remaining (S : System V) : Languages V := fun x w => Not (ForcedTop S x w)

theorem remaining_closed (S : System V) (x : V) : PrefixClosed (Remaining S x) := by
  intro u v huv hu
  exact huv (forcedTop_suffix hu v)

/-- The negative witness is used only to exclude a top root at a product.
The constructed negative projection is not the independently supplied one. -/
theorem remaining_model {S : System V} {P Q : Languages V}
    (MP : Model S P) (MQ : Model S.dual Q) : Model S.dual (Remaining S) := by
  constructor
  case closed => exact remaining_closed S
  case leq =>
    intro x y hxy w hx hy
    exact hx (ForcedTop.leq hxy hy)
  case bot =>
    intro x hx w hw
    exact hw (ForcedTop.seed hx w)
  case top =>
    intro x hx w hw
    exact MP.bot hx w (forcedTop_in_positive MP hw)
  case prodRoot =>
    intro x l r hp hw
    exact forcedTop_disjoint_negative MQ hw (MQ.prodRoot hp)
  case prodLeft =>
    intro x l r hp w
    constructor
    · intro hx hl
      exact hx (ForcedTop.push0 hp hl)
    · intro hl hx
      exact hl (ForcedTop.pop0 hp hx)
  case prodRight =>
    intro x l r hp w
    constructor
    · intro hx hr
      exact hx (ForcedTop.push1 hp hr)
    · intro hr hx
      exact hr (ForcedTop.pop1 hp hx)

theorem positive_covered {S : System V} {P : Languages V} (MP : Model S P) :
    Cover P (Remaining S) := by
  classical
  intro x w
  by_cases ht : ForcedTop S x w
  · exact Or.inl (forcedTop_in_positive MP ht)
  · exact Or.inr ht

def PositiveSatisfiable (S : System V) : Prop := Exists (fun P => Model S P)
def Satisfiable (S : System V) : Prop := Exists (fun P => Exists (fun Q => PairedModel S P Q))

/-- Every positive projected valuation lifts, preserving all its words and
variables at once, provided the opposite projected system is satisfiable. -/
theorem positive_projection_surjective {S : System V} {P : Languages V}
    (MP : Model S P) (hN : PositiveSatisfiable S.dual) :
    Exists (fun Q => PairedModel S P Q) := by
  cases hN with
  | intro Q MQ =>
    exact Exists.intro (Remaining S)
      (And.intro MP (And.intro (remaining_model MP MQ) (positive_covered MP)))

theorem paired_dual_iff (S : System V) (P Q : Languages V) :
    PairedModel S.dual Q P <-> PairedModel S P Q := by
  unfold PairedModel
  rw [System.dual_dual]
  constructor
  · intro h
    exact And.intro h.2.1 (And.intro h.1 (fun x w => (h.2.2 x w).symm))
  · intro h
    exact And.intro h.2.1 (And.intro h.1 (fun x w => (h.2.2 x w).symm))

theorem negative_projection_surjective {S : System V} {Q : Languages V}
    (MQ : Model S.dual Q) (hP : PositiveSatisfiable S) :
    Exists (fun P => PairedModel S P Q) := by
  have hPP : PositiveSatisfiable S.dual.dual := by
    simpa only [System.dual_dual] using hP
  have hl := positive_projection_surjective MQ hPP
  cases hl with
  | intro P h => exact Exists.intro P ((paired_dual_iff S P Q).mp h)

theorem satisfiable_iff_projections (S : System V) :
    Satisfiable S <-> And (PositiveSatisfiable S) (PositiveSatisfiable S.dual) := by
  constructor
  · intro h
    cases h with
    | intro P h =>
      cases h with
      | intro Q h => exact And.intro (Exists.intro P h.1) (Exists.intro Q h.2.1)
  · intro h
    cases h.1 with
    | intro P MP =>
      exact Exists.intro P (positive_projection_surjective MP h.2)

def PositiveEntails (S : System V) (a b : V) : Prop :=
  forall P, Model S P -> Included (P a) (P b)

def Entails (S : System V) (a b : V) : Prop :=
  forall P Q, PairedModel S P Q -> And (Included (P a) (P b)) (Included (Q b) (Q a))

theorem entails_iff_of_satisfiable (S : System V) (a b : V)
    (hP : PositiveSatisfiable S) (hN : PositiveSatisfiable S.dual) :
    Entails S a b <-> And (PositiveEntails S a b) (PositiveEntails S.dual b a) := by
  constructor
  · intro he
    constructor
    · intro P MP
      have hl := positive_projection_surjective MP hN
      cases hl with
      | intro Q hm => exact (he P Q hm).1
    · intro Q MQ
      have hl := negative_projection_surjective MQ hP
      cases hl with
      | intro P hm => exact (he P Q hm).2
  · intro he P Q hm
    exact And.intro (he.1 P hm.1) (he.2 Q hm.2.1)

/-- Unconditional decomposition, including vacuous entailment. -/
theorem entails_iff_projections (S : System V) (a b : V) :
    Entails S a b <->
    Or (Not (PositiveSatisfiable S))
      (Or (Not (PositiveSatisfiable S.dual))
        (And (PositiveEntails S a b) (PositiveEntails S.dual b a))) := by
  classical
  constructor
  · intro he
    by_cases hP : PositiveSatisfiable S
    · by_cases hN : PositiveSatisfiable S.dual
      · exact Or.inr (Or.inr ((entails_iff_of_satisfiable S a b hP hN).mp he))
      · exact Or.inr (Or.inl hN)
    · exact Or.inl hP
  · intro h P Q hm
    cases h with
    | inl hp => exact False.elim (hp (Exists.intro P hm.1))
    | inr h =>
      cases h with
      | inl hq => exact False.elim (hq (Exists.intro Q hm.2.1))
      | inr he => exact And.intro (he.1 P hm.1) (he.2 Q hm.2.1)

/-- A failed projected comparison is preserved at the SAME supplied word. -/
theorem positive_countermodel_lift {S : System V} {P : Languages V}
    (MP : Model S P) (hN : PositiveSatisfiable S.dual) (a b : V) (w : Word)
    (ha : P a w) (hb : Not (P b w)) :
    Exists (fun Q => And (PairedModel S P Q) (And (P a w) (Not (P b w)))) := by
  cases positive_projection_surjective MP hN with
  | intro Q h => exact Exists.intro Q (And.intro h (And.intro ha hb))

end Subtail.ExplicitTopDualProjection
