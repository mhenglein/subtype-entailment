import Subtail.Basic

/-!
# Arbitrary product-address trees and normalized subtype semantics

Specification predicates range over ALL binary addresses. No decidable-membership,
finite-tree, regular-language or supplied witness-bound assumption is present.
This is the semantic foundation of stage 6 (#31), not an executable decision.
-/
namespace Subtail
namespace TreeSemantics

/-- Closure under removing any finite suffix. -/
def PrefixClosed (X : Word → Prop) : Prop :=
  ∀ u v, X (u ++ v) → X u

/-- A possibly infinite tree, specified by its product-labelled addresses. -/
structure Tree where
  nodes : Word → Prop
  closed : PrefixClosed nodes

/-- Covariant subtype order. -/
def Below (X Y : Tree) : Prop := ∀ w, X.nodes w → Y.nodes w

def bottom : Tree := ⟨fun _ => False, by intro u v h; exact h⟩

def product (X Y : Tree) : Tree where
  nodes
    | [] => True
    | false :: w => X.nodes w
    | true :: w => Y.nodes w
  closed := by
    intro u v h
    cases u with
    | nil => trivial
    | cons a u =>
      cases a with
      | false => exact X.closed u v h
      | true => exact Y.closed u v h

@[simp] theorem product_root (X Y : Tree) : (product X Y).nodes [] := by trivial
@[simp] theorem product_left (X Y : Tree) (w : Word) :
    (product X Y).nodes (false :: w) ↔ X.nodes w := Iff.rfl
@[simp] theorem product_right (X Y : Tree) (w : Word) :
    (product X Y).nodes (true :: w) ↔ Y.nodes w := Iff.rfl

/-- Every nonroot address exists precisely when its parent is a product.
The root exists even when the product set is empty. -/
def domain (X : Tree) (w : Word) : Prop :=
  w = [] ∨ X.nodes (w.take (w.length - 1))

@[simp] theorem domain_root (X : Tree) : domain X [] := Or.inl rfl

theorem nodes_defined (X : Tree) {w : Word} (h : X.nodes w) : domain X w := by
  right
  apply X.closed (w.take (w.length - 1)) (w.drop (w.length - 1))
  simpa only [List.take_append_drop] using h

@[simp] theorem domain_child (X : Tree) (w : Word) (a : Bool) :
    domain X (w ++ [a]) ↔ X.nodes w := by
  simp [domain]

/-- A separate node-domain specification: nodes have either product or bottom
labels, root is present, and precisely products have both children. -/
structure TreeDiagram where
  defined : Word → Prop
  isProduct : Word → Prop
  root_defined : defined []
  product_defined : ∀ w, isProduct w → defined w
  children : ∀ w a, defined (w ++ [a]) ↔ isProduct w

def toDiagram (X : Tree) : TreeDiagram where
  defined := domain X
  isProduct := X.nodes
  root_defined := domain_root X
  product_defined := fun _ h => nodes_defined X h
  children := domain_child X

theorem diagram_products_closed (D : TreeDiagram) : PrefixClosed D.isProduct := by
  have aux : ∀ v u, D.isProduct (u ++ v) → D.isProduct u := by
    intro v
    induction v with
    | nil => intro u h; simpa only [List.append_nil] using h
    | cons a v ih =>
      intro u h
      have hc : D.isProduct ((u ++ [a]) ++ v) := by
        simpa only [List.append_assoc, List.singleton_append] using h
      exact (D.children u a).mp (D.product_defined _ (ih _ hc))
  intro u v h
  exact aux v u h

def ofDiagram (D : TreeDiagram) : Tree := ⟨D.isProduct, diagram_products_closed D⟩

/-- The domain is determined by the product set, so no missing bottom root
or additional disconnected nodes are hidden in the path-set representation. -/
theorem diagram_domain_exact (D : TreeDiagram) (w : Word) :
    D.defined w ↔ domain (ofDiagram D) w := by
  have aux : ∀ v : Word, D.defined v.reverse ↔ domain (ofDiagram D) v.reverse := by
    intro v
    cases v with
    | nil => simp [D.root_defined]
    | cons a v =>
      simpa only [List.reverse_cons] using
        (D.children v.reverse a).trans (domain_child (ofDiagram D) v.reverse a).symm
  simpa only [List.reverse_reverse] using aux w.reverse

theorem tree_roundtrip (X : Tree) : ofDiagram (toDiagram X) = X := by
  cases X
  rfl

theorem product_mono {X X' Y Y' : Tree} (hx : Below X X') (hy : Below Y Y') :
    Below (product X Y) (product X' Y') := by
  intro w hw
  cases w with
  | nil => trivial
  | cons a w => cases a with
    | false => exact hx w hw
    | true => exact hy w hw

/-- All four normalized clauses, with an explicit finite variable set. -/
inductive Constraint (n : Nat) where
  | leq (source target : Fin n)
  | upper (source left right : Fin n)
  | lower (left right target : Fin n)
  | denial (source : Fin n)
  deriving DecidableEq, Repr

abbrev Valuation (n : Nat) := Fin n → Tree

def Holds (rho : Valuation n) : Constraint n → Prop
  | .leq a b => Below (rho a) (rho b)
  | .upper a l r => Below (rho a) (product (rho l) (rho r))
  | .lower l r a => Below (product (rho l) (rho r)) (rho a)
  | .denial a => Below (rho a) bottom

def Models (C : List (Constraint n)) (rho : Valuation n) : Prop :=
  ∀ c ∈ C, Holds rho c

def Satisfiable (C : List (Constraint n)) : Prop := ∃ rho, Models C rho

def Entails (C : List (Constraint n)) (a b : Fin n) : Prop :=
  ∀ rho, Models C rho → Below (rho a) (rho b)

theorem unsatisfiable_entails (C : List (Constraint n)) (a b : Fin n)
    (h : ¬ Satisfiable C) : Entails C a b := by
  intro rho hm
  exact False.elim (h ⟨rho, hm⟩)

/-- Non-entailment has a FINITE address even when its models are infinite. -/
theorem not_entails_iff_separating (C : List (Constraint n)) (a b : Fin n) :
    ¬ Entails C a b ↔
      ∃ rho w, Models C rho ∧ (rho a).nodes w ∧ ¬ (rho b).nodes w := by
  classical
  constructor
  · intro h
    by_contra hn
    apply h
    intro rho hm w ha
    by_contra hb
    exact hn ⟨rho, w, hm, ha, hb⟩
  · rintro ⟨rho, w, hm, ha, hb⟩ he
    exact hb (he rho hm w ha)

/-- A concrete regular INFINITE tree, used only as a semantic regression. -/
def zeroSpine : Tree where
  nodes := fun w => ∀ b ∈ w, b = false
  closed := by
    intro u v h b hb
    exact h b (by simp [hb])

theorem zeroSpine_lower : Below (product zeroSpine bottom) zeroSpine := by
  intro w h
  cases w with
  | nil => simp [zeroSpine]
  | cons a w =>
    cases a with
    | false => simpa [zeroSpine] using h
    | true => exact False.elim h

theorem zeroSpine_unbounded (N : Nat) :
    ∃ w, zeroSpine.nodes w ∧ N < w.length := by
  refine ⟨List.replicate (N + 1) false, ?_, ?_⟩
  · intro b hb
    simpa using (List.mem_replicate.mp hb).2
  · simp

end TreeSemantics
end Subtail
