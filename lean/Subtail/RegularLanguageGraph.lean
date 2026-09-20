import Subtail.RegularTreeCertificate
import Subtail.StackSummary

/-!
Finite-language graph conversion for issue 68.  The state graph is the existing
C084 Graph, not a new tree semantics.  Only the selected root language must be
prefix-closed; unreachable automaton states have no extra hypothesis.

SOURCE DRAFT: pinned elaboration/kernel checks must be recorded independently.
-/
namespace Subtail.RegularLanguageGraph

open TreeSemantics RegularTreeCertificate StackSummary ExpressionNormalization

variable {v : Nat} {alpha : Type}

structure DFA (v : Nat) where
  next : Fin v -> Bool -> Fin v
  final : Fin v -> Bool

def accepts (D : DFA v) (q : Fin v) : Word -> Bool
  | [] => D.final q
  | a :: w => accepts D (D.next q a) w

def toGraph (D : DFA v) : Graph v where
  nodes := Vector.ofFn fun q =>
    if D.final q then some (D.next q false, D.next q true) else none

@[simp] theorem nodes_toGraph (D : DFA v) (q : Fin v) :
    (toGraph D).nodes.get q =
      (if D.final q then some (D.next q false, D.next q true) else none) := by
  change (Vector.ofFn _)[q.val] = _
  exact Vector.getElem_ofFn q.isLt

theorem derivative_closed (D : DFA v) (q : Fin v)
    (h : PrefixClosed (fun w => accepts D q w = true)) (a : Bool) :
    PrefixClosed (fun w => accepts D (D.next q a) w = true) := by
  intro u w hu
  have hu' : accepts D q ((a :: u) ++ w) = true := hu
  exact h (a :: u) w hu'

/-- Pruning rejection to bottom preserves every address at a prefix-closed root. -/
theorem graphNodes_iff (D : DFA v) (q : Fin v)
    (h : PrefixClosed (fun w => accepts D q w = true)) (w : Word) :
    graphNodes (toGraph D) q w = true <-> accepts D q w = true := by
  induction w generalizing q with
  | nil =>
      cases hf : D.final q <;> simp [graphNodes, accepts, hf]
  | cons a w ih =>
      cases hf : D.final q with
      | false =>
          have hn : ¬ accepts D q (a :: w) = true := by
            intro hw
            have hr : accepts D q [] = true := h [] (a :: w) hw
            simp [accepts, hf] at hr
          simp [graphNodes, hf, hn]
      | true =>
          have hi := ih (D.next q a) (derivative_closed D q h a)
          cases a <;> simpa [graphNodes, accepts, hf] using hi

/-! Explicit finite subset construction.  Repeated carrier entries are allowed. -/

structure NFA (alpha : Type) where
  carrier : List alpha
  next : alpha -> Bool -> alpha -> Bool
  final : alpha -> Bool

variable [DecidableEq alpha]

def subsetsOf (A : NFA alpha) : List (List alpha) := subsets A.carrier

def encode (A : NFA alpha) (s : List alpha) (h : s ∈ subsetsOf A) :
    Fin (subsetsOf A).length := locate (subsetsOf A) s h

def decode (A : NFA alpha) (q : Fin (subsetsOf A).length) : List alpha :=
  (subsetsOf A).get q

@[simp] theorem decode_encode (A : NFA alpha) (s : List alpha)
    (h : s ∈ subsetsOf A) : decode A (encode A s h) = s :=
  get_locate (subsetsOf A) s h

def nextSet (A : NFA alpha) (s : List alpha) (a : Bool) : List alpha :=
  A.carrier.filter fun q => s.any fun p => A.next p a q

def initialSet (A : NFA alpha) (p : alpha) : List alpha :=
  A.carrier.filter fun q => decide (q = p)

def initial (A : NFA alpha) (p : alpha) : Fin (subsetsOf A).length :=
  encode A (initialSet A p) (filter_mem_subsets _ _)

def determinize (A : NFA alpha) : DFA (subsetsOf A).length where
  next q a := encode A (nextSet A (decode A q) a) (filter_mem_subsets _ _)
  final q := (decode A q).any A.final

theorem member_of_subset {xs ys : List alpha} (h : ys ∈ subsets xs)
    {p : alpha} (hp : p ∈ ys) : p ∈ xs := by
  induction xs generalizing ys with
  | nil =>
      have he : ys = [] := by simpa [subsets] using h
      subst ys
      simp at hp
  | cons x xs ih =>
      rcases List.mem_append.mp h with h | h
      · exact List.mem_cons.mpr (Or.inr (ih h hp))
      · obtain ⟨zs, hzs, he⟩ := List.mem_map.mp h
        subst ys
        rcases List.mem_cons.mp hp with hp | hp
        · exact List.mem_cons.mpr (Or.inl hp)
        · exact List.mem_cons.mpr (Or.inr (ih hzs hp))

theorem decode_member (A : NFA alpha) (q : Fin (subsetsOf A).length)
    {p : alpha} (hp : p ∈ decode A q) : p ∈ A.carrier := by
  exact member_of_subset (List.get_mem (subsetsOf A) q) hp

@[simp] theorem mem_nextSet (A : NFA alpha) (s : List alpha)
    (a : Bool) (q : alpha) :
    q ∈ nextSet A s a <->
      q ∈ A.carrier ∧ ∃ p, p ∈ s ∧ A.next p a q = true := by
  simp [nextSet, List.any_eq_true]

/-- The finite NFA derivative law is enough; no unbounded path decision is assumed. -/
theorem accepts_iff (A : NFA alpha) (L : alpha -> Word -> Prop)
    (hfinal : ∀ p, p ∈ A.carrier -> (A.final p = true <-> L p []))
    (hnext : ∀ p, p ∈ A.carrier -> ∀ a w,
      L p (a :: w) <-> ∃ q, q ∈ A.carrier ∧
        A.next p a q = true ∧ L q w)
    (q : Fin (subsetsOf A).length) (w : Word) :
    accepts (determinize A) q w = true <->
      ∃ p, p ∈ decode A q ∧ L p w := by
  induction w generalizing q with
  | nil =>
      change (decode A q).any A.final = true <-> _
      constructor
      · intro h
        obtain ⟨p, hp, hf⟩ := List.any_eq_true.mp h
        exact ⟨p, hp, (hfinal p (decode_member A q hp)).mp hf⟩
      · rintro ⟨p, hp, hl⟩
        exact List.any_eq_true.mpr
          ⟨p, hp, (hfinal p (decode_member A q hp)).mpr hl⟩
  | cons a w ih =>
      have hd : decode A ((determinize A).next q a) = nextSet A (decode A q) a :=
        decode_encode A _ _
      rw [accepts, ih, hd]
      constructor
      · rintro ⟨r, hr, hl⟩
        obtain ⟨hrU, p, hp, ht⟩ := (mem_nextSet A (decode A q) a r).mp hr
        exact ⟨p, hp, (hnext p (decode_member A q hp) a w).mpr
          ⟨r, hrU, ht, hl⟩⟩
      · rintro ⟨p, hp, hl⟩
        obtain ⟨r, hrU, ht, hr⟩ :=
          (hnext p (decode_member A q hp) a w).mp hl
        exact ⟨r, (mem_nextSet A (decode A q) a r).mpr
          ⟨hrU, p, hp, ht⟩, hr⟩

theorem accepts_initial_iff (A : NFA alpha) (L : alpha -> Word -> Prop)
    (hfinal : ∀ p, p ∈ A.carrier -> (A.final p = true <-> L p []))
    (hnext : ∀ p, p ∈ A.carrier -> ∀ a w,
      L p (a :: w) <-> ∃ q, q ∈ A.carrier ∧
        A.next p a q = true ∧ L q w)
    (p : alpha) (hp : p ∈ A.carrier) (w : Word) :
    accepts (determinize A) (initial A p) w = true <-> L p w := by
  rw [accepts_iff A L hfinal hnext]
  simp [initial, initialSet, and_assoc, hp]

end Subtail.RegularLanguageGraph
