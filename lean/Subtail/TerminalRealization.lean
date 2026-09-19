import Subtail.TreeSemantics

/-!
C030 direct terminal-final realization. The proof uses only Basic and
TreeSemantics: no forward summary bridge or pushdown saturation theorem.
See notes/2026-09-19-c030-independent-review.md for the ordinary proof.
-/
namespace Subtail
namespace TerminalRealization
open TreeSemantics

/-- The sole additional automaton hypothesis. -/
def TerminalFinal (I : Instance k) : Prop :=
  ∀ q, I.final.get q = true → ∀ c, step I q c = none

def a (q : Fin k) : Fin (2 * k + 1) :=
  ⟨q.val, by have := q.isLt; omega⟩
def v (q : Fin k) : Fin (2 * k + 1) :=
  ⟨k + q.val, by have := q.isLt; omega⟩
def b (k : Nat) : Fin (2 * k + 1) := ⟨2 * k, by omega⟩

def child (f : Fin k → Fin (2 * k + 1)) : Option (Fin k) → Fin (2 * k + 1)
  | none => b k
  | some q => f q

def upperClause (I : Instance k) (q : Fin k) : Constraint (2 * k + 1) :=
  .upper (a q) (child a (step I q false)) (child a (step I q true))
def lowerClause (I : Instance k) (q : Fin k) : Constraint (2 * k + 1) :=
  .lower (child v (step I q false)) (child v (step I q true)) (v q)

/-- Exactly the C030 clauses, grouped by source state. -/
def constraints (I : Instance k) : List (Constraint (2 * k + 1)) :=
  [.denial (b k)] ++ (List.finRange k).flatMap (fun q =>
    [upperClause I q] ++
    (if I.final.get q then [] else [lowerClause I q]) ++
    (List.finRange k).flatMap (fun r =>
      if (I.flags.get q).get r then [.leq (a q) (v r)] else []) ++
    (if I.bad.get q then [.denial (a q)] else []))

/-- An unpacking of the normalized list, not a changed semantics. -/
def Laws (I : Instance k) (rho : Valuation (2 * k + 1)) : Prop :=
  Holds rho (.denial (b k)) ∧ ∀ q,
    Holds rho (upperClause I q) ∧
    (I.final.get q = false → Holds rho (lowerClause I q)) ∧
    (∀ r, (I.flags.get q).get r = true → Holds rho (.leq (a q) (v r))) ∧
    (I.bad.get q = true → Holds rho (.denial (a q)))

theorem models_append (C D : List (Constraint n)) (rho : Valuation n) :
    Models (C ++ D) rho ↔ Models C rho ∧ Models D rho := by
  simp only [Models, List.mem_append, or_imp, forall_and]

theorem models_singleton (c : Constraint n) (rho : Valuation n) :
    Models [c] rho ↔ Holds rho c := by simp [Models]

theorem models_fin_flat (f : Fin k → List (Constraint n)) (rho : Valuation n) :
    Models ((List.finRange k).flatMap f) rho ↔ ∀ q, Models (f q) rho := by
  constructor
  · intro h q c hc
    exact h c (List.mem_flatMap.mpr ⟨q, by simp, hc⟩)
  · intro h c hc
    rcases List.mem_flatMap.mp hc with ⟨q, _, hq⟩
    exact h q c hq

theorem models_if_true (t : Bool) (c : Constraint n) (rho : Valuation n) :
    Models (if t then [c] else []) rho ↔ (t = true → Holds rho c) := by
  cases t <;> simp [Models]

theorem models_if_false (t : Bool) (c : Constraint n) (rho : Valuation n) :
    Models (if t then [] else [c]) rho ↔ (t = false → Holds rho c) := by
  cases t <;> simp [Models]

theorem models_iff_laws (I : Instance k) (rho : Valuation (2 * k + 1)) :
    Models (constraints I) rho ↔ Laws I rho := by
  simp only [constraints, models_append, models_singleton, models_fin_flat,
    models_if_true, models_if_false, Laws]

theorem split_run (I : Instance k) {q r : Fin k} {u t : Word}
    (h : runFrom I q (u ++ t) = some r) :
    ∃ p, runFrom I q u = some p ∧ runFrom I p t = some r := by
  rw [runFrom_append] at h
  cases hp : runFrom I q u with
  | none => simp [hp] at h
  | some p => exact ⟨p, hp, by simpa [hp] using h⟩

theorem nonfinal_of_nonempty_run (I : Instance k) (ht : TerminalFinal I)
    {q r : Fin k} {u : Word} (hne : u ≠ [])
    (h : runFrom I q u = some r) : I.final.get q = false := by
  cases hf : I.final.get q with
  | false => rfl
  | true =>
    cases u with
    | nil => exact False.elim (hne rfl)
    | cons c u => simp [runFrom, ht q hf c] at h

theorem b_empty {I : Instance k} {rho : Valuation (2 * k + 1)}
    (h : Laws I rho) (u : Word) : ¬ (rho (b k)).nodes u := by
  intro hu
  exact h.1 u hu

theorem upper_letter {I : Instance k} {rho : Valuation (2 * k + 1)}
    (h : Laws I rho) (q : Fin k) (c : Bool) (u : Word)
    (hu : (rho (a q)).nodes (c :: u)) :
    (rho (child a (step I q c))).nodes u := by
  have hx := (h.2 q).1 (c :: u) hu
  cases c <;> exact hx

theorem lower_letter {I : Instance k} {rho : Valuation (2 * k + 1)}
    (h : Laws I rho) (q : Fin k) (hq : I.final.get q = false)
    (c : Bool) (u : Word) (hu : (rho (child v (step I q c))).nodes u) :
    (rho (v q)).nodes (c :: u) := by
  apply (h.2 q).2.1 hq (c :: u)
  cases c <;> exact hu

theorem upper_run {I : Instance k} {rho : Valuation (2 * k + 1)}
    (h : Laws I rho) (q : Fin k) (u t : Word)
    (hu : (rho (a q)).nodes (u ++ t)) :
    ∃ r, runFrom I q u = some r ∧ (rho (a r)).nodes t := by
  induction u generalizing q with
  | nil => exact ⟨q, rfl, hu⟩
  | cons c u ih =>
    have hx := upper_letter h q c (u ++ t) hu
    cases hs : step I q c with
    | none =>
      have hb : (rho (b k)).nodes (u ++ t) := by simpa [child, hs] using hx
      exact False.elim (b_empty h _ hb)
    | some p =>
      have hp : (rho (a p)).nodes (u ++ t) := by simpa [child, hs] using hx
      rcases ih p hp with ⟨r, hr, hm⟩
      exact ⟨r, by simp [runFrom, hs, hr], hm⟩

theorem lower_run {I : Instance k} {rho : Valuation (2 * k + 1)}
    (ht : TerminalFinal I) (h : Laws I rho) (q r : Fin k) (u t : Word)
    (hr : runFrom I q u = some r) (hm : (rho (v r)).nodes t) :
    (rho (v q)).nodes (u ++ t) := by
  induction u generalizing q with
  | nil =>
    have he : q = r := by simpa [runFrom] using hr
    simpa [he] using hm
  | cons c u ih =>
    have hq := nonfinal_of_nonempty_run I ht (by simp) hr
    cases hs : step I q c with
    | none => simp [runFrom, hs] at hr
    | some p =>
      have hp : runFrom I p u = some r := by simpa [runFrom, hs] using hr
      have hx := ih p hp
      apply lower_letter h q hq c (u ++ t)
      simpa [child, hs] using hx

/-- Any separating model satisfies every original word check, including cut 0. -/
theorem separation_implies_witness (I : Instance k) (ht : TerminalFinal I)
    (rho : Valuation (2 * k + 1)) (hm : Models (constraints I) rho)
    (w : Word) (ha : (rho (a I.initial)).nodes w)
    (hv : ¬ (rho (v I.initial)).nodes w) : Witness I w := by
  have h := (models_iff_laws I rho).mp hm
  have atCut : ∀ i, ∃ q, stateAt I w i = some q ∧
      (rho (a q)).nodes (w.drop i) := by
    intro i
    rcases upper_run h I.initial (w.take i) (w.drop i)
      (by simpa only [List.take_append_drop] using ha) with ⟨q, hq, hmem⟩
    exact ⟨q, hq, hmem⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases atCut i with ⟨q, hq, hmem⟩
    have hb : I.bad.get q = false := by
      cases hb : I.bad.get q with
      | false => rfl
      | true => exact False.elim ((h.2 q).2.2.2 hb _ hmem)
    simp [safeCheck, hq, hb]
  · rcases atCut w.length with ⟨q, hq, _⟩
    have hr : runFrom I I.initial w = some q := by simpa [stateAt] using hq
    have hf : I.final.get q = true := by
      cases hf : I.final.get q with
      | true => rfl
      | false =>
        have hroot : (rho (v q)).nodes [] :=
          (h.2 q).2.1 hf [] (product_root _ _)
        have hx := lower_run ht h I.initial q w [] hr hroot
        exact False.elim (hv (by simpa using hx))
    simp [finalCheck, hq, hf]
  · intro j hj i hi hag
    rcases atCut i with ⟨p, hp, hpa⟩
    rcases atCut j with ⟨q, hq, _⟩
    have hf : (I.flags.get p).get q = false := by
      cases hf : (I.flags.get p).get q with
      | false => rfl
      | true =>
        rcases hag with ⟨z, hz⟩
        have hy : (rho (a p)).nodes (w.drop j) :=
          (rho (a p)).closed (w.drop j) z (by simpa only [hz] using hpa)
        have hvy := (h.2 p).2.2.1 q hf (w.drop j) hy
        have hx := lower_run ht h I.initial q (w.take j) (w.drop j) hq hvy
        exact False.elim (hv (by simpa only [List.take_append_drop] using hx))
    simp [unflaggedCheck, hp, hq, hf]

/-- Forced lower-copy nodes: defined paths ending at a nonaccepting control. -/
def baseNodes (I : Instance k) (q : Fin k) (u : Word) : Prop :=
  ∃ r, runFrom I q u = some r ∧ I.final.get r = false

theorem base_closed (I : Instance k) (ht : TerminalFinal I) (q : Fin k) :
    PrefixClosed (baseNodes I q) := by
  intro u t
  rintro ⟨r, hr, hf⟩
  rcases split_run I hr with ⟨p, hp, hpr⟩
  refine ⟨p, hp, ?_⟩
  cases t with
  | nil =>
    have he : p = r := by simpa [runFrom] using hpr
    simpa [he] using hf
  | cons c t => exact nonfinal_of_nonempty_run I ht (by simp) hpr

def baseTree (I : Instance k) (ht : TerminalFinal I) (q : Fin k) : Tree :=
  ⟨baseNodes I q, base_closed I ht q⟩

/-- Place two arbitrary tree families on the disjoint indexed copies; b is bottom. -/
def valuation (A V : Fin k → Tree) (x : Fin (2 * k + 1)) : Tree :=
  if h : x.val < k then A ⟨x.val, h⟩
  else if h : x.val < 2 * k then V ⟨x.val - k, by omega⟩
  else bottom

@[simp] theorem valuation_a (A V : Fin k → Tree) (q : Fin k) :
    valuation A V (a q) = A q := by simp [valuation, a, q.isLt]
@[simp] theorem valuation_v (A V : Fin k → Tree) (q : Fin k) :
    valuation A V (v q) = V q := by
  have h1 : ¬ k + q.val < k := by omega
  have h2 : k + q.val < 2 * k := by have := q.isLt; omega
  simp [valuation, v, h1, h2]
@[simp] theorem valuation_b (A V : Fin k → Tree) :
    valuation A V (b k) = bottom := by
  have h : ¬ 2 * k < k := by omega
  simp [valuation, b, h]

/-- A concrete model exists even when the lower trees are necessarily infinite. -/
theorem baseline_models (I : Instance k) (ht : TerminalFinal I) :
    Models (constraints I) (valuation (fun _ => bottom) (baseTree I ht)) := by
  apply (models_iff_laws I _).mpr
  constructor
  · simp [Holds, valuation_b, Below, bottom]
  · intro q
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Holds, upperClause, valuation_a, Below, bottom]
    · intro hq
      change Below (product _ _) (valuation (fun _ => bottom) (baseTree I ht) (v q))
      rw [valuation_v]
      intro u hu
      change baseNodes I q u
      cases u with
      | nil => exact ⟨q, rfl, hq⟩
      | cons c u =>
        have hc : (valuation (fun _ => bottom) (baseTree I ht)
            (child v (step I q c))).nodes u := by
          cases c <;> exact hu
        cases hs : step I q c with
        | none => simpa [child, hs, bottom] using hc
        | some p =>
          have hp : baseNodes I p u := by simpa [child, hs, baseTree] using hc
          rcases hp with ⟨r, hr, hf⟩
          exact ⟨r, by simp [runFrom, hs, hr], hf⟩
    · intro r hflag
      simp [Holds, valuation_a, Below, bottom]
    · intro hbad
      simp [Holds, valuation_a, Below, bottom]

theorem realization_satisfiable (I : Instance k) (ht : TerminalFinal I) :
    Satisfiable (constraints I) :=
  ⟨valuation (fun _ => bottom) (baseTree I ht), baseline_models I ht⟩

end TerminalRealization
end Subtail
