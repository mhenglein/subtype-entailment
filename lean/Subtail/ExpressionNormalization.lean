import Subtail.TreeSemantics

/-!
Finite syntax only; valuations retain the existing arbitrary-tree semantics.
A product-occurrence table allocates one slot per occurrence. References to an
identical subexpression use its first slot; every duplicate slot is still
constrained. Bottom has exactly one slot when used, and none otherwise.
-/
namespace Subtail.ExpressionNormalization
open TreeSemantics

inductive Expr (n : Nat) where
  | var (x : Fin n)
  | bot
  | prod (left right : Expr n)
  deriving DecidableEq, Repr

abbrev Input (n : Nat) := List (Expr n × Expr n)

def eval (rho : Valuation n) : Expr n → Tree
  | .var x => rho x
  | .bot => bottom
  | .prod l r => product (eval rho l) (eval rho r)

def ExprModels (G : Input n) (rho : Valuation n) : Prop :=
  ∀ c ∈ G, Below (eval rho c.1) (eval rho c.2)

def ExprEntails (G : Input n) (s t : Expr n) : Prop :=
  ∀ rho, ExprModels G rho → Below (eval rho s) (eval rho t)

def Expr.pairs : Expr n → List (Expr n × Expr n)
  | .var _ => []
  | .bot => []
  | .prod l r => (l,r) :: (l.pairs ++ r.pairs)

def Expr.hasBot : Expr n → Bool
  | .var _ => false
  | .bot => true
  | .prod l r => l.hasBot || r.hasBot

def Supports (b : Bool) (ps : List (Expr n × Expr n)) : Expr n → Prop
  | .var _ => True
  | .bot => b = true
  | .prod l r => (l,r) ∈ ps ∧ Supports b ps l ∧ Supports b ps r

theorem supports_mono {b b' : Bool} {ps ps' : List (Expr n × Expr n)}
    (hp : ∀ p ∈ ps, p ∈ ps') (hb : b = true → b' = true)
    (e : Expr n) : Supports b ps e → Supports b' ps' e := by
  induction e with
  | var x => intro _; trivial
  | bot => exact hb
  | prod l r il ir =>
    intro h
    exact ⟨hp _ h.1, il h.2.1, ir h.2.2⟩

theorem supports_self (e : Expr n) : Supports e.hasBot e.pairs e := by
  induction e with
  | var x => trivial
  | bot => rfl
  | prod l r il ir =>
    refine ⟨by simp [Expr.pairs], ?_, ?_⟩
    · exact supports_mono (by intro p h; simp [Expr.pairs, h])
        (by intro h; simp [Expr.hasBot, h]) l il
    · exact supports_mono (by intro p h; simp [Expr.pairs, h])
        (by intro h; simp [Expr.hasBot, h]) r ir

theorem supports_forest (F : List (Expr n)) {e : Expr n} (he : e ∈ F) :
    Supports (F.any Expr.hasBot) (F.flatMap Expr.pairs) e := by
  apply supports_mono _ _ e (supports_self e)
  · intro p hp
    exact List.mem_flatMap.mpr ⟨e, he, hp⟩
  · intro hb
    exact List.any_eq_true.mpr ⟨e, he, hb⟩

theorem supports_children {b : Bool} {ps : List (Expr n × Expr n)}
    (e : Expr n) (h : Supports b ps e) {p : Expr n × Expr n}
    (hp : p ∈ e.pairs) : Supports b ps p.1 ∧ Supports b ps p.2 := by
  induction e with
  | var x => simp [Expr.pairs] at hp
  | bot => simp [Expr.pairs] at hp
  | prod l r il ir =>
    rcases List.mem_cons.mp hp with he | hp
    · subst p; exact h.2
    · rcases List.mem_append.mp hp with hp | hp
      · exact il h.2.1 hp
      · exact ir h.2.2 hp

theorem supported_size_pos {b : Bool} {ps : List (Expr n × Expr n)}
    (e : Expr n) (h : Supports b ps e) : 0 < n + (b.toNat + ps.length) := by
  cases e with
  | var x => have hx := x.isLt; omega
  | bot =>
    have hb : b = true := h
    simp only [hb, Bool.toNat_true]
    omega
  | prod l r =>
    have hp := h.1
    cases ps with
    | nil => simp at hp
    | cons p ps => simp; omega

/-- Effective lookup with a membership proof, not classical selection. -/
def locate [DecidableEq α] : (xs : List α) → (a : α) → a ∈ xs → Fin xs.length
  | [], _, h => False.elim (List.not_mem_nil h)
  | x :: xs, a, h =>
    if he : a = x then ⟨0, by simp⟩
    else (locate xs a ((List.mem_cons.mp h).resolve_left he)).succ

theorem get_locate [DecidableEq α] (xs : List α) (a : α) (h : a ∈ xs) :
    xs.get (locate xs a h) = a := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    by_cases he : a = x
    · subst a; simp [locate]
    · simpa [locate, he] using ih ((List.mem_cons.mp h).resolve_left he)

structure Naming (n : Nat) where
  botUsed : Bool
  pairs : List (Expr n × Expr n)
  positive : 0 < n + (botUsed.toNat + pairs.length)

def Naming.extra (R : Naming n) := R.botUsed.toNat + R.pairs.length
def Naming.total (R : Naming n) := n + R.extra

def Naming.old (R : Naming n) (x : Fin n) : Fin R.total :=
  ⟨x.val, by have := x.isLt; dsimp [Naming.total]; omega⟩

def Naming.slot (R : Naming n) (j : Fin R.pairs.length) : Fin R.total :=
  ⟨n + R.botUsed.toNat + j.val, by
    have := j.isLt; dsimp [Naming.total, Naming.extra]; omega⟩

def Naming.botIndex (R : Naming n) : Fin R.total :=
  if hb : R.botUsed = true then
    ⟨n, by simp only [Naming.total, Naming.extra, hb, Bool.toNat_true]; omega⟩
  else ⟨0, R.positive⟩

def Naming.ref (R : Naming n) : Expr n → Fin R.total
  | .var x => R.old x
  | .bot => R.botIndex
  | .prod l r =>
    if h : (l,r) ∈ R.pairs then R.slot (locate R.pairs (l,r) h)
    else ⟨0, R.positive⟩

def Naming.upper (R : Naming n) (j : Fin R.pairs.length) : Constraint R.total :=
  .upper (R.slot j) (R.ref (R.pairs.get j).1) (R.ref (R.pairs.get j).2)

def Naming.lower (R : Naming n) (j : Fin R.pairs.length) : Constraint R.total :=
  .lower (R.ref (R.pairs.get j).1) (R.ref (R.pairs.get j).2) (R.slot j)

def Naming.definitions (R : Naming n) : List (Constraint R.total) :=
  (if R.botUsed then [.denial R.botIndex] else []) ++
  (List.finRange R.pairs.length).flatMap (fun j => [R.upper j, R.lower j])

def Naming.restrict (R : Naming n) (eta : Valuation R.total) : Valuation n :=
  fun x => eta (R.old x)

def Naming.extend (R : Naming n) (rho : Valuation n) : Valuation R.total :=
  fun i =>
    if h : i.val < n then rho ⟨i.val,h⟩
    else if hb : i.val < n + R.botUsed.toNat then bottom
    else
      let j : Fin R.pairs.length := ⟨i.val - (n + R.botUsed.toNat), by
        have := i.isLt; dsimp [Naming.total, Naming.extra] at this; omega⟩
      eval rho (.prod (R.pairs.get j).1 (R.pairs.get j).2)

theorem extend_old (R : Naming n) (rho : Valuation n) (x : Fin n) :
    R.extend rho (R.old x) = rho x := by
  simp [Naming.extend, Naming.old, x.isLt]

theorem restrict_extend (R : Naming n) (rho : Valuation n) :
    R.restrict (R.extend rho) = rho := by
  funext x; exact extend_old R rho x

theorem extend_bottom (R : Naming n) (rho : Valuation n) (hb : R.botUsed = true) :
    R.extend rho R.botIndex = bottom := by
  simp [Naming.extend, Naming.botIndex, hb]

theorem extend_slot (R : Naming n) (rho : Valuation n) (j : Fin R.pairs.length) :
    R.extend rho (R.slot j) = eval rho (.prod (R.pairs.get j).1 (R.pairs.get j).2) := by
  simp [Naming.extend, Naming.slot, Nat.not_lt.mpr (show n ≤ n + R.botUsed.toNat + j.val by omega),
    Nat.not_lt.mpr (show n + R.botUsed.toNat ≤ n + R.botUsed.toNat + j.val by omega)]

theorem extend_ref (R : Naming n) (rho : Valuation n) (e : Expr n)
    (h : Supports R.botUsed R.pairs e) : R.extend rho (R.ref e) = eval rho e := by
  cases e with
  | var x => exact extend_old R rho x
  | bot => exact extend_bottom R rho h
  | prod l r =>
    simp only [Naming.ref, dif_pos h.1]
    rw [extend_slot, get_locate]

theorem denial_mem (R : Naming n) (hb : R.botUsed = true) :
    Constraint.denial R.botIndex ∈ R.definitions := by
  simp [Naming.definitions, hb]

theorem upper_mem (R : Naming n) (j : Fin R.pairs.length) :
    R.upper j ∈ R.definitions := by
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨j, by simp, by simp⟩

theorem lower_mem (R : Naming n) (j : Fin R.pairs.length) :
    R.lower j ∈ R.definitions := by
  apply List.mem_append.mpr
  right
  exact List.mem_flatMap.mpr ⟨j, by simp, by simp⟩

theorem tree_eq_of_below {X Y : Tree} (h : Below X Y) (g : Below Y X) : X = Y := by
  have hn : X.nodes = Y.nodes := funext (fun w => propext ⟨h w, g w⟩)
  cases X; cases Y; cases hn; rfl

theorem models_bottom (R : Naming n) (eta : Valuation R.total)
    (hm : Models R.definitions eta) (hb : R.botUsed = true) : eta R.botIndex = bottom := by
  apply tree_eq_of_below (hm _ (denial_mem R hb))
  intro w hw; exact False.elim hw

theorem models_slot (R : Naming n) (eta : Valuation R.total)
    (hm : Models R.definitions eta) (j : Fin R.pairs.length) :
    eta (R.slot j) = product (eta (R.ref (R.pairs.get j).1)) (eta (R.ref (R.pairs.get j).2)) :=
  tree_eq_of_below (hm _ (upper_mem R j)) (hm _ (lower_mem R j))

/-- The invariant includes every supported subexpression, not only query roots. -/
theorem representative_correct (R : Naming n) (eta : Valuation R.total)
    (hm : Models R.definitions eta) (e : Expr n)
    (h : Supports R.botUsed R.pairs e) : eta (R.ref e) = eval (R.restrict eta) e := by
  induction e with
  | var x => rfl
  | bot => exact models_bottom R eta hm h
  | prod l r il ir =>
    simp only [Naming.ref, dif_pos h.1]
    rw [models_slot R eta hm, get_locate]
    change product (eta (R.ref l)) (eta (R.ref r)) =
      product (eval (R.restrict eta) l) (eval (R.restrict eta) r)
    rw [il h.2.1, ir h.2.2]

def Naming.Closed (R : Naming n) : Prop :=
  ∀ p ∈ R.pairs, Supports R.botUsed R.pairs p.1 ∧ Supports R.botUsed R.pairs p.2

theorem extend_definitions (R : Naming n) (hc : R.Closed) (rho : Valuation n) :
    Models R.definitions (R.extend rho) := by
  intro c h
  rcases List.mem_append.mp h with h | h
  · by_cases hb : R.botUsed = true
    · have he : c = .denial R.botIndex := by simpa [hb] using h
      subst c
      change Below (R.extend rho R.botIndex) bottom
      rw [extend_bottom R rho hb]
      exact fun _ h => h
    · simp [hb] at h
  · obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp h
    have hs := hc (R.pairs.get j) (List.get_mem _ _)
    have he := extend_slot R rho j
    have hl := extend_ref R rho _ hs.1
    have hr := extend_ref R rho _ hs.2
    rcases List.mem_cons.mp hj with hj | hj
    · subst c
      change Below (R.extend rho (R.slot j))
        (product (R.extend rho (R.ref (R.pairs.get j).1)) (R.extend rho (R.ref (R.pairs.get j).2)))
      rw [he, hl, hr]
      exact fun _ h => h
    · have hj : c = R.lower j := by simpa using hj
      subst c
      change Below
        (product (R.extend rho (R.ref (R.pairs.get j).1)) (R.extend rho (R.ref (R.pairs.get j).2)))
        (R.extend rho (R.slot j))
      rw [he, hl, hr]
      exact fun _ h => h

def forest (G : Input n) (s t : Expr n) : List (Expr n) :=
  s :: t :: G.flatMap (fun c => [c.1,c.2])

def naming (G : Input n) (s t : Expr n) : Naming n where
  botUsed := (forest G s t).any Expr.hasBot
  pairs := (forest G s t).flatMap Expr.pairs
  positive := supported_size_pos s (supports_forest (forest G s t) (by simp [forest]))

theorem naming_support (G : Input n) (s t : Expr n) (e : Expr n)
    (he : e ∈ forest G s t) : Supports (naming G s t).botUsed (naming G s t).pairs e :=
  supports_forest _ he

theorem naming_closed (G : Input n) (s t : Expr n) : (naming G s t).Closed := by
  intro p hp
  obtain ⟨e, he, hp⟩ := List.mem_flatMap.mp hp
  exact supports_children e (naming_support G s t e he) hp

theorem premise_mem_forest (G : Input n) (s t : Expr n) (c : Expr n × Expr n)
    (hc : c ∈ G) : c.1 ∈ forest G s t ∧ c.2 ∈ forest G s t := by
  constructor
  · simp only [forest, List.mem_cons]
    exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨c, hc, by simp⟩))
  · simp only [forest, List.mem_cons]
    exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨c, hc, by simp⟩))

def normalized (G : Input n) (s t : Expr n) : List (Constraint (naming G s t).total) :=
  let R := naming G s t
  R.definitions ++ G.map (fun c => .leq (R.ref c.1) (R.ref c.2))

theorem normalized_definitions (G : Input n) (s t : Expr n)
    (eta : Valuation (naming G s t).total) (hm : Models (normalized G s t) eta) :
    Models (naming G s t).definitions eta := by
  intro c hc
  exact hm c (List.mem_append.mpr (Or.inl hc))

theorem extend_models (G : Input n) (s t : Expr n) (rho : Valuation n)
    (hm : ExprModels G rho) : Models (normalized G s t) ((naming G s t).extend rho) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact extend_definitions _ (naming_closed G s t) rho c hc
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    have hf := premise_mem_forest G s t p hp
    change Below ((naming G s t).extend rho ((naming G s t).ref p.1))
      ((naming G s t).extend rho ((naming G s t).ref p.2))
    rw [extend_ref _ _ _ (naming_support G s t _ hf.1),
      extend_ref _ _ _ (naming_support G s t _ hf.2)]
    exact hm p hp

theorem restrict_models (G : Input n) (s t : Expr n)
    (eta : Valuation (naming G s t).total) (hm : Models (normalized G s t) eta) :
    ExprModels G ((naming G s t).restrict eta) := by
  intro p hp
  have hd := normalized_definitions G s t eta hm
  have hf := premise_mem_forest G s t p hp
  have h := hm (.leq ((naming G s t).ref p.1) ((naming G s t).ref p.2))
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩)))
  change Below (eta ((naming G s t).ref p.1)) (eta ((naming G s t).ref p.2)) at h
  rw [representative_correct _ _ hd _ (naming_support G s t _ hf.1),
    representative_correct _ _ hd _ (naming_support G s t _ hf.2)] at h
  exact h

theorem normalize_entails_iff (G : Input n) (s t : Expr n) :
    ExprEntails G s t ↔ Entails (normalized G s t) ((naming G s t).ref s) ((naming G s t).ref t) := by
  have hs := naming_support G s t s (by simp [forest])
  have ht := naming_support G s t t (by simp [forest])
  constructor
  · intro h eta hm
    have hd := normalized_definitions G s t eta hm
    rw [representative_correct _ _ hd _ hs, representative_correct _ _ hd _ ht]
    exact h _ (restrict_models G s t eta hm)
  · intro h rho hm
    have hh := h _ (extend_models G s t rho hm)
    rw [extend_ref _ _ _ hs, extend_ref _ _ _ ht] at hh
    exact hh

theorem normalize_satisfiable_iff (G : Input n) (s t : Expr n) :
    (∃ rho, ExprModels G rho) ↔ Satisfiable (normalized G s t) := by
  constructor
  · rintro ⟨rho, hm⟩
    exact ⟨_, extend_models G s t rho hm⟩
  · rintro ⟨eta, hm⟩
    exact ⟨_, restrict_models G s t eta hm⟩

theorem normalize_separating_iff (G : Input n) (s t : Expr n) (w : Word) :
    (∃ rho, ExprModels G rho ∧ (eval rho s).nodes w ∧ ¬ (eval rho t).nodes w) ↔
    ∃ eta, Models (normalized G s t) eta ∧
      (eta ((naming G s t).ref s)).nodes w ∧ ¬ (eta ((naming G s t).ref t)).nodes w := by
  have hs := naming_support G s t s (by simp [forest])
  have ht := naming_support G s t t (by simp [forest])
  constructor
  · rintro ⟨rho, hm, hl, hr⟩
    refine ⟨(naming G s t).extend rho, extend_models G s t rho hm, ?_, ?_⟩
    · simpa only [extend_ref _ _ _ hs] using hl
    · simpa only [extend_ref _ _ _ ht] using hr
  · rintro ⟨eta, hm, hl, hr⟩
    have hd := normalized_definitions G s t eta hm
    refine ⟨(naming G s t).restrict eta, restrict_models G s t eta hm, ?_, ?_⟩
    · simpa only [representative_correct _ _ hd _ hs] using hl
    · simpa only [representative_correct _ _ hd _ ht] using hr

theorem old_value (R : Naming n) (x : Fin n) : (R.old x).val = x.val := rfl

theorem variable_query_preserved (G : Input n) (a b : Fin n) :
    ((naming G (.var a) (.var b)).ref (.var a)).val = a.val ∧
    ((naming G (.var a) (.var b)).ref (.var b)).val = b.val := ⟨rfl,rfl⟩

end Subtail.ExpressionNormalization
