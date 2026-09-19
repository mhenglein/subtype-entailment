import Subtail.RankQueryEnumeration

/-!
# Stage 4b: coverage of every safe first-return extension by a bounded diagram

For a safe base `B`, a safe first-return extension `C` and a clause `c` modelled by
the literal prefix graph of `C`, we build a bounded portal `Diagram` whose compiled
clause is modelled by the literal prefix graph of `B`.  This is the forward
direction of the Closure Lemma (`RankQueryEnumeration.DiagramCoverage`); the
reverse direction is `RankQuerySound.closure_reverse`.

Route: product-simple chains for every atom (`accepts_bounded_visits`),
segmentation of each chain into maximal old blocks and maximal physically
consecutive fresh blocks, global marks at block endpoints and fresh variable
positions, pieces read off the blocks, seam controls from the chains, and the
shared-interval product run assembled from the chains' controls.

No `sorry`, no custom axiom.
-/
namespace Subtail
namespace RankQueryCoverage
open TerminalRank RankMilestones RankQuery RankQueryCompiler RankQuerySound RankQueryEnumeration

variable {k : Nat}

/-! ## A first-return extension as a labelled trace over the base -/

/-- The labelled trace of an extension `C` of `B`: letters after `|B|` paired with the
label of the next position. -/
def traceOf (B C : Reference k) : List (Bool × Fin k) :=
  (List.range (C.word.length - B.word.length)).map fun i =>
    (C.word.getD (B.word.length + i) false, C.label (B.word.length + i + 1))

theorem traceOf_length (B C : Reference k) :
    (traceOf B C).length = C.word.length - B.word.length := by
  simp [traceOf]

theorem traceOf_getElem (B C : Reference k) {i : Nat} (hi : i < (traceOf B C).length) :
    (traceOf B C)[i] = (C.word.getD (B.word.length + i) false, C.label (B.word.length + i + 1)) := by
  simp [traceOf]

theorem extRef_traceOf_word (B C : Reference k) (h : B.word <+: C.word) :
    (extRef B (traceOf B C)).word = C.word := by
  rw [extRef_word]
  have hlen : B.word.length ≤ C.word.length := h.length_le
  have htake : B.word = C.word.take B.word.length := List.prefix_iff_eq_take.mp h
  apply List.ext_getElem
  · simp [traceOf_length]; omega
  · intro i h₁ h₂
    by_cases hi : i < B.word.length
    · rw [List.getElem_append_left hi]
      exact h.getElem hi
    · rw [List.getElem_append_right (by omega)]
      simp only [List.getElem_map, traceOf]
      simp only [List.getElem_map, List.getElem_range]
      have hlt : B.word.length + (i - B.word.length) < C.word.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      congr 1
      omega

theorem extRef_traceOf_label (B C : Reference k) (h : B.word <+: C.word)
    (hl : ∀ j, j ≤ B.word.length → C.label j = B.label j) {j : Nat} (hj : j ≤ C.word.length) :
    (extRef B (traceOf B C)).label j = C.label j := by
  have hlen : B.word.length ≤ C.word.length := h.length_le
  by_cases hjm : j ≤ B.word.length
  · rw [extRef_label_le B _ hjm, hl j hjm]
  · obtain ⟨i, rfl⟩ : ∃ i, j = B.word.length + (i + 1) := ⟨j - B.word.length - 1, by omega⟩
    rw [extRef_label_add, stateAt_succ _ _ (by rw [traceOf_length]; omega), traceOf_getElem]
    show C.label (B.word.length + i + 1) = C.label (B.word.length + (i + 1))
    rw [Nat.add_assoc]

/-- Prefix graphs depend only on the word and the labels up to its length. -/
theorem prefixGraph_congr (I : Instance k) {C C' : Reference k} (hw : C.word = C'.word)
    (hl : ∀ j, j ≤ C.word.length → C.label j = C'.label j) :
    prefixGraph I C = prefixGraph I C' := by
  obtain ⟨w, l⟩ := C
  obtain ⟨w', l'⟩ := C'
  simp only at hw hl
  subst hw
  unfold prefixGraph
  congr 1
  funext j
  have hj : j.val ≤ w.length := by
    have := j.isLt
    change j.val < w.length + 1 at this
    omega
  dsimp only
  rw [hl j.val hj]
  congr 1
  simp only [mask]
  congr 1
  funext p
  apply any_congr
  intro h hh
  rw [hl h (Nat.le_trans (mem_borders_le hh) hj)]

theorem safeReference_congr (I : Instance k) {C C' : Reference k} (hw : C.word = C'.word)
    (hl : ∀ j, j ≤ C.word.length → C.label j = C'.label j) (h : SafeReference I C) :
    SafeReference I C' := by
  obtain ⟨w, l⟩ := C
  obtain ⟨w', l'⟩ := C'
  simp only at hw hl
  subst hw
  obtain ⟨hne, hacc, hrun, hsafe, hborder⟩ := h
  dsimp only at hne hacc hrun hsafe hborder
  refine ⟨hne, by dsimp only; rw [← hl 0 (Nat.zero_le _)]; exact hacc, ?_, ?_, ?_⟩
  · intro j hj
    dsimp only at hj ⊢
    have := hrun j hj
    rw [hl j (Nat.le_of_lt hj), hl (j + 1) hj] at this
    exact this
  · intro j hj
    dsimp only at hj ⊢
    rw [← hl j hj]
    exact hsafe j hj
  · intro j hj
    dsimp only at hj ⊢
    have := hborder j hj
    have hmask : mask I ⟨w, l⟩ j = mask I ⟨w, l'⟩ j := by
      simp only [mask]
      congr 1
      funext p
      apply any_congr
      intro h hh
      rw [hl h (Nat.le_trans (mem_borders_le hh) hj)]
    rw [← hmask, ← hl j hj]
    exact this

/-! ## The extension setting -/

/-- A safe first-return extension of a base `B`, given by its first letter, the label of
its first fresh position, and the remaining labelled trace. -/
structure Ext (I : Instance k) (B : Reference k) where
  a : Bool
  p : Fin k
  rest : List (Bool × Fin k)
  hm : 0 < B.word.length
  hr : FirstReturn (extRef B ((a, p) :: rest)).word B.word.length (extRef B ((a, p) :: rest)).word.length
  safe : SafeReference I (extRef B ((a, p) :: rest))

/-- Every safe first-return extension is such a setting (up to labels beyond the word). -/
theorem exists_ext (I : Instance k) (B C : Reference k) (hB : SafeReference I B)
    (hC : FirstReturnExt I B C) :
    ∃ E : Ext I B, prefixGraph I C = prefixGraph I (extRef B ((E.a, E.p) :: E.rest)) := by
  have hw := extRef_traceOf_word B C hC.word
  have hl : ∀ j, j ≤ C.word.length → (extRef B (traceOf B C)).label j = C.label j :=
    fun j hj => extRef_traceOf_label B C hC.word hC.label hj
  have hlen : B.word.length < C.word.length := hC.firstReturn.1
  have hne : traceOf B C ≠ [] := by
    intro h
    have := traceOf_length B C
    rw [h] at this
    simp at this
    omega
  obtain ⟨⟨a, p⟩, rest, hext⟩ : ∃ (x : Bool × Fin k) (rest : List (Bool × Fin k)),
      traceOf B C = x :: rest := by
    cases h : traceOf B C with
    | nil => exact absurd h hne
    | cons x rest => exact ⟨x, rest, rfl⟩
  rw [hext] at hw hl
  have hG : prefixGraph I C = prefixGraph I (extRef B ((a, p) :: rest)) :=
    prefixGraph_congr I hw.symm (fun j hj => (hl j hj).symm)
  refine ⟨⟨a, p, rest, hB.nonempty, ?_, ?_⟩, hG⟩
  · rw [hw]; exact hC.firstReturn
  · exact safeReference_congr I hw.symm (fun j hj => (hl j hj).symm) hC.safe

namespace Ext
variable {I : Instance k} {B : Reference k} (E : Ext I B)

/-- The labelled trace. -/
abbrev ext : List (Bool × Fin k) := (E.a, E.p) :: E.rest

/-- The extension reference. -/
abbrev C : Reference k := extRef B ((E.a, E.p) :: E.rest)

theorem C_eq : E.C = extRef B E.ext := rfl

/-- Length of the extension word. -/
abbrev N : Nat := E.C.word.length

theorem N_def : E.N = (extRef B ((E.a, E.p) :: E.rest)).word.length := rfl

theorem m_lt_N : B.word.length < E.N := E.hr.1

theorem N_eq : E.N = B.word.length + 1 + E.rest.length := by
  show (extRef B ((E.a, E.p) :: E.rest)).word.length = _
  rw [extRef_length]; simp; omega

theorem word_m : E.C.word[B.word.length]? = some E.a := by
  have := extRef_getElem? B ((E.a, E.p) :: E.rest) 0
  simpa using this

theorem word_lt {j : Nat} (hj : j < B.word.length) : E.C.word[j]? = B.word[j]? :=
  extRef_getElem?_lt B _ hj

theorem word_some {j : Nat} (hj : j < E.N) : ∃ b, E.C.word[j]? = some b :=
  ⟨E.C.word[j], List.getElem?_eq_getElem hj⟩

theorem word_none : E.C.word[E.N]? = none := List.getElem?_eq_none_iff.mpr (Nat.le_refl _)

theorem word_isSome_iff (j : Nat) : (E.C.word[j]?).isSome = true ↔ j < E.N := by
  constructor
  · intro h
    cases hw : E.C.word[j]? with
    | none => rw [hw] at h; simp at h
    | some b => exact (List.getElem?_eq_some_iff.mp hw).1
  · intro h
    obtain ⟨b, hb⟩ := E.word_some h
    rw [hb]; rfl

theorem label_le {j : Nat} (hj : j ≤ B.word.length) : E.C.label j = B.label j :=
  extRef_label_le B _ hj

theorem label_m1 : E.C.label (B.word.length + 1) = E.p := by
  have := extRef_label_add B ((E.a, E.p) :: E.rest) 1
  rw [this]
  rfl

/-! ### The generator cursor at a fresh position -/

/-- KMP cursor (in the base) of position `j` of the extension. -/
def cur (j : Nat) : Nat := FirstReturnGraph.cursor E.C.word B.word.length (j - B.word.length)

theorem cur_le {j : Nat} (hj : j ≤ E.N) : E.cur j ≤ B.word.length := by
  unfold cur
  apply cursor_le B ((E.a, E.p) :: E.rest) E.hm
  have := E.N_eq
  simp only [List.length_cons]
  omega

theorem cur_eq_parent {j : Nat} (hmj : B.word.length ≤ j) (hj : j ≤ E.N) :
    E.cur j = failureParent (E.C.word.take j) := by
  unfold cur
  have hN := E.N_def
  have h := FirstReturnGraph.cursor_eq_parent E.hm E.hr (d := j - B.word.length) (by omega)
  rw [h]
  congr 2
  omega

theorem cur_lt {j : Nat} (hmj : B.word.length < j) (hj : j < E.N) : E.cur j < B.word.length := by
  rw [E.cur_eq_parent (Nat.le_of_lt hmj) (Nat.le_of_lt hj)]
  exact first_return_internal_parent_lt E.hr hmj hj

theorem cur_N : E.cur E.N = B.word.length := by
  rw [E.cur_eq_parent (Nat.le_of_lt E.m_lt_N) (Nat.le_refl _)]
  exact first_return_parent E.hr

theorem cur_eq_m_iff {j : Nat} (hmj : B.word.length < j) (hj : j ≤ E.N) :
    E.cur j = B.word.length ↔ j = E.N := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    have := E.cur_lt hmj (Nat.lt_of_le_of_ne hj hne)
    omega
  · intro h; rw [h]; exact E.cur_N

theorem cur_succ {j : Nat} {b : Bool} (hmj : B.word.length ≤ j) (hb : E.C.word[j]? = some b) :
    E.cur (j + 1) = advance B.word (E.cur j) b := by
  have hj : j < E.N := (List.getElem?_eq_some_iff.mp hb).1
  unfold cur
  have h := cursor_succ B ((E.a, E.p) :: E.rest) E.hm (d := j - B.word.length) (b := b)
    (by rw [show B.word.length + (j - B.word.length) = j by omega]; exact hb)
    (by have := E.N_eq; simp only [List.length_cons]; omega)
  rw [show j + 1 - B.word.length = j - B.word.length + 1 by omega]
  exact h

theorem cur_m : E.cur B.word.length = failureParent B.word := by
  unfold cur
  rw [Nat.sub_self, FirstReturnGraph.cursor, extRef_take]

theorem cur_first : E.cur (B.word.length + 1) = advance B.word (failureParent B.word) E.a := by
  rw [E.cur_succ (Nat.le_refl _) E.word_m, E.cur_m]

/-! ### Colours -/

theorem colC_old {j : Nat} (hj : j ≤ B.word.length) : colB I E.C j = coreMap E.a (colB I B j) :=
  colC_old_all I B E.a E.p E.rest hj

theorem colC_fresh {j : Nat} (hmj : B.word.length < j) (hj : j ≤ E.N) :
    colB I E.C j = freshMap I (E.C.label j) (E.C.word[j]?) (colB I B (E.cur j)) :=
  RankQuerySound.colC_fresh I B _ E.hm E.hr hmj hj

theorem colB_isEnd {j : Nat} : (colB I B j).isEnd = decide (j = B.word.length) := rfl

theorem colB_mask (j : Nat) : (colB I B j).mask = mask I B j := rfl

theorem colB_state (j : Nat) : (colB I B j).state = B.label j := rfl

theorem colB_m_isEnd : (colB I B B.word.length).isEnd = true := by simp [colB]

theorem colB_m_root (hm : 0 < B.word.length) : (colB I B B.word.length).root = false := by
  show decide (B.word.length = 0) = false
  exact decide_eq_false (by omega)

theorem colB_m_next : (colB I B B.word.length).next = none := by
  simp [colB]

/-! ### Safety facts -/

theorem step_label {j : Nat} {b : Bool} (hb : E.C.word[j]? = some b) :
    step I (E.C.label (j + 1)) b = some (E.C.label j) := by
  have hj : j < E.N := (List.getElem?_eq_some_iff.mp hb).1
  have h := E.safe.run j hj
  rw [List.getElem?_eq_getElem hj] at hb
  rw [← Option.some.inj hb]
  exact h

theorem bad_false {j : Nat} (hj : j ≤ E.N) : I.bad.get (E.C.label j) = false := E.safe.safe j hj

/-- The two components of the safety mask at a fresh position: no diagonal flag, and the
base mask at the cursor does not contain the label. -/
theorem fresh_clear {j : Nat} (hmj : B.word.length < j) (hj : j ≤ E.N) :
    (I.flags.get (E.C.label j)).get (E.C.label j) = false ∧
      (mask I B (E.cur j)).get (E.C.label j) = false := by
  have h := E.safe.border j hj
  rw [RankQueryFirstReturn.mask_get_eq] at h
  have h2 := (FirstReturnGraph.fresh_clear_iff E.hm E.hr hmj hj
    (fun p t => (I.flags.get p).get t) E.C.label).mp h
  refine ⟨h2.1, ?_⟩
  have hcur : E.cur j ≤ B.word.length := E.cur_le hj
  have h3 := frMask_ext I B ((E.a, E.p) :: E.rest) E.hm hcur (E.C.label j)
  rw [← h3]
  exact h2.2

theorem diag_false {j : Nat} (hmj : B.word.length < j) (hj : j ≤ E.N) :
    (I.flags.get (E.C.label j)).get (E.C.label j) = false := (E.fresh_clear hmj hj).1

theorem maskB_cur_false {j : Nat} (hmj : B.word.length < j) (hj : j ≤ E.N) :
    (mask I B (E.cur j)).get (E.C.label j) = false := (E.fresh_clear hmj hj).2

/-! ### Edges, by position -/

/-- Edge destination from position `j` of the extension graph. -/
def edge (j : Nat) (hj : j ≤ E.N) (l : Label) : Option Nat := edgeC I B ((E.a, E.p) :: E.rest) j hj l

theorem edge_val {j : Nat} (hj : j ≤ E.N) (l : Label) :
    ((prefixGraph I E.C).edge ⟨j, Nat.lt_succ_of_le hj⟩ l).map Fin.val = E.edge j hj l := rfl

theorem edge_F_old {j : Nat} (hj : j ≤ B.word.length) (hjC : j ≤ E.N) :
    E.edge j hjC .F = some (failureParent (B.word.take j)) :=
  edgeC_F_old I B _ E.hm E.hr hj hjC

theorem edge_F_fresh {j : Nat} (hmj : B.word.length < j) (hjC : j ≤ E.N) :
    E.edge j hjC .F = some (E.cur j) :=
  edgeC_F_fresh I B _ E.hm E.hr hmj hjC

theorem edge_S {j : Nat} (hjC : j ≤ E.N) :
    E.edge j hjC .S = if j < E.N then some (j + 1) else none :=
  edgeC_S I B _ E.hm E.hr hjC

theorem edge_K_old {j : Nat} (hj : j < B.word.length) (hjC : j ≤ E.N) (b : Bool) :
    E.edge j hjC (.K b) = some (advance B.word j b) :=
  edgeC_K_old I B _ E.hm E.hr hj hjC b

theorem edge_K_m (hjC : B.word.length ≤ E.N) (b : Bool) :
    E.edge B.word.length hjC (.K b) =
      some (if b = E.a then B.word.length + 1 else advance B.word B.word.length b) := by
  rw [edge, edgeC_K_m I B _ E.hm E.hr hjC b]
  have hw := E.word_m
  by_cases hba : b = E.a
  · simp [hba, hw]
  · have : ¬ (E.C.word[B.word.length]? = some b) := by
      rw [hw]; intro h; exact hba (Option.some.inj h).symm
    simp [hba, this]

theorem edge_K_fresh {j : Nat} (hmj : B.word.length < j) (hj : j < E.N) (b : Bool) :
    E.edge j (Nat.le_of_lt hj) (.K b) =
      some (if E.C.word[j]? = some b then j + 1 else advance B.word (E.cur j) b) :=
  edgeC_K_fresh I B _ E.hm E.hr hmj hj b

theorem edge_K_N (b : Bool) :
    E.edge E.N (Nat.le_refl _) (.K b) =
      some (if b = E.a then B.word.length + 1 else advance B.word B.word.length b) := by
  rw [edge, edgeC_K_end I B _ E.hm E.hr b]
  have hw := E.word_m
  by_cases hba : b = E.a
  · simp [hba, hw]
  · have : ¬ (E.C.word[B.word.length]? = some b) := by
      rw [hw]; intro h; exact hba (Option.some.inj h).symm
    simp [hba, this]

theorem edge_congr {j j' : Nat} (h : j = j') (hj : j ≤ E.N) (hj' : j' ≤ E.N) (l : Label) :
    E.edge j hj l = E.edge j' hj' l := by
  subst h; rfl

/-- Recover a `Fin`-valued edge from its position value. -/
theorem edge_fin {j j' : Nat} (hj : j ≤ E.N) {l : Label} (h : E.edge j hj l = some j') :
    ∃ h' : j' < (prefixGraph I E.C).size,
      (prefixGraph I E.C).edge ⟨j, Nat.lt_succ_of_le hj⟩ l = some ⟨j', h'⟩ :=
  edge_of_edgeC I B ((E.a, E.p) :: E.rest) hj h

end Ext

/-! ## Consecutive-pair predicates on lists -/

/-- `Consec R l`: every two consecutive elements of `l` satisfy `R`. -/
def Consec {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: l => R x y ∧ Consec R (y :: l)

theorem consec_tail {α : Type} {R : α → α → Prop} {x : α} {l : List α} (h : Consec R (x :: l)) :
    Consec R l := by
  cases l with
  | nil => trivial
  | cons y l => exact h.2

theorem consec_cons_cons {α : Type} {R : α → α → Prop} {x y : α} {l : List α} :
    Consec R (x :: y :: l) ↔ R x y ∧ Consec R (y :: l) := Iff.rfl

theorem consec_getElem {α : Type} {R : α → α → Prop} : ∀ {l : List α}, Consec R l →
    ∀ i (h : i + 1 < l.length), R l[i] l[i + 1] := by
  intro l
  induction l with
  | nil => intro _ i h; simp at h
  | cons x l ih =>
    intro hc i h
    cases l with
    | nil => simp at h
    | cons y l =>
      cases i with
      | zero => exact hc.1
      | succ i => exact ih hc.2 i (by simpa using h)

theorem consec_of_getElem {α : Type} {R : α → α → Prop} : ∀ {l : List α},
    (∀ i (h : i + 1 < l.length), R l[i] l[i + 1]) → Consec R l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons x l ih =>
    intro h
    cases l with
    | nil => trivial
    | cons y l =>
      refine ⟨h 0 (by simp), ?_⟩
      exact ih fun i hi => h (i + 1) (by simpa using hi)

theorem consec_mono {α : Type} {R R' : α → α → Prop} (h : ∀ x y, R x y → R' x y) :
    ∀ {l : List α}, Consec R l → Consec R' l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons x l ih =>
    intro hc
    cases l with
    | nil => trivial
    | cons y l => exact ⟨h _ _ hc.1, ih hc.2⟩

/-- `Chain` of the query semantics is `Consec Step`. -/
theorem chain_iff_consec (G : Graph k) (O : Observer k) : ∀ (l : List (Node G O)),
    Chain G O l ↔ Consec (Step G O) l := by
  intro l
  induction l with
  | nil => exact Iff.rfl
  | cons x l ih =>
    cases l with
    | nil => exact Iff.rfl
    | cons y l =>
      show Step G O x y ∧ Chain G O (y :: l) ↔ Step G O x y ∧ Consec (Step G O) (y :: l)
      rw [ih]

/-! ## Nodes as pairs of naturals -/

/-- A node of a graph as `(position, control)`. -/
abbrev NNode := Nat × Nat

def toN {G : Graph k} {O : Observer k} (n : Node G O) : NNode := (n.1.val, n.2.val)

theorem toN_injective {G : Graph k} {O : Observer k} {x y : Node G O} (h : toN x = toN y) : x = y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [toN, Prod.mk.injEq] at h
  rw [Fin.ext h.1, Fin.ext h.2]

/-- A step between two `Nat` nodes, with the bounds packaged. -/
def NStep (G : Graph k) (O : Observer k) (x y : NNode) : Prop :=
  ∃ (hx : x.1 < G.size) (hy : y.1 < G.size) (hs : x.2 < O.size) (ht : y.2 < O.size),
    Step G O (⟨x.1, hx⟩, ⟨x.2, hs⟩) (⟨y.1, hy⟩, ⟨y.2, ht⟩)

def NAllowed (G : Graph k) (O : Observer k) (x : NNode) : Prop :=
  ∃ (hx : x.1 < G.size) (hs : x.2 < O.size), Allowed G O (⟨x.1, hx⟩, ⟨x.2, hs⟩)

theorem nstep_of_step {G : Graph k} {O : Observer k} {x y : Node G O} (h : Step G O x y) :
    NStep G O (toN x) (toN y) :=
  ⟨x.1.isLt, y.1.isLt, x.2.isLt, y.2.isLt, h⟩

theorem nallowed_of_allowed {G : Graph k} {O : Observer k} {x : Node G O} (h : Allowed G O x) :
    NAllowed G O (toN x) :=
  ⟨x.1.isLt, x.2.isLt, h⟩

theorem nallowed_bounds {G : Graph k} {O : Observer k} {x : NNode} (h : NAllowed G O x) :
    x.1 < G.size ∧ x.2 < O.size := by
  obtain ⟨hx, hs, -⟩ := h
  exact ⟨hx, hs⟩

theorem nstep_allowed {G : Graph k} {O : Observer k} {x y : NNode} (h : NStep G O x y) :
    NAllowed G O y := by
  obtain ⟨hx, hy, hs, ht, hst⟩ := h
  obtain ⟨-, -, -, ha⟩ := hst
  exact ⟨hy, ht, ha⟩

theorem consec_nstep_of_chain {G : Graph k} {O : Observer k} {l : List (Node G O)} (h : Chain G O l) :
    Consec (NStep G O) (l.map toN) := by
  rw [chain_iff_consec] at h
  induction l with
  | nil => trivial
  | cons x l ih =>
    cases l with
    | nil => trivial
    | cons y l => exact ⟨nstep_of_step h.1, ih h.2⟩

theorem nodup_map_toN {G : Graph k} {O : Observer k} {l : List (Node G O)} (h : l.Nodup) :
    (l.map toN).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨hx, hl⟩ := List.nodup_cons.mp h
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl⟩
    intro hm
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    exact hx (toN_injective he ▸ hy)

/-! ## Segmentation of a chain into old and fresh-consecutive blocks -/

/-- Two consecutive nodes stay in one block: both old, or a fresh node followed by its
physical successor. -/
def compat (m : Nat) (x y : NNode) : Bool :=
  (decide (x.1 ≤ m) && decide (y.1 ≤ m)) || (decide (m < x.1) && decide (y.1 = x.1 + 1))

theorem compat_true_iff {m : Nat} {x y : NNode} :
    compat m x y = true ↔ (x.1 ≤ m ∧ y.1 ≤ m) ∨ (m < x.1 ∧ y.1 = x.1 + 1) := by
  simp [compat]

theorem compat_false_iff {m : Nat} {x y : NNode} :
    compat m x y = false ↔ ¬ (x.1 ≤ m ∧ y.1 ≤ m) ∧ ¬ (m < x.1 ∧ y.1 = x.1 + 1) := by
  rw [← Bool.not_eq_true, compat_true_iff]
  constructor
  · intro h; exact ⟨fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  · rintro ⟨h1, h2⟩ (h | h)
    · exact h1 h
    · exact h2 h

/-- Maximal blocks of a node list. -/
def segments (m : Nat) : List NNode → List (List NNode)
  | [] => []
  | x :: xs =>
    match segments m xs with
    | [] => [[x]]
    | [] :: segs => [x] :: segs
    | (y :: seg) :: segs =>
      if compat m x y then (x :: y :: seg) :: segs else [x] :: (y :: seg) :: segs

theorem segments_flatten (m : Nat) : ∀ xs : List NNode, (segments m xs).flatten = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [segments]
    split
    · rename_i h
      rw [h] at ih
      simp at ih
      simp [ih]
    · rename_i h
      rw [h] at ih
      simpa using ih
    · rename_i y seg segs h
      rw [h] at ih
      split
      · simpa using ih
      · simpa using ih

theorem segments_eq_nil_iff (m : Nat) (xs : List NNode) : segments m xs = [] ↔ xs = [] := by
  constructor
  · intro h
    have := segments_flatten m xs
    rw [h] at this
    simpa using this.symm
  · intro h; subst h; rfl

/-- The block structure: nonempty blocks, each `Consec R`, consecutive blocks linked by `Q`. -/
def Blocks (R Q : NNode → NNode → Prop) : List (List NNode) → Prop
  | [] => True
  | [s] => s ≠ [] ∧ Consec R s
  | s :: t :: rest => s ≠ [] ∧ Consec R s ∧
      (∀ x y, s.getLast? = some x → t.head? = some y → Q x y) ∧ Blocks R Q (t :: rest)

theorem blocks_head_ne_nil {R Q : NNode → NNode → Prop} {s : List NNode} {rest : List (List NNode)}
    (h : Blocks R Q (s :: rest)) : s ≠ [] := by
  cases rest with
  | nil => exact h.1
  | cons t rest => exact h.1

theorem blocks_head_consec {R Q : NNode → NNode → Prop} {s : List NNode} {rest : List (List NNode)}
    (h : Blocks R Q (s :: rest)) : Consec R s := by
  cases rest with
  | nil => exact h.2
  | cons t rest => exact h.2.1

theorem blocks_tail {R Q : NNode → NNode → Prop} {s : List NNode} {rest : List (List NNode)}
    (h : Blocks R Q (s :: rest)) : Blocks R Q rest := by
  cases rest with
  | nil => trivial
  | cons t rest => exact h.2.2.2

theorem blocks_link {R Q : NNode → NNode → Prop} {s t : List NNode} {rest : List (List NNode)}
    (h : Blocks R Q (s :: t :: rest)) {x y : NNode} (hx : s.getLast? = some x) (hy : t.head? = some y) :
    Q x y := h.2.2.1 x y hx hy

theorem blocks_mem_ne_nil {R Q : NNode → NNode → Prop} : ∀ {segs : List (List NNode)},
    Blocks R Q segs → ∀ s ∈ segs, s ≠ [] := by
  intro segs
  induction segs with
  | nil => intro _ s hs; simp at hs
  | cons s rest ih =>
    intro h t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact blocks_head_ne_nil h
    · exact ih (blocks_tail h) t ht

theorem blocks_mem_consec {R Q : NNode → NNode → Prop} : ∀ {segs : List (List NNode)},
    Blocks R Q segs → ∀ s ∈ segs, Consec R s := by
  intro segs
  induction segs with
  | nil => intro _ s hs; simp at hs
  | cons s rest ih =>
    intro h t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact blocks_head_consec h
    · exact ih (blocks_tail h) t ht

/-- The head of a nonempty list of nonempty blocks is the head of the flatten. -/
theorem flatten_head? {s : List NNode} {rest : List (List NNode)} (hs : s ≠ []) :
    (s :: rest).flatten.head? = s.head? := by
  cases s with
  | nil => exact absurd rfl hs
  | cons x s => simp

theorem flatten_getLast? : ∀ {segs : List (List NNode)}, (∀ s ∈ segs, s ≠ []) →
    ∀ {s : List NNode}, segs.getLast? = some s → segs.flatten.getLast? = s.getLast? := by
  intro segs
  induction segs with
  | nil => intro _ s h; simp at h
  | cons t rest ih =>
    intro hne s hs
    cases rest with
    | nil =>
      simp at hs; subst hs; simp
    | cons t' rest' =>
      have hs' : (t' :: rest').getLast? = some s := by simpa using hs
      have hne' : ∀ u ∈ t' :: rest', u ≠ [] := fun u hu => hne u (List.mem_cons_of_mem _ hu)
      have hrec := ih hne' hs'
      rw [List.flatten_cons, List.getLast?_append, hrec]
      have hsne : s ≠ [] := hne s (List.mem_cons_of_mem _ (List.mem_of_getLast? hs'))
      cases hl : s.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hsne
      | some v => rfl

theorem segments_head? {m : Nat} {xs : List NNode} {y : NNode} {seg : List NNode}
    {segs : List (List NNode)} (h : segments m xs = (y :: seg) :: segs) : xs.head? = some y := by
  have hf := segments_flatten m xs
  rw [h] at hf
  rw [← hf]
  simp

/-- The segmentation of a `Consec S` list has the block structure. -/
theorem segments_blocks (m : Nat) {S : NNode → NNode → Prop} : ∀ {xs : List NNode}, Consec S xs →
    Blocks (fun x y => S x y ∧ compat m x y = true) (fun x y => S x y ∧ compat m x y = false)
      (segments m xs) := by
  intro xs
  induction xs with
  | nil => intro _; trivial
  | cons x xs ih =>
    intro hc
    have ih' := ih (consec_tail hc)
    simp only [segments]
    split
    · exact ⟨by simp, trivial⟩
    · rename_i h
      rw [h] at ih'
      exact absurd rfl (blocks_head_ne_nil ih')
    · rename_i y seg segs h
      rw [h] at ih'
      have hy : xs.head? = some y := segments_head? h
      have hxs : ∃ l, xs = y :: l := by
        cases xs with
        | nil => simp at hy
        | cons z l => simp at hy; subst hy; exact ⟨l, rfl⟩
      obtain ⟨l, rfl⟩ := hxs
      have hS : S x y := hc.1
      split
      · rename_i hcompat
        cases segs with
        | nil =>
          exact ⟨by simp, ⟨⟨hS, hcompat⟩, blocks_head_consec ih'⟩⟩
        | cons t rest =>
          refine ⟨by simp, ⟨⟨hS, hcompat⟩, blocks_head_consec ih'⟩, ?_, blocks_tail ih'⟩
          intro u v hu hv
          exact blocks_link ih' (by simpa using hu) hv
      · rename_i hcompat
        refine ⟨by simp, trivial, ?_, ih'⟩
        intro u v hu hv
        simp at hu hv
        subst hu; subst hv
        exact ⟨hS, Bool.eq_false_iff.mpr hcompat⟩

/-! ### Old and fresh blocks -/

/-- Position of the head of a block (`0` for the empty block). -/
def hdPos (s : List NNode) : Nat := ((s.head?).map Prod.fst).getD 0

/-- Position of the last node of a block. -/
def lastPos (s : List NNode) : Nat := ((s.getLast?).map Prod.fst).getD 0

def hdCtl (s : List NNode) : Nat := ((s.head?).map Prod.snd).getD 0

def lastCtl (s : List NNode) : Nat := ((s.getLast?).map Prod.snd).getD 0

/-- Control of the node of a fresh block at position `j`. -/
def ctlAt (s : List NNode) (j : Nat) : Nat := ((s.map Prod.snd).getD (j - hdPos s) 0)

def isFresh (m : Nat) (s : List NNode) : Bool := decide (m < hdPos s)

theorem hdPos_cons (x : NNode) (s : List NNode) : hdPos (x :: s) = x.1 := rfl

theorem hdCtl_cons (x : NNode) (s : List NNode) : hdCtl (x :: s) = x.2 := rfl

theorem lastPos_eq {s : List NNode} {x : NNode} (h : s.getLast? = some x) : lastPos s = x.1 := by
  simp [lastPos, h]

theorem lastCtl_eq {s : List NNode} {x : NNode} (h : s.getLast? = some x) : lastCtl s = x.2 := by
  simp [lastCtl, h]

theorem hdPos_eq {s : List NNode} {x : NNode} (h : s.head? = some x) : hdPos s = x.1 := by
  simp [hdPos, h]

theorem hdCtl_eq {s : List NNode} {x : NNode} (h : s.head? = some x) : hdCtl s = x.2 := by
  simp [hdCtl, h]

/-- In a compat-consecutive block starting old, every node is old. -/
theorem consec_compat_old {m : Nat} {S : NNode → NNode → Prop} : ∀ {s : List NNode},
    Consec (fun x y => S x y ∧ compat m x y = true) s → ¬ (m < hdPos s) → ∀ n ∈ s, n.1 ≤ m := by
  intro s
  induction s with
  | nil => intro _ _ n hn; simp at hn
  | cons x s ih =>
    intro hc hx n hn
    rw [hdPos_cons] at hx
    rcases List.mem_cons.mp hn with rfl | hn
    · omega
    · cases s with
      | nil => simp at hn
      | cons y s =>
        have h1 := (compat_true_iff.mp hc.1.2)
        have hy : y.1 ≤ m := by
          rcases h1 with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · omega
        exact ih hc.2 (by rw [hdPos_cons]; omega) n hn

/-- In a compat-consecutive block starting fresh, positions are consecutive. -/
theorem consec_compat_fresh {m : Nat} {S : NNode → NNode → Prop} : ∀ {s : List NNode},
    Consec (fun x y => S x y ∧ compat m x y = true) s → m < hdPos s →
    ∀ i (hi : i < s.length), (s[i]).1 = hdPos s + i := by
  intro s
  induction s with
  | nil => intro _ _ i hi; simp at hi
  | cons x s ih =>
    intro hc hx i hi
    rw [hdPos_cons] at hx ⊢
    cases i with
    | zero => simp
    | succ i =>
      cases s with
      | nil => simp at hi
      | cons y s =>
        have h1 := compat_true_iff.mp hc.1.2
        have hy : y.1 = x.1 + 1 := by
          rcases h1 with ⟨h, -⟩ | ⟨-, h⟩
          · omega
          · exact h
        have := ih hc.2 (by rw [hdPos_cons]; omega) i (by simpa using hi)
        rw [hdPos_cons] at this
        simp only [List.getElem_cons_succ]
        omega

theorem fresh_block_pos_le {m : Nat} {S : NNode → NNode → Prop} {s : List NNode}
    (hc : Consec (fun x y => S x y ∧ compat m x y = true) s) (hx : m < hdPos s)
    {i : Nat} (hi : i < s.length) : hdPos s ≤ (s[i]).1 := by
  rw [consec_compat_fresh hc hx i hi]; omega

theorem fresh_block_lastPos {m : Nat} {S : NNode → NNode → Prop} {s : List NNode} (hne : s ≠ [])
    (hc : Consec (fun x y => S x y ∧ compat m x y = true) s) (hx : m < hdPos s) :
    lastPos s = hdPos s + (s.length - 1) := by
  have hlen : 0 < s.length := List.length_pos_iff.mpr hne
  have h := consec_compat_fresh hc hx (s.length - 1) (by omega)
  rw [lastPos, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  simpa using h

/-- Control of a fresh block at an internal position. -/
theorem ctlAt_getElem {s : List NNode} {i : Nat} (hi : i < s.length) :
    ctlAt s (hdPos s + i) = (s[i]).2 := by
  simp only [ctlAt, Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD]
  rw [List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

theorem ctlAt_hd {s : List NNode} (hne : s ≠ []) : ctlAt s (hdPos s) = hdCtl s := by
  cases s with
  | nil => exact absurd rfl hne
  | cons x s => simp [ctlAt, hdPos, hdCtl]

theorem ctlAt_last {m : Nat} {S : NNode → NNode → Prop} {s : List NNode} (hne : s ≠ [])
    (hc : Consec (fun x y => S x y ∧ compat m x y = true) s) (hx : m < hdPos s) :
    ctlAt s (lastPos s) = lastCtl s := by
  have hlen : 0 < s.length := List.length_pos_iff.mpr hne
  rw [fresh_block_lastPos hne hc hx, ctlAt_getElem (by omega), lastCtl, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega)]
  rfl

/-! ### Counting blocks -/

/-- Head node of a block (`(0,0)` for the empty block). -/
def hdN (s : List NNode) : NNode := s.headD (0, 0)

theorem hdN_cons (x : NNode) (s : List NNode) : hdN (x :: s) = x := rfl

theorem hdPos_eq_hdN {s : List NNode} (hne : s ≠ []) : hdPos s = (hdN s).1 := by
  cases s with
  | nil => exact absurd rfl hne
  | cons x s => rfl

/-- Number of fresh blocks. -/
def freshCount (m : Nat) (segs : List (List NNode)) : Nat := (segs.filter (isFresh m)).length

/-- Number of nodes at position `p`. -/
def visitsN (p : Nat) (xs : List NNode) : Nat := (xs.filter fun n => decide (n.1 = p)).length

theorem visitsN_map_toN {G : Graph k} {O : Observer k} (xs : List (Node G O)) (entry : Fin G.size) :
    visitsN entry.val (xs.map toN) = visits G O xs entry := by
  unfold visitsN visits
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro n _
  show decide (n.1.val = entry.val) = decide (n.1 = entry)
  exact decide_eq_decide.mpr Fin.ext_iff.symm

theorem map_hdN_sublist : ∀ {segs : List (List NNode)}, (∀ s ∈ segs, s ≠ []) →
    (segs.map hdN).Sublist segs.flatten := by
  intro segs
  induction segs with
  | nil => intro _; exact List.Sublist.refl _
  | cons s rest ih =>
    intro hne
    have hs : s ≠ [] := hne s (List.mem_cons_self ..)
    have ih' := ih fun t ht => hne t (List.mem_cons_of_mem _ ht)
    cases s with
    | nil => exact absurd rfl hs
    | cons x s' =>
      simp only [List.map_cons, hdN_cons, List.flatten_cons, List.cons_append]
      exact List.Sublist.cons_cons x (ih'.trans (List.sublist_append_right s' _))

theorem length_filter_le_of_imp {α : Type} {p q : α → Bool} : ∀ {l : List α},
    (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
    intro h
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hp : p x = true
    · have hq := h x (List.mem_cons_self ..) hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      simp only [List.length_cons]
      omega
    · have hp' : ¬ p x = true := hp
      by_cases hq : q x = true
      · rw [List.filter_cons_of_neg hp', List.filter_cons_of_pos hq]
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_neg hp', List.filter_cons_of_neg hq]
        exact ih'

section Counting
variable {I : Instance k} {B : Reference k} (E : Ext I B) (o : Observer k)

/-- The block relations of a chain of `o` in the extension graph. -/
abbrev InBlock (x y : NNode) : Prop := NStep (prefixGraph I E.C) o x y ∧ compat B.word.length x y = true
abbrev Link (x y : NNode) : Prop := NStep (prefixGraph I E.C) o x y ∧ compat B.word.length x y = false

/-- A fresh block entered from a previous block starts at the first fresh vertex. -/
theorem link_fresh_head {x y : NNode} (h : Link E o x y) (hy : B.word.length < y.1) :
    y.1 = B.word.length + 1 := by
  obtain ⟨⟨hx1, hy1, hx2, hy2, hstep⟩, hcomp⟩ := h
  obtain ⟨l, he, -, -⟩ := hstep
  have hc := compat_false_iff.mp hcomp
  exact RankQueryFirstReturn.fresh_break_target I E.C E.hm E.hr he ⟨hy, hc.2⟩

theorem blocks_fresh_heads : ∀ {s : List NNode} {rest : List (List NNode)},
    Blocks (InBlock E o) (Link E o) (s :: rest) →
    ∀ t ∈ rest, isFresh B.word.length t = true → hdPos t = B.word.length + 1 := by
  intro s rest
  induction rest generalizing s with
  | nil => intro _ t ht; simp at ht
  | cons t rest ih =>
    intro h u hu hfresh
    rcases List.mem_cons.mp hu with rfl | hu
    · have hne_s := blocks_head_ne_nil h
      have hne_u := blocks_head_ne_nil (blocks_tail h)
      obtain ⟨x, hx⟩ : ∃ x, s.getLast? = some x := by
        cases hl : s.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne_s
        | some x => exact ⟨x, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y, u.head? = some y := by
        cases hl : u.head? with
        | none => exact absurd (List.head?_eq_none_iff.mp hl) hne_u
        | some y => exact ⟨y, rfl⟩
      have hlink := blocks_link h hx hy
      rw [hdPos_eq hy]
      simp only [isFresh, decide_eq_true_eq] at hfresh
      rw [hdPos_eq hy] at hfresh
      exact link_fresh_head E o hlink hfresh
    · exact ih (blocks_tail h) u hu hfresh

/-- At most `1 + visits(m+1)` fresh blocks. -/
theorem freshCount_le_visits {xs : List NNode} (hc : Consec (NStep (prefixGraph I E.C) o) xs) :
    freshCount B.word.length (segments B.word.length xs) ≤ 1 + visitsN (B.word.length + 1) xs := by
  have hb := segments_blocks B.word.length hc
  have hf := segments_flatten B.word.length xs
  cases hsegs : segments B.word.length xs with
  | nil => simp [freshCount]
  | cons s rest =>
    rw [hsegs] at hb hf
    have hne : ∀ t ∈ s :: rest, t ≠ [] := blocks_mem_ne_nil hb
    have hheads := blocks_fresh_heads E o hb
    unfold freshCount
    have h1 : ((s :: rest).filter (isFresh B.word.length)).length ≤
        1 + (rest.filter (isFresh B.word.length)).length := by
      by_cases hs : isFresh B.word.length s = true
      · rw [List.filter_cons_of_pos hs, List.length_cons]; omega
      · rw [List.filter_cons_of_neg hs]; omega
    have h2 : (rest.filter (isFresh B.word.length)).length ≤
        (rest.filter fun t => decide ((hdN t).1 = B.word.length + 1)).length := by
      apply length_filter_le_of_imp
      intro t ht hfresh
      have := hheads t ht hfresh
      rw [hdPos_eq_hdN (hne t (List.mem_cons_of_mem _ ht))] at this
      simpa using this
    have h3 : (rest.filter fun t => decide ((hdN t).1 = B.word.length + 1)).length =
        ((rest.map hdN).filter fun n => decide (n.1 = B.word.length + 1)).length := by
      rw [List.filter_map, List.length_map]; rfl
    have h4 : ((rest.map hdN).filter fun n => decide (n.1 = B.word.length + 1)).length ≤
        (((s :: rest).map hdN).filter fun n => decide (n.1 = B.word.length + 1)).length := by
      apply List.Sublist.length_le
      apply List.Sublist.filter
      simp only [List.map_cons]
      exact List.sublist_cons_self _ _
    have h5 : (((s :: rest).map hdN).filter fun n => decide (n.1 = B.word.length + 1)).length ≤
        visitsN (B.word.length + 1) xs := by
      unfold visitsN
      rw [← hf]
      exact List.Sublist.length_le (List.Sublist.filter _ (map_hdN_sublist hne))
    omega

/-- Two consecutive blocks are never both old. -/
theorem blocks_not_both_old {s t : List NNode} {rest : List (List NNode)}
    (h : Blocks (InBlock E o) (Link E o) (s :: t :: rest)) :
    isFresh B.word.length s = true ∨ isFresh B.word.length t = true := by
  apply Classical.byContradiction
  intro hnot
  have hs : ¬ (B.word.length < hdPos s) := by
    intro hlt; apply hnot; left; simpa [isFresh] using hlt
  have ht : ¬ (B.word.length < hdPos t) := by
    intro hlt; apply hnot; right; simpa [isFresh] using hlt
  have hne_s := blocks_head_ne_nil h
  have hne_t := blocks_head_ne_nil (blocks_tail h)
  obtain ⟨x, hx⟩ : ∃ x, s.getLast? = some x := by
    cases hl : s.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne_s
    | some x => exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, t.head? = some y := by
    cases hl : t.head? with
    | none => exact absurd (List.head?_eq_none_iff.mp hl) hne_t
    | some y => exact ⟨y, rfl⟩
  have hlink := blocks_link h hx hy
  have hxold : x.1 ≤ B.word.length :=
    consec_compat_old (blocks_head_consec h) hs x (List.mem_of_getLast? hx)
  have hyold : y.1 ≤ B.word.length := by
    rw [hdPos_eq hy] at ht; omega
  have hcomp := compat_false_iff.mp hlink.2
  exact hcomp.1 ⟨hxold, hyold⟩

theorem length_blocks_le_aux : ∀ {segs : List (List NNode)}, Blocks (InBlock E o) (Link E o) segs →
    segs.length ≤ 2 * freshCount B.word.length segs + 1 ∧
      (∀ s rest, segs = s :: rest → isFresh B.word.length s = true →
        segs.length ≤ 2 * freshCount B.word.length segs) := by
  intro segs
  induction segs with
  | nil => intro _; exact ⟨by simp, fun s rest h => by simp at h⟩
  | cons s rest ih =>
    intro h
    cases rest with
    | nil =>
      refine ⟨by simp [freshCount], ?_⟩
      intro s' rest' he hfresh
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      simp [freshCount, hfresh]
    | cons t rest =>
      obtain ⟨ih1, ih2⟩ := ih (blocks_tail h)
      by_cases hs : isFresh B.word.length s = true
      · have hlen : (s :: t :: rest).length = (t :: rest).length + 1 := rfl
        have hfc : freshCount B.word.length (s :: t :: rest) =
            freshCount B.word.length (t :: rest) + 1 := by
          unfold freshCount
          rw [List.filter_cons_of_pos hs, List.length_cons]
        refine ⟨by omega, ?_⟩
        intro _ _ _ _
        omega
      · have ht : isFresh B.word.length t = true := by
          rcases blocks_not_both_old E o h with h' | h'
          · exact absurd h' hs
          · exact h'
        have hfc : freshCount B.word.length (s :: t :: rest) = freshCount B.word.length (t :: rest) := by
          unfold freshCount
          rw [List.filter_cons_of_neg hs]
        have h2 := ih2 t rest rfl ht
        refine ⟨by simp only [List.length_cons] at h2 ⊢; omega, ?_⟩
        intro s' rest' he hfresh
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        exact absurd hfresh hs

/-- At most `2 · fresh + 1` blocks. -/
theorem length_segments_le {xs : List NNode} (hc : Consec (NStep (prefixGraph I E.C) o) xs) :
    (segments B.word.length xs).length ≤ 2 * freshCount B.word.length (segments B.word.length xs) + 1 :=
  (length_blocks_le_aux E o (segments_blocks B.word.length hc)).1

end Counting

/-! ## Ordered marks -/

/-- The positions of `raw` up to `N`, in increasing order and without repetition. -/
def marksOf (N : Nat) (raw : List Nat) : List Nat :=
  (List.range (N + 1)).filter fun j => decide (j ∈ raw)

theorem mem_marksOf {N : Nat} {raw : List Nat} {j : Nat} : j ∈ marksOf N raw ↔ j ≤ N ∧ j ∈ raw := by
  simp [marksOf, List.mem_filter, List.mem_range, Nat.lt_succ_iff]

theorem marksOf_pairwise (N : Nat) (raw : List Nat) : (marksOf N raw).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem marksOf_nodup (N : Nat) (raw : List Nat) : (marksOf N raw).Nodup :=
  List.Pairwise.filter _ List.nodup_range

theorem marksOf_lt {N : Nat} {raw : List Nat} {i j : Nat} (hi : i < (marksOf N raw).length)
    (hj : j < (marksOf N raw).length) (hij : i < j) : (marksOf N raw)[i] < (marksOf N raw)[j] :=
  List.pairwise_iff_getElem.mp (marksOf_pairwise N raw) i j hi hj hij

theorem marksOf_le {N : Nat} {raw : List Nat} {i j : Nat} (hi : i < (marksOf N raw).length)
    (hj : j < (marksOf N raw).length) (hij : i ≤ j) : (marksOf N raw)[i] ≤ (marksOf N raw)[j] := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact Nat.le_of_lt (marksOf_lt hi hj h)
  · subst h; exact Nat.le_refl _

theorem marksOf_getElem_le {N : Nat} {raw : List Nat} {i : Nat} (hi : i < (marksOf N raw).length) :
    (marksOf N raw)[i] ≤ N :=
  (mem_marksOf.mp (List.getElem_mem hi)).1

theorem marksOf_getElem_mem {N : Nat} {raw : List Nat} {i : Nat} (hi : i < (marksOf N raw).length) :
    (marksOf N raw)[i] ∈ raw :=
  (mem_marksOf.mp (List.getElem_mem hi)).2

theorem marksOf_length_le (N : Nat) (raw : List Nat) : (marksOf N raw).length ≤ raw.length :=
  (marksOf_nodup N raw).length_le_of_subset fun j hj => (mem_marksOf.mp hj).2

/-- Group index of a mark. -/
def idxM (M : List Nat) (p : Nat) : Nat := M.idxOf p

theorem idxM_lt {M : List Nat} {p : Nat} (h : p ∈ M) : idxM M p < M.length :=
  List.idxOf_lt_length_iff.mpr h

theorem getElem_idxM {M : List Nat} {p : Nat} (h : p ∈ M) : M[idxM M p]'(idxM_lt h) = p :=
  List.getElem_idxOf _

theorem idxM_mono {N : Nat} {raw : List Nat} {p q : Nat} (hp : p ∈ marksOf N raw)
    (hq : q ∈ marksOf N raw) (hpq : p < q) : idxM (marksOf N raw) p < idxM (marksOf N raw) q := by
  apply Classical.byContradiction
  intro hnot
  have hle : idxM (marksOf N raw) q ≤ idxM (marksOf N raw) p := Nat.le_of_not_lt hnot
  have := marksOf_le (idxM_lt hq) (idxM_lt hp) hle
  rw [getElem_idxM hq, getElem_idxM hp] at this
  omega

theorem idxM_injective {N : Nat} {raw : List Nat} {p q : Nat} (hp : p ∈ marksOf N raw)
    (hq : q ∈ marksOf N raw) (h : idxM (marksOf N raw) p = idxM (marksOf N raw) q) : p = q := by
  have h1 : (marksOf N raw)[idxM (marksOf N raw) p]? = some p := by
    rw [List.getElem?_eq_getElem (idxM_lt hp), getElem_idxM hp]
  rw [h, List.getElem?_eq_getElem (idxM_lt hq), getElem_idxM hq] at h1
  exact (Option.some.inj h1).symm

theorem idxM_getElem {N : Nat} {raw : List Nat} {i : Nat} (hi : i < (marksOf N raw).length) :
    idxM (marksOf N raw) ((marksOf N raw)[i]) = i := by
  have hmem := List.getElem_mem hi
  have h := getElem_idxM hmem
  rcases Nat.lt_trichotomy (idxM (marksOf N raw) (marksOf N raw)[i]) i with hlt | heq | hgt
  · have := marksOf_lt (idxM_lt hmem) hi hlt
    rw [h] at this
    exact absurd this (Nat.lt_irrefl _)
  · exact heq
  · have := marksOf_lt hi (idxM_lt hmem) hgt
    rw [h] at this
    exact absurd this (Nat.lt_irrefl _)

theorem idxM_le_of_le {N : Nat} {raw : List Nat} {p q : Nat} (hp : p ∈ marksOf N raw)
    (hq : q ∈ marksOf N raw) (hpq : p ≤ q) : idxM (marksOf N raw) p ≤ idxM (marksOf N raw) q := by
  rcases Nat.lt_or_eq_of_le hpq with h | h
  · exact Nat.le_of_lt (idxM_mono hp hq h)
  · subst h; exact Nat.le_refl _

/-- The least mark is first. -/
theorem idxM_min {N : Nat} {raw : List Nat} {p : Nat} (hp : p ∈ marksOf N raw)
    (hmin : ∀ q ∈ marksOf N raw, p ≤ q) : idxM (marksOf N raw) p = 0 := by
  apply Classical.byContradiction
  intro hne
  have hpos : 0 < idxM (marksOf N raw) p := Nat.pos_of_ne_zero hne
  have hlen : 0 < (marksOf N raw).length := Nat.lt_of_lt_of_le hpos (Nat.le_of_lt (idxM_lt hp))
  have h1 := marksOf_lt hlen (idxM_lt hp) hpos
  rw [getElem_idxM hp] at h1
  have h2 := hmin _ (List.getElem_mem hlen)
  omega

/-- The greatest mark is last. -/
theorem idxM_max {N : Nat} {raw : List Nat} {p : Nat} (hp : p ∈ marksOf N raw)
    (hmax : ∀ q ∈ marksOf N raw, q ≤ p) : idxM (marksOf N raw) p = (marksOf N raw).length - 1 := by
  have hlt := idxM_lt hp
  apply Classical.byContradiction
  intro hne
  have hlt' : idxM (marksOf N raw) p < (marksOf N raw).length - 1 := by omega
  have h1 := marksOf_lt hlt (by omega) hlt'
  rw [getElem_idxM hp] at h1
  have h2 := hmax _ (List.getElem_mem (by omega : (marksOf N raw).length - 1 < (marksOf N raw).length))
  omega

/-! ## The mixed-radix encoder -/

/-- Inverse of `digits` on in-range digit lists. -/
def encode : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | s :: ss, d :: ds => d * prodList ss + encode ss ds

theorem prodList_pos : ∀ {sizes : List Nat}, (∀ s ∈ sizes, 0 < s) → 0 < prodList sizes := by
  intro sizes
  induction sizes with
  | nil => intro _; simp [prodList]
  | cons s ss ih =>
    intro h
    simp only [prodList]
    exact Nat.mul_pos (h s (List.mem_cons_self ..)) (ih fun t ht => h t (List.mem_cons_of_mem _ ht))

theorem encode_lt : ∀ {sizes ds : List Nat}, (∀ s ∈ sizes, 0 < s) → ds.length = sizes.length →
    (∀ i (hi : i < ds.length) (hs : i < sizes.length), ds[i] < sizes[i]) → encode sizes ds < prodList sizes := by
  intro sizes
  induction sizes with
  | nil => intro ds _ _ _; simp [encode, prodList]
  | cons s ss ih =>
    intro ds hpos hlen hb
    cases ds with
    | nil => simp at hlen
    | cons d ds =>
      have hP : 0 < prodList ss := prodList_pos fun t ht => hpos t (List.mem_cons_of_mem _ ht)
      have hd : d < s := hb 0 (by simp) (by simp)
      have he : encode ss ds < prodList ss := ih (fun t ht => hpos t (List.mem_cons_of_mem _ ht))
        (by simpa using hlen) (fun i hi hs => hb (i + 1) (by simpa using hi) (by simpa using hs))
      simp only [encode, prodList]
      have : d * prodList ss + encode ss ds < (d + 1) * prodList ss := by
        rw [Nat.succ_mul]; omega
      exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hd)

theorem digits_encode : ∀ {sizes ds : List Nat}, (∀ s ∈ sizes, 0 < s) → ds.length = sizes.length →
    (∀ i (hi : i < ds.length) (hs : i < sizes.length), ds[i] < sizes[i]) → digits sizes (encode sizes ds) = ds := by
  intro sizes
  induction sizes with
  | nil => intro ds _ hlen _; cases ds with | nil => rfl | cons _ _ => simp at hlen
  | cons s ss ih =>
    intro ds hpos hlen hb
    cases ds with
    | nil => simp at hlen
    | cons d ds =>
      have hpos' : ∀ t ∈ ss, 0 < t := fun t ht => hpos t (List.mem_cons_of_mem _ ht)
      have hP : 0 < prodList ss := prodList_pos hpos'
      have hd : d < s := hb 0 (by simp) (by simp)
      have hlen' : ds.length = ss.length := by simpa using hlen
      have hb' : ∀ i (hi : i < ds.length) (hs : i < ss.length), ds[i] < ss[i] :=
        fun i hi hs => hb (i + 1) (by simpa using hi) (by simpa using hs)
      have he : encode ss ds < prodList ss := encode_lt hpos' hlen' hb'
      simp only [encode, digits]
      have h1 : (d * prodList ss + encode ss ds) / prodList ss = d := by
        rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt he, Nat.add_zero]
      have h2 : (d * prodList ss + encode ss ds) % prodList ss = encode ss ds := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt he]
      rw [h1, h2, Nat.mod_eq_of_lt hd, ih hpos' hlen' hb']

theorem stateOf_val (q : Fin k) : stateOf k q.val = some q := by
  unfold stateOf
  cases hf : (List.finRange k).find? (fun p => decide (p.val = q.val)) with
  | none =>
    have := (List.find?_eq_none.mp hf) q (List.mem_finRange q)
    simp at this
  | some r =>
    have hr := List.find?_some hf
    simp only [decide_eq_true_eq] at hr
    rw [Fin.ext hr]

theorem nextOfIdx_idxOfNext (n : Option Bool) : nextOfIdx (idxOfNext n) = some n := by
  cases n with
  | none => rfl
  | some b => cases b <;> rfl

theorem idxOfNext_lt (n : Option Bool) : idxOfNext n < 3 := by
  cases n with
  | none => decide
  | some b => cases b <;> decide

/-- Encoded interval control. -/
def encodeI (items : List (Active k)) (x : IControl k) : Nat :=
  encode (intervalSizes k items) (x.state.val :: idxOfNext x.next :: x.seen :: x.controls)

/-- Well-formed interval controls: seen bit, and one in-range control per item. -/
def ICOK (items : List (Active k)) (x : IControl k) : Prop :=
  x.seen < 2 ∧ x.controls.length = items.length ∧
    ∀ i (hi : i < x.controls.length) (hj : i < items.length), x.controls[i] < (items[i]).1.size

theorem intervalSizes_pos (items : List (Active k)) (x : IControl k) (hx : ICOK items x) :
    ∀ s ∈ intervalSizes k items, 0 < s := by
  intro s hs
  simp only [intervalSizes, List.mem_cons, List.mem_map] at hs
  rcases hs with rfl | rfl | rfl | ⟨a, ha, rfl⟩
  · exact Nat.lt_of_le_of_lt (Nat.zero_le _) x.state.isLt
  · decide
  · decide
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have := hx.2.2 i (by rw [hx.2.1]; exact hi) hi
    omega

theorem encodeI_digits (items : List (Active k)) (x : IControl k) (hx : ICOK items x) :
    digits (intervalSizes k items) (encodeI items x) =
      x.state.val :: idxOfNext x.next :: x.seen :: x.controls := by
  apply digits_encode (intervalSizes_pos items x hx)
  · simp [intervalSizes, hx.2.1]
  · intro i hi hs
    match i with
    | 0 => exact x.state.isLt
    | 1 => exact idxOfNext_lt _
    | 2 => exact hx.1
    | i + 3 =>
      simp only [List.getElem_cons_succ, intervalSizes, List.getElem_map]
      exact hx.2.2 i (by simpa using hi) (by simpa [intervalSizes] using hs)

theorem encodeI_lt (items : List (Active k)) (x : IControl k) (hx : ICOK items x) :
    encodeI items x < intervalSize k items := by
  apply encode_lt (intervalSizes_pos items x hx)
  · simp [intervalSizes, hx.2.1]
  · intro i hi hs
    match i with
    | 0 => exact x.state.isLt
    | 1 => exact idxOfNext_lt _
    | 2 => exact hx.1
    | i + 3 =>
      simp only [List.getElem_cons_succ, intervalSizes, List.getElem_map]
      exact hx.2.2 i (by simpa using hi) (by simpa [intervalSizes] using hs)

theorem decodeI_encodeI (items : List (Active k)) (x : IControl k) (hx : ICOK items x) :
    decodeI items (encodeI items x) = some x := by
  unfold decodeI
  rw [encodeI_digits items x hx]
  simp only [stateOf_val, nextOfIdx_idxOfNext]
  rfl

/-! ## Sums -/

theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum := by
  intro l
  induction l with
  | nil => intro x h; simp at h
  | cons y l ih =>
    intro x h
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h; simp; omega

theorem sum_map_le_sum_map {α : Type} {f g : α → Nat} : ∀ {l : List α}, (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons y l ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := h y (List.mem_cons_self ..)
    omega

/-! ## The step label between two nodes -/

/-- A labelled step between `Nat` nodes. -/
def NStepL (G : Graph k) (O : Observer k) (x y : NNode) (l : Label) : Prop :=
  ∃ (hx : x.1 < G.size) (hy : y.1 < G.size) (hs : x.2 < O.size) (ht : y.2 < O.size),
    G.edge ⟨x.1, hx⟩ l = some ⟨y.1, hy⟩ ∧
      (⟨y.2, ht⟩ : Fin O.size) ∈ O.move ⟨x.2, hs⟩ (G.colour ⟨x.1, hx⟩) l (G.colour ⟨y.1, hy⟩)

def labelOK (G : Graph k) (O : Observer k) (x y : NNode) (l : Label) : Bool :=
  if hx : x.1 < G.size then
    if hy : y.1 < G.size then
      if hs : x.2 < O.size then
        if ht : y.2 < O.size then
          decide (G.edge ⟨x.1, hx⟩ l = some ⟨y.1, hy⟩) &&
            decide ((⟨y.2, ht⟩ : Fin O.size) ∈ O.move ⟨x.2, hs⟩ (G.colour ⟨x.1, hx⟩) l (G.colour ⟨y.1, hy⟩))
        else false
      else false
    else false
  else false

theorem labelOK_iff {G : Graph k} {O : Observer k} {x y : NNode} {l : Label} :
    labelOK G O x y l = true ↔ NStepL G O x y l := by
  unfold labelOK NStepL
  by_cases hx : x.1 < G.size
  · by_cases hy : y.1 < G.size
    · by_cases hs : x.2 < O.size
      · by_cases ht : y.2 < O.size
        · simp only [dif_pos hx, dif_pos hy, dif_pos hs, dif_pos ht, Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨hx, hy, hs, ht, h1, h2⟩
          · rintro ⟨_, _, _, _, h1, h2⟩; exact ⟨h1, h2⟩
        · simp only [dif_pos hx, dif_pos hy, dif_pos hs, dif_neg ht, Bool.false_eq_true, false_iff]
          rintro ⟨_, _, _, ht', -⟩; exact ht ht'
      · simp only [dif_pos hx, dif_pos hy, dif_neg hs, Bool.false_eq_true, false_iff]
        rintro ⟨_, _, hs', -⟩; exact hs hs'
    · simp only [dif_pos hx, dif_neg hy, Bool.false_eq_true, false_iff]
      rintro ⟨_, hy', -⟩; exact hy hy'
  · simp only [dif_neg hx, Bool.false_eq_true, false_iff]
    rintro ⟨hx', -⟩; exact hx hx'

def allLabels : List Label := [.F, .S, .K false, .K true]

theorem mem_allLabels (l : Label) : l ∈ allLabels := by
  cases l with
  | F => simp [allLabels]
  | S => simp [allLabels]
  | K b => cases b <;> simp [allLabels]

/-- A label realising the step from `x` to `y` (`F` if there is none). -/
def stepLabel (G : Graph k) (O : Observer k) (x y : NNode) : Label :=
  (allLabels.find? (labelOK G O x y)).getD .F

theorem nstepL_of_nstep {G : Graph k} {O : Observer k} {x y : NNode} (h : NStep G O x y) :
    ∃ l, NStepL G O x y l := by
  obtain ⟨hx, hy, hs, ht, l, he, hm, -⟩ := h
  exact ⟨l, hx, hy, hs, ht, he, hm⟩

theorem stepLabel_spec {G : Graph k} {O : Observer k} {x y : NNode} (h : NStep G O x y) :
    NStepL G O x y (stepLabel G O x y) := by
  obtain ⟨l, hl⟩ := nstepL_of_nstep h
  unfold stepLabel
  cases hf : allLabels.find? (labelOK G O x y) with
  | none =>
    have := (List.find?_eq_none.mp hf) l (mem_allLabels l)
    exact absurd (labelOK_iff.mpr hl) this
  | some l' =>
    exact labelOK_iff.mp (List.find?_some hf)

theorem stepLabel_eq {G : Graph k} {O : Observer k} {x y : NNode} (h : NStep G O x y) {l₀ : Label}
    (huniq : ∀ l, NStepL G O x y l → l = l₀) : stepLabel G O x y = l₀ :=
  huniq _ (stepLabel_spec h)

/-! ## The coverage data: a model of the clause on the extension with one chain per atom -/

/-- Observer, source and target of atom `ai` (defaults for out-of-range indices). -/
def obsAt (c : Clause k) (ai : Nat) : Observer k :=
  match c.atoms[ai]? with
  | some atm => atm.observer
  | none => oneEdge .F

def srcAt (c : Clause k) (ai : Nat) : Nat :=
  match c.atoms[ai]? with
  | some atm => atm.source.val
  | none => 0

def tgtAt (c : Clause k) (ai : Nat) : Nat :=
  match c.atoms[ai]? with
  | some atm => atm.target.val
  | none => 0

theorem obsAt_eq {c : Clause k} {ai : Nat} (h : ai < c.atoms.length) :
    obsAt c ai = (c.atoms[ai]).observer := by
  simp [obsAt, List.getElem?_eq_getElem h]

theorem srcAt_eq {c : Clause k} {ai : Nat} (h : ai < c.atoms.length) :
    srcAt c ai = (c.atoms[ai]).source.val := by
  simp [srcAt, List.getElem?_eq_getElem h]

theorem tgtAt_eq {c : Clause k} {ai : Nat} (h : ai < c.atoms.length) :
    tgtAt c ai = (c.atoms[ai]).target.val := by
  simp [tgtAt, List.getElem?_eq_getElem h]

/-- A model `τ` of the clause on the extension graph together with a product-simple
chain for every atom. -/
structure Cov (I : Instance k) (B : Reference k) (E : Ext I B) (c : Clause k) where
  τ : Fin c.vars → Fin (prefixGraph I E.C).size
  tests : ∀ t ∈ c.tests, t.2 ((prefixGraph I E.C).colour (τ t.1)) = true
  equal : ∀ e ∈ c.equal, τ e.1 = τ e.2
  unequal : ∀ e ∈ c.unequal, τ e.1 ≠ τ e.2
  chain : Nat → List NNode
  chain_consec : ∀ ai, ai < c.atoms.length →
    Consec (NStep (prefixGraph I E.C) (obsAt c ai)) (chain ai)
  chain_allowed : ∀ ai, ai < c.atoms.length → ∀ x ∈ chain ai, NAllowed (prefixGraph I E.C) (obsAt c ai) x
  chain_head : ∀ ai (h : ai < c.atoms.length), ∃ q ∈ (obsAt c ai).initial,
    (chain ai).head? = some ((τ (c.atoms[ai]).source).val, q.val)
  chain_last : ∀ ai (h : ai < c.atoms.length), ∃ p ∈ (obsAt c ai).final,
    (chain ai).getLast? = some ((τ (c.atoms[ai]).target).val, p.val)
  chain_visits : ∀ ai, ai < c.atoms.length →
    visitsN (B.word.length + 1) (chain ai) ≤ (obsAt c ai).size

namespace Cov
variable {I : Instance k} {B : Reference k} {E : Ext I B} {c : Clause k} (X : Cov I B E c)

/-! ### Blocks -/

def segs (ai : Nat) : List (List NNode) := segments B.word.length (X.chain ai)

def segCount (ai : Nat) : Nat := (X.segs ai).length

def blk (ai si : Nat) : List NNode := (X.segs ai).getD si []

/-- A uniform upper bound on the block counts, used for the core-variable layout. -/
def K : Nat := ((List.range c.atoms.length).map X.segCount).sum

/-! ### Marks -/

/-- All positions that must become marks: the first fresh vertex, the endpoint, the
fresh variable positions, and both endpoints of every fresh block. -/
def rawMarks : List Nat :=
  [B.word.length + 1, E.N] ++
    (List.finRange c.vars).filterMap (fun v => if B.word.length < (X.τ v).val then some (X.τ v).val else none) ++
    (List.range c.atoms.length).flatMap fun ai =>
      (X.segs ai).flatMap fun s => if isFresh B.word.length s then [hdPos s, lastPos s] else []

def M : List Nat := marksOf E.N X.rawMarks

/-- Number of mark groups. -/
def n : Nat := X.M.length

/-- Group index of a mark position. -/
def idx (p : Nat) : Nat := idxM X.M p

/-- Position of group `g`. -/
def pos (g : Nat) : Nat := X.M.getD g 0

/-! ### Core variables -/

def cix (ai si side : Nat) : Nat := c.vars + (ai * X.K + si) * 2 + side

def coreVars : Nat := c.vars + c.atoms.length * X.K * 2

/-- Core index of the head of block `si` of atom `ai` (the atom's source for the first block). -/
def headIdx (ai si : Nat) : Nat := if si = 0 then srcAt c ai else X.cix ai si 0

/-- Core index of the last node of block `si` (the atom's target for the last block). -/
def lastIdx (ai si : Nat) : Nat := if si = X.segCount ai - 1 then tgtAt c ai else X.cix ai si 1

/-! ### Pieces -/

def lastN (s : List NNode) : NNode := (s.getLast?).getD (0, 0)

def blockPiece (ai si : Nat) (s : List NNode) : Piece :=
  if isFresh B.word.length s then
    ⟨.forward, X.idx (hdPos s), X.idx (lastPos s), hdCtl s, lastCtl s, .F⟩
  else ⟨.core, X.headIdx ai si, X.lastIdx ai si, hdCtl s, lastCtl s, .F⟩

def transPiece (ai si : Nat) (s t : List NNode) : Piece :=
  let x := lastN s
  let y := hdN t
  if x.1 ≤ B.word.length then
    ⟨.enter, X.lastIdx ai si, 0, x.2, y.2, stepLabel (prefixGraph I E.C) (obsAt c ai) x y⟩
  else if B.word.length < y.1 then
    ⟨.wrap, X.n - 1, 0, x.2, y.2, .K E.a⟩
  else
    ⟨.exit, X.idx x.1, X.headIdx ai (si + 1), x.2, y.2, stepLabel (prefixGraph I E.C) (obsAt c ai) x y⟩

def buildPieces (ai : Nat) : Nat → List (List NNode) → List Piece
  | _, [] => []
  | si, [s] => [X.blockPiece ai si s]
  | si, s :: t :: rest => X.blockPiece ai si s :: X.transPiece ai si s t :: buildPieces ai (si + 1) (t :: rest)

def pieces (ai : Nat) : List Piece := X.buildPieces ai 0 (X.segs ai)

/-! ### Seams -/

def blockSeams (ai si : Nat) (s : List NNode) : List (Nat × Nat × Nat × Nat) :=
  if isFresh B.word.length s then
    ((List.range X.n).filter fun g => decide (X.idx (hdPos s) < g ∧ g < X.idx (lastPos s))).map
      fun g => (ai, 2 * si, g, ctlAt s (X.pos g))
  else []

def seamsOf (ai : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range (X.segCount ai)).flatMap fun si => X.blockSeams ai si (X.blk ai si)

def seams : List (Nat × Nat × Nat × Nat) := (List.range c.atoms.length).flatMap X.seamsOf

/-! ### The diagram -/

def loc : List Loc :=
  (List.finRange c.vars).map fun v =>
    if B.word.length < (X.τ v).val then Loc.fresh (X.idx (X.τ v).val) else Loc.core v.val

def D : Diagram k where
  groups := X.n
  coreVars := X.coreVars
  loc := X.loc
  states := X.M.map E.C.label
  nextBits := X.M.map fun p => E.C.word[p]?
  firstBit := E.a
  oldEnd := colB I B B.word.length
  pieces := (List.range c.atoms.length).map X.pieces
  seams := X.seams

/-! ### The base assignment -/

/-- Base position of core variable `x`. -/
def corePos (x : Nat) : Nat :=
  if h : x < c.vars then min (X.τ ⟨x, h⟩).val B.word.length
  else
    let r := x - c.vars
    let ai := r / (X.K * 2)
    let si := (r % (X.K * 2)) / 2
    let side := r % 2
    min (if side = 0 then hdPos (X.blk ai si) else lastPos (X.blk ai si)) B.word.length

theorem corePos_le (x : Nat) : X.corePos x ≤ B.word.length := by
  unfold corePos
  split
  · exact Nat.min_le_right _ _
  · exact Nat.min_le_right _ _

/-- Value of the base assignment at variable index `v`. -/
def sigmaVal (v : Nat) : Nat :=
  if v = 0 then B.word.length
  else if v = 1 then failureParent B.word
  else if v < 2 + X.n then E.cur (X.pos (v - 2))
  else X.corePos (v - 2 - X.n)

theorem pos_le_N (g : Nat) : X.pos g ≤ E.N := by
  unfold pos
  rw [List.getD_eq_getElem?_getD]
  cases h : X.M[g]? with
  | none => exact Nat.zero_le _
  | some p => exact (mem_marksOf.mp (List.mem_of_getElem? h)).1

theorem sigmaVal_le (v : Nat) : X.sigmaVal v ≤ B.word.length := by
  unfold sigmaVal
  split
  · exact Nat.le_refl _
  · split
    · have := failureParent_take_le B.word B.word.length
      simpa using this
    · split
      · exact E.cur_le (X.pos_le_N _)
      · exact X.corePos_le _

/-- The base assignment on the compiled clause's variables. -/
def σ : Var X.D → Fin (prefixGraph I B).size :=
  fun v => ⟨X.sigmaVal v.val, Nat.lt_succ_of_le (X.sigmaVal_le v.val)⟩

end Cov

namespace Cov
variable {I : Instance k} {B : Reference k} {E : Ext I B} {c : Clause k} (X : Cov I B E c)

/-! ### Basic block facts -/

theorem blocks_segs {ai : Nat} (hai : ai < c.atoms.length) :
    Blocks (InBlock E (obsAt c ai)) (Link E (obsAt c ai)) (X.segs ai) :=
  segments_blocks B.word.length (X.chain_consec ai hai)

theorem segs_flatten (ai : Nat) : (X.segs ai).flatten = X.chain ai := segments_flatten _ _

theorem blk_eq {ai si : Nat} (hsi : si < X.segCount ai) : X.blk ai si = (X.segs ai)[si] := by
  unfold blk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsi, Option.getD_some]

theorem blk_mem {ai si : Nat} (hsi : si < X.segCount ai) : X.blk ai si ∈ X.segs ai := by
  rw [X.blk_eq hsi]; exact List.getElem_mem hsi

theorem blk_ne_nil {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai) :
    X.blk ai si ≠ [] :=
  blocks_mem_ne_nil (X.blocks_segs hai) _ (X.blk_mem hsi)

theorem blk_consec {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai) :
    Consec (InBlock E (obsAt c ai)) (X.blk ai si) :=
  blocks_mem_consec (X.blocks_segs hai) _ (X.blk_mem hsi)

theorem blk_sub_chain {ai si : Nat} (hsi : si < X.segCount ai) {x : NNode} (hx : x ∈ X.blk ai si) :
    x ∈ X.chain ai := by
  rw [← X.segs_flatten ai]
  exact List.mem_flatten.mpr ⟨_, X.blk_mem hsi, hx⟩

theorem blk_allowed {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai) {x : NNode}
    (hx : x ∈ X.blk ai si) : NAllowed (prefixGraph I E.C) (obsAt c ai) x :=
  X.chain_allowed ai hai x (X.blk_sub_chain hsi hx)

theorem blk_pos_le {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai) {x : NNode}
    (hx : x ∈ X.blk ai si) : x.1 ≤ E.N := by
  have := (nallowed_bounds (X.blk_allowed hai hsi hx)).1
  change x.1 < E.N + 1 at this
  omega

theorem blk_ctl_lt {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai) {x : NNode}
    (hx : x ∈ X.blk ai si) : x.2 < (obsAt c ai).size :=
  (nallowed_bounds (X.blk_allowed hai hsi hx)).2

theorem blk_old {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : ¬ isFresh B.word.length (X.blk ai si) = true) : ∀ x ∈ X.blk ai si, x.1 ≤ B.word.length := by
  apply consec_compat_old (X.blk_consec hai hsi)
  simpa [isFresh] using hf

theorem blk_fresh_pos {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) {i : Nat} (hi : i < (X.blk ai si).length) :
    ((X.blk ai si)[i]).1 = hdPos (X.blk ai si) + i :=
  consec_compat_fresh (X.blk_consec hai hsi) (by simpa [isFresh] using hf) i hi

theorem blk_fresh_lastPos {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) :
    lastPos (X.blk ai si) = hdPos (X.blk ai si) + ((X.blk ai si).length - 1) :=
  fresh_block_lastPos (X.blk_ne_nil hai hsi) (X.blk_consec hai hsi) (by simpa [isFresh] using hf)

theorem hdN_mem {s : List NNode} (hne : s ≠ []) : hdN s ∈ s := by
  cases s with
  | nil => exact absurd rfl hne
  | cons x s => exact List.mem_cons_self ..

theorem lastN_mem {s : List NNode} (hne : s ≠ []) : lastN s ∈ s := by
  unfold lastN
  rw [List.getLast?_eq_some_getLast hne]
  exact List.getLast_mem hne

theorem head?_eq_hdN {s : List NNode} (hne : s ≠ []) : s.head? = some (hdN s) := by
  cases s with
  | nil => exact absurd rfl hne
  | cons x s => rfl

theorem getLast?_eq_lastN {s : List NNode} (hne : s ≠ []) : s.getLast? = some (lastN s) := by
  unfold lastN
  rw [List.getLast?_eq_some_getLast hne]
  rfl

theorem hdPos_hdN (s : List NNode) : hdPos s = (hdN s).1 := by
  cases s with
  | nil => rfl
  | cons x s => rfl

theorem hdCtl_hdN (s : List NNode) : hdCtl s = (hdN s).2 := by
  cases s with
  | nil => rfl
  | cons x s => rfl

theorem lastPos_lastN {s : List NNode} (hne : s ≠ []) : lastPos s = (lastN s).1 := by
  rw [lastPos, getLast?_eq_lastN hne]; rfl

theorem lastCtl_lastN {s : List NNode} (hne : s ≠ []) : lastCtl s = (lastN s).2 := by
  rw [lastCtl, getLast?_eq_lastN hne]; rfl

/-- The link between consecutive blocks, by index. -/
theorem blocks_link_idx {R Q : NNode → NNode → Prop} : ∀ {segs : List (List NNode)},
    Blocks R Q segs → ∀ si (h : si + 1 < segs.length), Q (lastN segs[si]) (hdN segs[si + 1]) := by
  intro segs
  induction segs with
  | nil => intro _ si h; simp at h
  | cons s rest ih =>
    intro hb si h
    cases rest with
    | nil => simp at h
    | cons t rest =>
      cases si with
      | zero =>
        have hs := blocks_head_ne_nil hb
        have ht := blocks_head_ne_nil (blocks_tail hb)
        exact blocks_link hb (getLast?_eq_lastN hs) (head?_eq_hdN ht)
      | succ si =>
        exact ih (blocks_tail hb) si (by simpa using h)

theorem blk_link {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si + 1 < X.segCount ai) :
    Link E (obsAt c ai) (lastN (X.blk ai si)) (hdN (X.blk ai (si + 1))) := by
  rw [X.blk_eq (Nat.lt_of_succ_lt hsi), X.blk_eq hsi]
  exact blocks_link_idx (X.blocks_segs hai) si hsi

theorem segCount_pos {ai : Nat} (hai : ai < c.atoms.length) : 0 < X.segCount ai := by
  obtain ⟨q, -, hq⟩ := X.chain_head ai hai
  have hne : X.chain ai ≠ [] := by
    intro h; rw [h] at hq; simp at hq
  unfold segCount segs
  apply List.length_pos_iff.mpr
  intro h
  exact hne ((segments_eq_nil_iff _ _).mp h)

theorem blk_zero_head {ai : Nat} (hai : ai < c.atoms.length) :
    (X.blk ai 0).head? = (X.chain ai).head? := by
  have hpos := X.segCount_pos hai
  rw [← X.segs_flatten ai]
  cases hs : X.segs ai with
  | nil => unfold segCount at hpos; rw [hs] at hpos; simp at hpos
  | cons s rest =>
    have hne : s ≠ [] := by
      have := X.blocks_segs hai; rw [hs] at this; exact blocks_head_ne_nil this
    rw [flatten_head? hne]
    show ((X.segs ai).getD 0 []).head? = s.head?
    rw [hs]; rfl

theorem blk_last_last {ai : Nat} (hai : ai < c.atoms.length) :
    (X.blk ai (X.segCount ai - 1)).getLast? = (X.chain ai).getLast? := by
  have hpos := X.segCount_pos hai
  have hlen : (X.segs ai).length = X.segCount ai := rfl
  rw [← X.segs_flatten ai]
  have hne := blocks_mem_ne_nil (X.blocks_segs hai)
  rw [flatten_getLast? hne (s := X.blk ai (X.segCount ai - 1))]
  rw [X.blk_eq (by omega), List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rfl

/-! ### Marks -/

theorem m1_mem_raw : B.word.length + 1 ∈ X.rawMarks := by simp [rawMarks]

theorem N_mem_raw : E.N ∈ X.rawMarks := by simp [rawMarks]

theorem var_mem_raw {v : Fin c.vars} (hv : B.word.length < (X.τ v).val) : (X.τ v).val ∈ X.rawMarks := by
  simp only [rawMarks, List.append_assoc, List.mem_append, List.mem_cons, List.mem_filterMap]
  right; left
  exact ⟨v, List.mem_finRange v, by simp [hv]⟩

theorem blk_hd_mem_raw {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) : hdPos (X.blk ai si) ∈ X.rawMarks := by
  simp only [rawMarks, List.append_assoc, List.mem_append, List.mem_cons, List.mem_flatMap]
  right; right
  exact ⟨ai, List.mem_range.mpr hai, X.blk ai si, X.blk_mem hsi, by simp [hf]⟩

theorem blk_last_mem_raw {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) : lastPos (X.blk ai si) ∈ X.rawMarks := by
  simp only [rawMarks, List.append_assoc, List.mem_append, List.mem_cons, List.mem_flatMap]
  right; right
  exact ⟨ai, List.mem_range.mpr hai, X.blk ai si, X.blk_mem hsi, by simp [hf]⟩

theorem raw_gt_m : ∀ p ∈ X.rawMarks, B.word.length < p := by
  intro p hp
  simp only [rawMarks, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_filterMap, List.mem_flatMap, List.mem_range] at hp
  rcases hp with (rfl | rfl) | ⟨v, -, hv⟩ | ⟨ai, hai, s, hs, hps⟩
  · omega
  · exact E.m_lt_N
  · split at hv
    · rename_i h; simp only [Option.some.injEq] at hv; omega
    · simp at hv
  · split at hps
    · rename_i hf
      obtain ⟨si, hsi, hse⟩ := List.getElem_of_mem hs
      have hsi' : si < X.segCount ai := hsi
      have hb : X.blk ai si = s := (X.blk_eq hsi').trans hse
      subst hb
      simp only [isFresh, decide_eq_true_eq] at hf
      simp only [List.mem_cons, List.mem_singleton] at hps
      rcases hps with rfl | rfl | h
      · exact hf
      · rw [X.blk_fresh_lastPos hai hsi' (by simpa [isFresh] using hf)]; omega
      · simp at h
    · simp at hps

theorem raw_le_N : ∀ p ∈ X.rawMarks, p ≤ E.N := by
  intro p hp
  simp only [rawMarks, List.append_assoc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_filterMap, List.mem_flatMap, List.mem_range] at hp
  rcases hp with (rfl | rfl) | ⟨v, -, hv⟩ | ⟨ai, hai, s, hs, hps⟩
  · exact E.m_lt_N
  · exact Nat.le_refl _
  · split at hv
    · simp only [Option.some.injEq] at hv
      rw [← hv]
      have := (X.τ v).isLt
      change (X.τ v).val < E.N + 1 at this
      omega
    · simp at hv
  · split at hps
    · rename_i hf
      obtain ⟨si, hsi, hse⟩ := List.getElem_of_mem hs
      have hsi' : si < X.segCount ai := hsi
      have hb : X.blk ai si = s := (X.blk_eq hsi').trans hse
      subst hb
      have hne := X.blk_ne_nil hai hsi'
      simp only [List.mem_cons, List.mem_singleton] at hps
      rcases hps with rfl | rfl | h
      · rw [hdPos_hdN]; exact X.blk_pos_le hai hsi' (hdN_mem hne)
      · rw [lastPos_lastN hne]; exact X.blk_pos_le hai hsi' (lastN_mem hne)
      · simp at h
    · simp at hps

theorem mem_M {p : Nat} : p ∈ X.M ↔ p ∈ X.rawMarks := by
  unfold M
  rw [mem_marksOf]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨X.raw_le_N p h, h⟩

theorem M_gt_m {p : Nat} (hp : p ∈ X.M) : B.word.length < p := X.raw_gt_m p (X.mem_M.mp hp)

theorem M_le_N {p : Nat} (hp : p ∈ X.M) : p ≤ E.N := X.raw_le_N p (X.mem_M.mp hp)

theorem m1_mem_M : B.word.length + 1 ∈ X.M := X.mem_M.mpr X.m1_mem_raw

theorem N_mem_M : E.N ∈ X.M := X.mem_M.mpr X.N_mem_raw

theorem n_pos : 0 < X.n := List.length_pos_of_mem X.m1_mem_M

theorem idx_lt {p : Nat} (hp : p ∈ X.M) : X.idx p < X.n := idxM_lt hp

theorem pos_idx {p : Nat} (hp : p ∈ X.M) : X.pos (X.idx p) = p := by
  unfold pos idx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (idxM_lt hp), Option.getD_some]
  exact getElem_idxM hp

theorem pos_eq {g : Nat} (hg : g < X.n) : X.pos g = X.M[g] := by
  unfold pos
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg, Option.getD_some]

theorem pos_mem {g : Nat} (hg : g < X.n) : X.pos g ∈ X.M := by
  rw [X.pos_eq hg]; exact List.getElem_mem hg

theorem idx_pos {g : Nat} (hg : g < X.n) : X.idx (X.pos g) = g := by
  rw [X.pos_eq hg]; exact idxM_getElem hg

theorem idx_m1 : X.idx (B.word.length + 1) = 0 := by
  apply idxM_min X.m1_mem_M
  intro q hq
  exact X.M_gt_m hq

theorem idx_N : X.idx E.N = X.n - 1 := by
  apply idxM_max X.N_mem_M
  intro q hq
  exact X.M_le_N hq

theorem pos_zero : X.pos 0 = B.word.length + 1 := by
  have := X.pos_idx X.m1_mem_M
  rw [X.idx_m1] at this
  exact this

theorem pos_last : X.pos (X.n - 1) = E.N := by
  have := X.pos_idx X.N_mem_M
  rw [X.idx_N] at this
  exact this

theorem pos_gt_m {g : Nat} (hg : g < X.n) : B.word.length < X.pos g := X.M_gt_m (X.pos_mem hg)

theorem pos_strict {g h : Nat} (hgh : g < h) (hh : h < X.n) : X.pos g < X.pos h := by
  rw [X.pos_eq (Nat.lt_trans hgh hh), X.pos_eq hh]
  exact marksOf_lt _ _ hgh

theorem pos_mono {g h : Nat} (hgh : g ≤ h) (hh : h < X.n) : X.pos g ≤ X.pos h := by
  rcases Nat.lt_or_eq_of_le hgh with h' | h'
  · exact Nat.le_of_lt (X.pos_strict h' hh)
  · subst h'; exact Nat.le_refl _

theorem pos_lt_N {g : Nat} (hg : g < X.n - 1) : X.pos g < E.N := by
  have := X.pos_strict hg (by have := X.n_pos; omega)
  rw [X.pos_last] at this
  exact this

theorem idx_mono {p q : Nat} (hp : p ∈ X.M) (hq : q ∈ X.M) (hpq : p < q) : X.idx p < X.idx q :=
  idxM_mono hp hq hpq

theorem idx_le {p q : Nat} (hp : p ∈ X.M) (hq : q ∈ X.M) (hpq : p ≤ q) : X.idx p ≤ X.idx q :=
  idxM_le_of_le hp hq hpq

theorem idx_inj {p q : Nat} (hp : p ∈ X.M) (hq : q ∈ X.M) (h : X.idx p = X.idx q) : p = q :=
  idxM_injective hp hq h

theorem n_eq_one_iff : X.n = 1 ↔ E.N = B.word.length + 1 := by
  constructor
  · intro h
    have h1 := X.pos_zero
    have h2 := X.pos_last
    rw [h] at h2
    simp only [Nat.sub_self] at h2
    rw [h1] at h2
    exact h2.symm
  · intro h
    have hidx := X.idx_N
    rw [h, X.idx_m1] at hidx
    have := X.n_pos
    omega

theorem var_mem_M {v : Fin c.vars} (hv : B.word.length < (X.τ v).val) : (X.τ v).val ∈ X.M :=
  X.mem_M.mpr (X.var_mem_raw hv)

theorem blk_hd_mem_M {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) : hdPos (X.blk ai si) ∈ X.M :=
  X.mem_M.mpr (X.blk_hd_mem_raw hai hsi hf)

theorem blk_last_mem_M {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) : lastPos (X.blk ai si) ∈ X.M :=
  X.mem_M.mpr (X.blk_last_mem_raw hai hsi hf)

/-! ### Diagram fields -/

theorem D_groups : X.D.groups = X.n := rfl

theorem D_coreVars : X.D.coreVars = X.coreVars := rfl

theorem D_firstBit : X.D.firstBit = E.a := rfl

theorem D_oldEnd : X.D.oldEnd = colB I B B.word.length := rfl

theorem markState_eq {g : Nat} (hg : g < X.n) : markState X.D g = E.C.label (X.pos g) := by
  unfold markState
  show (X.M.map E.C.label).getD g _ = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hg, Option.map_some,
    Option.getD_some, X.pos_eq hg]

theorem nextOf_eq {g : Nat} (hg : g < X.n) : nextOf X.D g = E.C.word[X.pos g]? := by
  unfold nextOf
  show (X.M.map fun p => E.C.word[p]?).getD g none = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hg, Option.map_some,
    Option.getD_some, X.pos_eq hg]

theorem fm_eq {g : Nat} (hg : g < X.n) (col : Colour k) :
    fm I X.D g col = freshMap I (E.C.label (X.pos g)) (E.C.word[X.pos g]?) col := by
  unfold fm
  rw [X.markState_eq hg, X.nextOf_eq hg]

/-- The compiler's fresh colour map at a mark, read at the cursor, is the mark's colour. -/
theorem fm_pos {g : Nat} (hg : g < X.n) :
    fm I X.D g (colB I B (E.cur (X.pos g))) = colB I E.C (X.pos g) := by
  rw [X.fm_eq hg, E.colC_fresh (X.pos_gt_m hg) (X.pos_le_N g)]

theorem piecesOf_eq {ai : Nat} (hai : ai < c.atoms.length) : piecesOf X.D ai = X.pieces ai := by
  unfold piecesOf
  show ((List.range c.atoms.length).map X.pieces).getD ai [] = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hai),
    Option.map_some, Option.getD_some, List.getElem_range]

theorem locOf_eq {v : Nat} (hv : v < c.vars) :
    locOf X.D v = if B.word.length < (X.τ ⟨v, hv⟩).val then Loc.fresh (X.idx (X.τ ⟨v, hv⟩).val)
      else Loc.core v := by
  unfold locOf
  show X.loc.getD v _ = _
  unfold loc
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simpa using hv),
    Option.map_some, Option.getD_some, List.getElem_finRange]
  rfl

/-! ### The assignment -/

theorem σ_val (v : Var X.D) : (X.σ v).val = X.sigmaVal v.val := rfl

theorem σ_end : (X.σ (endVar X.D)).val = B.word.length := rfl

theorem σ_init : (X.σ (initVar X.D)).val = failureParent B.word := rfl

theorem σ_z {g : Nat} (hg : g < X.n) : (X.σ (zVar X.D g)).val = E.cur (X.pos g) := by
  rw [σ_val, zVar, dif_pos (show g < X.D.groups from hg)]
  show X.sigmaVal (2 + g) = E.cur (X.pos g)
  unfold sigmaVal
  rw [if_neg (by omega), if_neg (by omega), if_pos (show 2 + g < 2 + X.n by omega),
    show 2 + g - 2 = g by omega]

theorem σ_core {x : Nat} (hx : x < X.coreVars) : (X.σ (coreVar X.D x)).val = X.corePos x := by
  rw [σ_val, coreVar, dif_pos (show x < X.D.coreVars from hx)]
  show X.sigmaVal (2 + X.n + x) = X.corePos x
  unfold sigmaVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (show ¬ (2 + X.n + x < 2 + X.n) by omega),
    show 2 + X.n + x - 2 - X.n = x by omega]

theorem corePos_var {v : Nat} (hv : v < c.vars) (hold : (X.τ ⟨v, hv⟩).val ≤ B.word.length) :
    X.corePos v = (X.τ ⟨v, hv⟩).val := by
  unfold corePos
  rw [dif_pos hv]
  exact Nat.min_eq_left hold

theorem segCount_le_K {ai : Nat} (hai : ai < c.atoms.length) : X.segCount ai ≤ X.K := by
  unfold K
  apply le_sum_of_mem
  exact List.mem_map.mpr ⟨ai, List.mem_range.mpr hai, rfl⟩

theorem cix_decode {ai si side : Nat} (hsi : si < X.K) (hside : side < 2) :
    (X.cix ai si side - c.vars) / (X.K * 2) = ai ∧
      ((X.cix ai si side - c.vars) % (X.K * 2)) / 2 = si ∧ (X.cix ai si side - c.vars) % 2 = side := by
  have hK : 0 < X.K := by omega
  have e : X.K * 2 * ai = ai * X.K * 2 := by
    rw [Nat.mul_comm X.K 2, Nat.mul_assoc, Nat.mul_comm X.K ai, Nat.mul_comm 2 (ai * X.K)]
  have e3 : X.K * ai = ai * X.K := Nat.mul_comm _ _
  have hr : X.cix ai si side - c.vars = (si * 2 + side) + (X.K * 2) * ai := by
    unfold cix
    omega
  have hlt : si * 2 + side < X.K * 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, Nat.zero_add]
  · rw [hr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, show si * 2 + side = side + 2 * si by omega,
      Nat.add_mul_div_left _ _ (by decide : 0 < 2), Nat.div_eq_of_lt hside, Nat.zero_add]
  · rw [hr, show si * 2 + side + X.K * 2 * ai = side + 2 * (si + X.K * ai) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hside]

theorem corePos_cix_hd {ai si : Nat} (hsi : si < X.K) :
    X.corePos (X.cix ai si 0) = min (hdPos (X.blk ai si)) B.word.length := by
  have hge : ¬ X.cix ai si 0 < c.vars := by unfold cix; omega
  obtain ⟨h1, h2, h3⟩ := X.cix_decode (ai := ai) hsi (by decide : 0 < 2)
  unfold corePos
  rw [dif_neg hge]
  simp only [h1, h2, h3]
  rfl

theorem corePos_cix_last {ai si : Nat} (hsi : si < X.K) :
    X.corePos (X.cix ai si 1) = min (lastPos (X.blk ai si)) B.word.length := by
  have hge : ¬ X.cix ai si 1 < c.vars := by unfold cix; omega
  obtain ⟨h1, h2, h3⟩ := X.cix_decode (ai := ai) hsi (by decide : 1 < 2)
  unfold corePos
  rw [dif_neg hge]
  simp only [h1, h2, h3]
  rfl

theorem cix_lt {ai si side : Nat} (hai : ai < c.atoms.length) (hsi : si < X.K) (hside : side < 2) :
    X.cix ai si side < X.coreVars := by
  unfold cix coreVars
  have h1 : (ai * X.K + si) * 2 + side < (ai * X.K + X.K) * 2 := by omega
  have h2 : (ai * X.K + X.K) * 2 = (ai + 1) * X.K * 2 := by rw [Nat.succ_mul]
  have h3 : (ai + 1) * X.K * 2 ≤ c.atoms.length * X.K * 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hai)
  omega

theorem vars_le_coreVars : c.vars ≤ X.coreVars := by unfold coreVars; omega

end Cov

/-! ## Semantics of old steps: transport to the base graph -/

/-- Recover a `Fin`-valued edge of any graph from its position value. -/
theorem fin_edge_of_map_val {G : Graph k} {u : Fin G.size} {l : Label} {j : Nat}
    (h : (G.edge u l).map Fin.val = some j) (hj : j < G.size) : G.edge u l = some ⟨j, hj⟩ := by
  cases he : G.edge u l with
  | none => rw [he] at h; simp at h
  | some v =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    congr 1
    exact Fin.ext h

section Transport
variable {I : Instance k} {B : Reference k} (E : Ext I B) (o : Observer k)

/-- An old node of the extension graph, as a node of the base graph. -/
def castB (x : NNode) (hx : x.1 ≤ B.word.length) (hs : x.2 < o.size) :
    Node (prefixGraph I B) (coreObs o E.a) :=
  (⟨x.1, Nat.lt_succ_of_le hx⟩, ⟨x.2, hs⟩)

theorem colour_old {j : Nat} (hj : j ≤ B.word.length) (hjC : j < (prefixGraph I E.C).size) :
    (prefixGraph I E.C).colour ⟨j, hjC⟩ =
      coreMap E.a ((prefixGraph I B).colour ⟨j, Nat.lt_succ_of_le hj⟩) := by
  rw [prefixGraph_colour, prefixGraph_colour]
  exact E.colC_old hj

theorem old_allowed_transport {x : NNode} (hx : x.1 ≤ B.word.length) (h : NAllowed (prefixGraph I E.C) o x) :
    ∃ hs : x.2 < o.size, Allowed (prefixGraph I B) (coreObs o E.a) (castB E o x hx hs) := by
  obtain ⟨hx', hs, ha⟩ := h
  refine ⟨hs, ?_⟩
  simp only [Allowed, coreObs, castB]
  simp only [Allowed] at ha
  rw [colour_old E hx hx'] at ha
  exact ha

/-- The position value of an edge of the extension graph. -/
theorem edge_pos {x : NNode} (hx : x.1 < (prefixGraph I E.C).size) {l : Label} {v : Fin (prefixGraph I E.C).size}
    (he : (prefixGraph I E.C).edge ⟨x.1, hx⟩ l = some v) :
    E.edge x.1 (Nat.le_of_lt_succ hx) l = some v.val := by
  rw [← E.edge_val (Nat.le_of_lt_succ hx) l]
  have : (⟨x.1, hx⟩ : Fin (prefixGraph I E.C).size) = ⟨x.1, Nat.lt_succ_of_le (Nat.le_of_lt_succ hx)⟩ := rfl
  rw [← this, he]; rfl

/-- An old-to-old step of the extension graph is a step of the core observer in the base. -/
theorem old_step_transport {x y : NNode} (hx : x.1 ≤ B.word.length) (hy : y.1 ≤ B.word.length)
    (h : NStep (prefixGraph I E.C) o x y) :
    ∃ (hs : x.2 < o.size) (ht : y.2 < o.size),
      Step (prefixGraph I B) (coreObs o E.a) (castB E o x hx hs) (castB E o y hy ht) := by
  obtain ⟨hx', hy', hs, ht, l, he, hm, ha⟩ := h
  refine ⟨hs, ht, ?_⟩
  have hxN : x.1 ≤ E.N := by have := E.m_lt_N; omega
  have hval : E.edge x.1 hxN l = some y.1 := edge_pos E hx' he
  have hB := edgeB_val I B (Nat.lt_succ_of_le hx) l
  -- the base edge and the exclusion of the endpoint's K_a edge
  have hedge : ¬ (x.1 = B.word.length ∧ l = .K E.a) ∧
      (prefixGraph I B).edge ⟨x.1, Nat.lt_succ_of_le hx⟩ l = some ⟨y.1, Nat.lt_succ_of_le hy⟩ := by
    cases l with
    | F =>
      refine ⟨by simp, ?_⟩
      rw [E.edge_F_old hx hxN] at hval
      simp only at hB
      apply fin_edge_of_map_val
      rw [hB]; exact hval
    | S =>
      refine ⟨by simp, ?_⟩
      rw [E.edge_S hxN] at hval
      have hlt : x.1 < E.N := by
        apply Classical.byContradiction
        intro hn
        rw [if_neg hn] at hval
        simp at hval
      rw [if_pos hlt] at hval
      have hy1 : x.1 + 1 = y.1 := Option.some.inj hval
      have hxm : x.1 < B.word.length := by omega
      simp only at hB
      rw [if_pos hxm] at hB
      apply fin_edge_of_map_val
      rw [hB, hy1]
    | K b =>
      simp only at hB
      by_cases hxm : x.1 = B.word.length
      · rw [E.edge_congr hxm hxN (Nat.le_of_lt E.m_lt_N), E.edge_K_m _ b] at hval
        have hba : ¬ b = E.a := by
          intro hba
          rw [if_pos hba] at hval
          have := Option.some.inj hval
          omega
        rw [if_neg hba] at hval
        refine ⟨fun h' => hba (Label.K.inj h'.2), ?_⟩
        apply fin_edge_of_map_val
        rw [hB, hxm]; exact hval
      · have hxlt : x.1 < B.word.length := Nat.lt_of_le_of_ne hx hxm
        rw [E.edge_K_old hxlt hxN b] at hval
        refine ⟨fun h' => hxm h'.1, ?_⟩
        apply fin_edge_of_map_val
        rw [hB]; exact hval
  obtain ⟨hex, heB⟩ := hedge
  refine ⟨l, heB, ?_, ?_⟩
  · -- the move of the core observer
    simp only [castB, coreObs]
    have hnot : ¬ (((prefixGraph I B).colour ⟨x.1, Nat.lt_succ_of_le hx⟩).isEnd = true ∧ l = .K E.a) := by
      intro h'
      apply hex
      refine ⟨?_, h'.2⟩
      have := h'.1
      rw [prefixGraph_colour] at this
      exact of_decide_eq_true this
    rw [if_neg hnot]
    rw [colour_old E hx hx', colour_old E hy hy'] at hm
    exact hm
  · obtain ⟨hs', hall⟩ := old_allowed_transport E o hy ⟨hy', ht, ha⟩
    exact hall

/-- Runs of an observer are runs of the observer with other initial/final controls. -/
theorem run_coreObs_slice {G : Graph k} (lc rc : Fin o.size) {a : Bool} {x y : Node G (coreObs o a)}
    (h : Run G (coreObs o a) x y) : Run G (coreObs (sliceObs o lc rc) a) x y := by
  induction h with
  | refl h => exact Run.refl h
  | step _ hs ih => exact Run.step ih hs

/-- An old block of the extension graph runs in the base graph under the core observer. -/
theorem old_block_run : ∀ {s : List NNode}, Consec (NStep (prefixGraph I E.C) o) s →
    (∀ x ∈ s, x.1 ≤ B.word.length) → (∀ x ∈ s, NAllowed (prefixGraph I E.C) o x) →
    ∀ {x y : NNode}, s.head? = some x → s.getLast? = some y →
    ∃ (hx : x.1 ≤ B.word.length) (hs : x.2 < o.size) (hy : y.1 ≤ B.word.length) (ht : y.2 < o.size),
      Run (prefixGraph I B) (coreObs o E.a) (castB E o x hx hs) (castB E o y hy ht) := by
  intro s
  induction s with
  | nil => intro _ _ _ x y hx; simp at hx
  | cons z s ih =>
    intro hc hold hall x y hx hy
    simp only [List.head?_cons, Option.some.injEq] at hx
    subst hx
    have hxold := hold z (List.mem_cons_self ..)
    obtain ⟨hs, hallx⟩ := old_allowed_transport E o hxold (hall z (List.mem_cons_self ..))
    cases s with
    | nil =>
      simp at hy; subst hy
      exact ⟨hxold, hs, hxold, hs, Run.refl hallx⟩
    | cons z' s' =>
      have hy' : (z' :: s').getLast? = some y := by simpa using hy
      obtain ⟨hz, hs', hyo, ht, hrun⟩ := ih hc.2 (fun w hw => hold w (List.mem_cons_of_mem _ hw))
        (fun w hw => hall w (List.mem_cons_of_mem _ hw)) rfl hy'
      obtain ⟨hs'', ht'', hstep⟩ := old_step_transport E o hxold hz hc.1
      refine ⟨hxold, hs'', hyo, ht, ?_⟩
      exact run_prepend _ _ hallx hstep hrun

end Transport

/-! ## Semantics of the transitions between blocks -/

section Transitions
variable {I : Instance k} {B : Reference k} (E : Ext I B) (o : Observer k)

/-- The colour of a node of the extension graph, by position. -/
theorem colour_C {j : Nat} (hj : j < (prefixGraph I E.C).size) :
    (prefixGraph I E.C).colour ⟨j, hj⟩ = colB I E.C j := rfl

theorem nstepL_edge {x y : NNode} {l : Label} (h : NStepL (prefixGraph I E.C) o x y l) :
    ∃ hx : x.1 ≤ E.N, E.edge x.1 hx l = some y.1 := by
  obtain ⟨hx, hy, hs, ht, he, hm⟩ := h
  exact ⟨Nat.le_of_lt_succ hx, edge_pos E hx he⟩

theorem nstepL_move {x y : NNode} {l : Label} (h : NStepL (prefixGraph I E.C) o x y l) :
    ∃ (hs : x.2 < o.size) (ht : y.2 < o.size),
      (⟨y.2, ht⟩ : Fin o.size) ∈ o.move ⟨x.2, hs⟩ (colB I E.C x.1) l (colB I E.C y.1) := by
  obtain ⟨hx, hy, hs, ht, he, hm⟩ := h
  exact ⟨hs, ht, hm⟩

theorem nstepL_bounds {x y : NNode} {l : Label} (h : NStepL (prefixGraph I E.C) o x y l) :
    x.1 ≤ E.N ∧ y.1 ≤ E.N := by
  obtain ⟨hx, hy, -, -, -, -⟩ := h
  exact ⟨Nat.le_of_lt_succ hx, Nat.le_of_lt_succ hy⟩

/-- The labels realising an entrance `m → m+1`. -/
theorem enter_label {x y : NNode} {l : Label} (h : NStepL (prefixGraph I E.C) o x y l)
    (hx : x.1 = B.word.length) (hy : y.1 = B.word.length + 1) : l = .S ∨ l = .K E.a := by
  obtain ⟨hxN, he⟩ := nstepL_edge E o h
  cases l with
  | F =>
    rw [E.edge_F_old (by omega) hxN] at he
    have h1 := Option.some.inj he
    have h2 := failureParent_take_le B.word x.1
    omega
  | S => exact Or.inl rfl
  | K b =>
    rw [E.edge_congr hx hxN (Nat.le_of_lt E.m_lt_N), E.edge_K_m _ b] at he
    by_cases hba : b = E.a
    · exact Or.inr (by rw [hba])
    · rw [if_neg hba] at he
      have h1 := Option.some.inj he
      have h2 := advance_le B.word B.word.length b
      omega

/-- An old-to-fresh link is the entrance. -/
theorem enter_facts {x y : NNode} (h : Link E o x y) (hx : x.1 ≤ B.word.length) :
    x.1 = B.word.length ∧ y.1 = B.word.length + 1 ∧
      (stepLabel (prefixGraph I E.C) o x y = .S ∨ stepLabel (prefixGraph I E.C) o x y = .K E.a) ∧
      ∃ (hs : x.2 < o.size) (ht : y.2 < o.size),
        (⟨y.2, ht⟩ : Fin o.size) ∈ o.move ⟨x.2, hs⟩ (colB I E.C B.word.length)
          (stepLabel (prefixGraph I E.C) o x y) (colB I E.C (B.word.length + 1)) := by
  have hc := compat_false_iff.mp h.2
  have hyfresh : B.word.length < y.1 := by
    apply Classical.byContradiction
    intro hn
    exact hc.1 ⟨hx, Nat.le_of_not_lt hn⟩
  obtain ⟨hx', hy', hs, ht, l, he, -, -⟩ := h.1
  obtain ⟨hxm, hym⟩ := RankQueryFirstReturn.old_to_fresh I E.C E.hm E.hr he hx hyfresh
  have hxm' : x.1 = B.word.length := hxm
  have hym' : y.1 = B.word.length + 1 := hym
  have hL := stepLabel_spec h.1
  refine ⟨hxm', hym', enter_label E o hL hxm' hym', ?_⟩
  obtain ⟨hs', ht', hm⟩ := nstepL_move E o hL
  rw [hxm', hym'] at hm
  exact ⟨hs', ht', hm⟩

/-- A fresh-to-fresh link is the endpoint wrap by `K a`. -/
theorem wrap_facts {x y : NNode} (h : Link E o x y) (hx : B.word.length < x.1) (hy : B.word.length < y.1) :
    x.1 = E.N ∧ y.1 = B.word.length + 1 ∧ stepLabel (prefixGraph I E.C) o x y = .K E.a ∧
      ∃ (hs : x.2 < o.size) (ht : y.2 < o.size),
        (⟨y.2, ht⟩ : Fin o.size) ∈ o.move ⟨x.2, hs⟩ (colB I E.C E.N) (.K E.a) (colB I E.C (B.word.length + 1)) := by
  have hc := compat_false_iff.mp h.2
  obtain ⟨hx', hy', hs, ht, l, he, -, -⟩ := h.1
  have hshape := RankQueryFirstReturn.fresh_edge_shape I E.C E.hm E.hr he hy
  have hxy : x.1 = E.N ∧ y.1 = B.word.length + 1 := by
    rcases hshape with h1 | h2
    · exact absurd ⟨hx, h1⟩ hc.2
    · exact h2
  obtain ⟨hxN, hym⟩ := hxy
  have huniq : ∀ l', NStepL (prefixGraph I E.C) o x y l' → l' = .K E.a := by
    intro l' hl'
    obtain ⟨hxN', he'⟩ := nstepL_edge E o hl'
    cases l' with
    | F =>
      rw [E.edge_F_fresh hx hxN'] at he'
      have h1 := Option.some.inj he'
      have h2 := E.cur_le hxN'
      omega
    | S =>
      rw [E.edge_S hxN'] at he'
      have hnot : ¬ x.1 < E.N := by omega
      rw [if_neg hnot] at he'
      simp at he'
    | K b =>
      rw [E.edge_congr hxN hxN' (Nat.le_refl _), E.edge_K_N b] at he'
      by_cases hba : b = E.a
      · rw [hba]
      · rw [if_neg hba] at he'
        have h1 := Option.some.inj he'
        have h2 := advance_le B.word B.word.length b
        omega
  have hlab := stepLabel_eq h.1 huniq
  have hL := stepLabel_spec h.1
  refine ⟨hxN, hym, hlab, ?_⟩
  obtain ⟨hs', ht', hm⟩ := nstepL_move E o hL
  rw [hxN, hym, hlab] at hm
  exact ⟨hs', ht', hm⟩

/-- A fresh-to-old link exits by `F` to the cursor or by a mismatched `K b` to the base edge. -/
theorem exit_facts {x y : NNode} (h : Link E o x y) (hx : B.word.length < x.1) (hy : y.1 ≤ B.word.length) :
    x.1 ≤ E.N ∧
      ((stepLabel (prefixGraph I E.C) o x y = .F ∧ y.1 = E.cur x.1) ∨
        (∃ b, stepLabel (prefixGraph I E.C) o x y = .K b ∧ y.1 = advance B.word (E.cur x.1) b ∧
          (x.1 < E.N → E.C.word[x.1]? ≠ some b) ∧ (x.1 = E.N → b ≠ E.a))) ∧
      ∃ (hs : x.2 < o.size) (ht : y.2 < o.size),
        (⟨y.2, ht⟩ : Fin o.size) ∈ o.move ⟨x.2, hs⟩ (colB I E.C x.1)
          (stepLabel (prefixGraph I E.C) o x y) (colB I E.C y.1) := by
  have hL := stepLabel_spec h.1
  obtain ⟨hxN, he⟩ := nstepL_edge E o hL
  refine ⟨hxN, ?_, nstepL_move E o hL⟩
  generalize hl : stepLabel (prefixGraph I E.C) o x y = l at he
  cases l with
  | F =>
    left
    refine ⟨rfl, ?_⟩
    rw [E.edge_F_fresh hx hxN] at he
    exact (Option.some.inj he).symm
  | S =>
    exfalso
    rw [E.edge_S hxN] at he
    by_cases hlt : x.1 < E.N
    · rw [if_pos hlt] at he
      have := Option.some.inj he
      omega
    · rw [if_neg hlt] at he
      simp at he
  | K b =>
    right
    refine ⟨b, rfl, ?_⟩
    by_cases hlt : x.1 < E.N
    · rw [E.edge_K_fresh hx hlt b] at he
      by_cases hw : E.C.word[x.1]? = some b
      · rw [if_pos hw] at he
        have := Option.some.inj he
        omega
      · rw [if_neg hw] at he
        exact ⟨(Option.some.inj he).symm, fun _ => hw, fun hN => absurd hN (Nat.ne_of_lt hlt)⟩
    · have hxN' : x.1 = E.N := by omega
      rw [E.edge_congr hxN' hxN (Nat.le_refl _), E.edge_K_N b] at he
      by_cases hba : b = E.a
      · rw [if_pos hba] at he
        have := Option.some.inj he
        omega
      · rw [if_neg hba] at he
        refine ⟨?_, fun h' => absurd h' (by omega), fun _ => hba⟩
        rw [hxN', E.cur_N]
        exact (Option.some.inj he).symm

/-- A step between consecutive fresh positions reads the letter by `S` or `K b`. -/
theorem fresh_step_facts {x y : NNode} (h : NStep (prefixGraph I E.C) o x y) (hx : B.word.length < x.1)
    (hy : y.1 = x.1 + 1) :
    x.1 < E.N ∧ ∃ b, E.C.word[x.1]? = some b ∧
      ∃ (hs : x.2 < o.size) (ht : y.2 < o.size),
        ((⟨y.2, ht⟩ : Fin o.size) ∈ o.move ⟨x.2, hs⟩ (colB I E.C x.1) .S (colB I E.C y.1) ∨
          (⟨y.2, ht⟩ : Fin o.size) ∈ o.move ⟨x.2, hs⟩ (colB I E.C x.1) (.K b) (colB I E.C y.1)) := by
  obtain ⟨l, hL⟩ := nstepL_of_nstep h
  obtain ⟨hxN, he⟩ := nstepL_edge E o hL
  have hyN := (nstepL_bounds E o hL).2
  have hlt : x.1 < E.N := by omega
  obtain ⟨b, hb⟩ := E.word_some hlt
  refine ⟨hlt, b, hb, ?_⟩
  obtain ⟨hs, ht, hm⟩ := nstepL_move E o hL
  refine ⟨hs, ht, ?_⟩
  cases l with
  | F =>
    exfalso
    rw [E.edge_F_fresh hx hxN] at he
    have h1 := Option.some.inj he
    have h2 := E.cur_le hxN
    omega
  | S => exact Or.inl hm
  | K b' =>
    rw [E.edge_K_fresh hx hlt b'] at he
    by_cases hw : E.C.word[x.1]? = some b'
    · rw [hw] at hb
      have hbb : b' = b := Option.some.inj hb
      subst hbb
      exact Or.inr hm
    · rw [if_neg hw] at he
      have h1 := Option.some.inj he
      have h2 := advance_le B.word (E.cur x.1) b'
      omega

end Transitions

/-! ## Structure of the piece list -/

namespace Cov
variable {I : Instance k} {B : Reference k} {E : Ext I B} {c : Clause k} (X : Cov I B E c)

theorem buildPieces_length (ai : Nat) : ∀ (si : Nat) (segs : List (List NNode)),
    (X.buildPieces ai si segs).length = 2 * segs.length - 1 := by
  intro si segs
  induction segs generalizing si with
  | nil => rfl
  | cons s rest ih =>
    cases rest with
    | nil => rfl
    | cons t rest =>
      simp only [buildPieces, List.length_cons]
      rw [ih (si + 1)]
      simp only [List.length_cons]
      omega

theorem buildPieces_getD_even (ai : Nat) : ∀ (si : Nat) (segs : List (List NNode)) (t : Nat),
    t < segs.length →
    (X.buildPieces ai si segs).getD (2 * t) default = X.blockPiece ai (si + t) (segs.getD t []) := by
  intro si segs t
  induction segs generalizing si t with
  | nil => intro h; simp at h
  | cons s rest ih =>
    intro ht
    cases rest with
    | nil =>
      have : t = 0 := by simp at ht; omega
      subst this
      rfl
    | cons t' rest =>
      cases t with
      | zero => rfl
      | succ t =>
        simp only [buildPieces]
        rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
          ih (si + 1) t (by simp at ht ⊢; omega), List.getD_cons_succ,
          show si + 1 + t = si + (t + 1) by omega]

theorem buildPieces_getD_odd (ai : Nat) : ∀ (si : Nat) (segs : List (List NNode)) (t : Nat),
    t + 1 < segs.length →
    (X.buildPieces ai si segs).getD (2 * t + 1) default =
      X.transPiece ai (si + t) (segs.getD t []) (segs.getD (t + 1) []) := by
  intro si segs t
  induction segs generalizing si t with
  | nil => intro h; simp at h
  | cons s rest ih =>
    intro ht
    cases rest with
    | nil => simp at ht
    | cons t' rest =>
      cases t with
      | zero => rfl
      | succ t =>
        simp only [buildPieces]
        rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
          ih (si + 1) t (by simp at ht ⊢; omega), show si + 1 + t = si + (t + 1) by omega]
        simp only [List.getD_cons_succ]

theorem pieces_length (ai : Nat) : (X.pieces ai).length = 2 * X.segCount ai - 1 :=
  X.buildPieces_length ai 0 _

theorem pieces_getD_even {ai si : Nat} (hsi : si < X.segCount ai) :
    (X.pieces ai).getD (2 * si) default = X.blockPiece ai si (X.blk ai si) := by
  unfold pieces
  rw [X.buildPieces_getD_even ai 0 _ si hsi, Nat.zero_add]
  rfl

theorem pieces_getD_odd {ai si : Nat} (hsi : si + 1 < X.segCount ai) :
    (X.pieces ai).getD (2 * si + 1) default = X.transPiece ai si (X.blk ai si) (X.blk ai (si + 1)) := by
  unfold pieces
  rw [X.buildPieces_getD_odd ai 0 _ si hsi, Nat.zero_add]
  rfl

/-- Every piece index is even (a block) or odd (a transition). -/
theorem pi_cases {sc pi : Nat} (h : pi < 2 * sc - 1) :
    (∃ si, pi = 2 * si ∧ si < sc) ∨ (∃ si, pi = 2 * si + 1 ∧ si + 1 < sc) := by
  have hdm := Nat.div_add_mod pi 2
  have hr := Nat.mod_lt pi (by decide : 0 < 2)
  rcases Nat.lt_or_ge (pi % 2) 1 with h0 | h1
  · left; exact ⟨pi / 2, by omega, by omega⟩
  · right; exact ⟨pi / 2, by omega, by omega⟩

theorem getLast?_eq_getD {α : Type} [Inhabited α] {l : List α} (hne : l ≠ []) :
    l.getLast? = some (l.getD (l.length - 1) default) := by
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  have hlen : 0 < l.length := List.length_pos_iff.mpr hne
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

theorem head?_eq_getD {α : Type} [Inhabited α] {l : List α} (hne : l ≠ []) :
    l.head? = some (l.getD 0 default) := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x l => rfl

theorem pieces_ne_nil {ai : Nat} (hai : ai < c.atoms.length) : X.pieces ai ≠ [] := by
  intro h
  have := X.pieces_length ai
  rw [h] at this
  have := X.segCount_pos hai
  simp at *
  omega

theorem pieces_head? {ai : Nat} (hai : ai < c.atoms.length) :
    (X.pieces ai).head? = some (X.blockPiece ai 0 (X.blk ai 0)) := by
  rw [head?_eq_getD (X.pieces_ne_nil hai)]
  have := X.pieces_getD_even (ai := ai) (si := 0) (X.segCount_pos hai)
  rw [Nat.mul_zero] at this
  rw [this]

theorem pieces_getLast? {ai : Nat} (hai : ai < c.atoms.length) :
    (X.pieces ai).getLast? =
      some (X.blockPiece ai (X.segCount ai - 1) (X.blk ai (X.segCount ai - 1))) := by
  rw [getLast?_eq_getD (X.pieces_ne_nil hai), X.pieces_length]
  have hpos := X.segCount_pos hai
  rw [show 2 * X.segCount ai - 1 - 1 = 2 * (X.segCount ai - 1) by omega]
  rw [X.pieces_getD_even (by omega)]

/-! ### Shapes of the pieces -/

theorem blockPiece_fresh {ai si : Nat} {s : List NNode} (hf : isFresh B.word.length s = true) :
    X.blockPiece ai si s = ⟨.forward, X.idx (hdPos s), X.idx (lastPos s), hdCtl s, lastCtl s, .F⟩ := by
  unfold blockPiece; rw [if_pos hf]

theorem blockPiece_old {ai si : Nat} {s : List NNode} (hf : ¬ isFresh B.word.length s = true) :
    X.blockPiece ai si s = ⟨.core, X.headIdx ai si, X.lastIdx ai si, hdCtl s, lastCtl s, .F⟩ := by
  unfold blockPiece; rw [if_neg hf]

theorem transPiece_enter {ai si : Nat} {s t : List NNode} (hx : (lastN s).1 ≤ B.word.length) :
    X.transPiece ai si s t = ⟨.enter, X.lastIdx ai si, 0, (lastN s).2, (hdN t).2,
      stepLabel (prefixGraph I E.C) (obsAt c ai) (lastN s) (hdN t)⟩ := by
  unfold transPiece; simp only [if_pos hx]

theorem transPiece_wrap {ai si : Nat} {s t : List NNode} (hx : ¬ (lastN s).1 ≤ B.word.length)
    (hy : B.word.length < (hdN t).1) :
    X.transPiece ai si s t = ⟨.wrap, X.n - 1, 0, (lastN s).2, (hdN t).2, .K E.a⟩ := by
  unfold transPiece; simp only [if_neg hx, if_pos hy]

theorem transPiece_exit {ai si : Nat} {s t : List NNode} (hx : ¬ (lastN s).1 ≤ B.word.length)
    (hy : ¬ B.word.length < (hdN t).1) :
    X.transPiece ai si s t = ⟨.exit, X.idx (lastN s).1, X.headIdx ai (si + 1), (lastN s).2, (hdN t).2,
      stepLabel (prefixGraph I E.C) (obsAt c ai) (lastN s) (hdN t)⟩ := by
  unfold transPiece; simp only [if_neg hx, if_neg hy]

/-- Whether a block is fresh is read off its head and its last node alike. -/
theorem blk_fresh_iff_last {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai) :
    isFresh B.word.length (X.blk ai si) = true ↔ B.word.length < (lastN (X.blk ai si)).1 := by
  have hne := X.blk_ne_nil hai hsi
  constructor
  · intro hf
    rw [← lastPos_lastN hne, X.blk_fresh_lastPos hai hsi hf]
    simp only [isFresh, decide_eq_true_eq] at hf
    omega
  · intro hl
    apply Classical.byContradiction
    intro hf
    have := X.blk_old hai hsi hf _ (lastN_mem hne)
    omega

theorem blk_fresh_iff_hd {ai si : Nat} :
    isFresh B.word.length (X.blk ai si) = true ↔ B.word.length < (hdN (X.blk ai si)).1 := by
  rw [← hdPos_hdN]
  simp [isFresh]

theorem blk_fresh_all {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) {x : NNode} (hx : x ∈ X.blk ai si) :
    hdPos (X.blk ai si) ≤ x.1 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [X.blk_fresh_pos hai hsi hf hi]
  omega

end Cov

/-! ## Seam lookup -/

theorem flatMap_congr_left {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, List.map_congr_left h]

theorem filter_map_eq_flatMap {α β : Type} (p : α → Bool) (f : α → β) : ∀ (l : List α),
    (l.filter p).map f = l.flatMap fun x => if p x = true then [f x] else [] := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hp : p x = true
    · rw [List.filter_cons_of_pos hp, List.map_cons, List.flatMap_cons, if_pos hp, ih]; rfl
    · rw [List.filter_cons_of_neg hp, List.flatMap_cons, if_neg hp, ih]; rfl

namespace Cov
variable {I : Instance k} {B : Reference k} {E : Ext I B} {c : Clause k} (X : Cov I B E c)

theorem D_seams : X.D.seams = X.seams := rfl

theorem mem_seams_iff {e : Nat × Nat × Nat × Nat} : e ∈ X.seams ↔
    ∃ ai si g, ai < c.atoms.length ∧ si < X.segCount ai ∧ isFresh B.word.length (X.blk ai si) = true ∧
      X.idx (hdPos (X.blk ai si)) < g ∧ g < X.idx (lastPos (X.blk ai si)) ∧ g < X.n ∧
      e = (ai, 2 * si, g, ctlAt (X.blk ai si) (X.pos g)) := by
  unfold seams seamsOf blockSeams
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨ai, hai, si, hsi, he⟩
    split at he
    · rename_i hf
      obtain ⟨g, hgmem, rfl⟩ := List.mem_map.mp he
      obtain ⟨hg, hcond⟩ := List.mem_filter.mp hgmem
      simp only [decide_eq_true_eq] at hcond
      exact ⟨ai, si, g, hai, hsi, hf, hcond.1, hcond.2, List.mem_range.mp hg, rfl⟩
    · simp at he
  · rintro ⟨ai, si, g, hai, hsi, hf, hg1, hg2, hg, rfl⟩
    refine ⟨ai, hai, si, hsi, ?_⟩
    rw [if_pos hf]
    exact List.mem_map.mpr ⟨g, List.mem_filter.mpr ⟨List.mem_range.mpr hg, by simp [hg1, hg2]⟩, rfl⟩

/-- The seam control of an internal mark of a fresh block is the chain's control there. -/
theorem seamControl_eq {ai si g : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) (hg1 : X.idx (hdPos (X.blk ai si)) < g)
    (hg2 : g < X.idx (lastPos (X.blk ai si))) :
    seamControl X.D ai (2 * si) g = ctlAt (X.blk ai si) (X.pos g) := by
  have hgn : g < X.n := Nat.lt_trans hg2 (X.idx_lt (X.blk_last_mem_M hai hsi hf))
  have hmem : (ai, 2 * si, g, ctlAt (X.blk ai si) (X.pos g)) ∈ X.seams :=
    X.mem_seams_iff.mpr ⟨ai, si, g, hai, hsi, hf, hg1, hg2, hgn, rfl⟩
  unfold seamControl
  rw [D_seams]
  cases hfind : X.seams.find? (fun s => decide (s.1 = ai ∧ s.2.1 = 2 * si ∧ s.2.2.1 = g)) with
  | none =>
    exfalso
    have := (List.find?_eq_none.mp hfind) _ hmem
    simp at this
  | some r =>
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    obtain ⟨ai', si', g', -, -, -, -, -, -, hr⟩ := X.mem_seams_iff.mp (List.mem_of_find?_eq_some hfind)
    subst hr
    simp only at hp
    obtain ⟨h1, h2, h3⟩ := hp
    subst h1 h3
    have : si' = si := by omega
    subst this
    rfl

/-- The internal entries of the forward control sequence. -/
theorem forwardControls_getD_mid (D : Diagram k) (ai pi i j : Nat) (P : Piece) {t : Nat} (ht : 0 < t)
    (htj : t < j - i) : (forwardControls D ai pi i j P).getD t 0 = seamControl D ai pi (i + t) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  unfold forwardControls
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_cons_succ,
    List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  congr 1
  omega

theorem forwardControls_getD_zero (D : Diagram k) (ai pi i j : Nat) (P : Piece) :
    (forwardControls D ai pi i j P).getD 0 0 = P.lc := rfl

theorem forwardControls_getD_last (D : Diagram k) (ai pi i j : Nat) (P : Piece) (hij : i < j) :
    (forwardControls D ai pi i j P).getD (j - i) 0 = P.rc := by
  obtain ⟨d, hd⟩ : ∃ d, j - i = d + 1 := ⟨j - i - 1, by omega⟩
  rw [hd]
  unfold forwardControls
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_cons, List.length_map, List.length_range]
  rw [show d + 1 - (j - i - 1 + 1) = 0 by omega]
  rfl

/-- The forward controls of a fresh block are the chain's controls at the marks it covers. -/
theorem block_forwardControls {ai si : Nat} (hai : ai < c.atoms.length) (hsi : si < X.segCount ai)
    (hf : isFresh B.word.length (X.blk ai si) = true) {t : Nat}
    (ht : t ≤ X.idx (lastPos (X.blk ai si)) - X.idx (hdPos (X.blk ai si))) :
    (forwardControls X.D ai (2 * si) (X.idx (hdPos (X.blk ai si))) (X.idx (lastPos (X.blk ai si)))
        (X.blockPiece ai si (X.blk ai si))).getD t 0 =
      ctlAt (X.blk ai si) (X.pos (X.idx (hdPos (X.blk ai si)) + t)) := by
  have hne := X.blk_ne_nil hai hsi
  have hhd := X.blk_hd_mem_M hai hsi hf
  have hlast := X.blk_last_mem_M hai hsi hf
  rw [X.blockPiece_fresh hf]
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · rw [forwardControls_getD_zero, Nat.add_zero, X.pos_idx hhd, ctlAt_hd hne]
  · by_cases hlt : t < X.idx (lastPos (X.blk ai si)) - X.idx (hdPos (X.blk ai si))
    · rw [forwardControls_getD_mid _ _ _ _ _ _ htpos hlt]
      exact X.seamControl_eq hai hsi hf (by omega) (by omega)
    · have heq : t = X.idx (lastPos (X.blk ai si)) - X.idx (hdPos (X.blk ai si)) := by omega
      have hij : X.idx (hdPos (X.blk ai si)) < X.idx (lastPos (X.blk ai si)) := by omega
      rw [heq, forwardControls_getD_last _ _ _ _ _ _ hij,
        show X.idx (hdPos (X.blk ai si)) + (X.idx (lastPos (X.blk ai si)) - X.idx (hdPos (X.blk ai si))) =
          X.idx (lastPos (X.blk ai si)) by omega, X.pos_idx hlast]
      exact (ctlAt_last hne (X.blk_consec hai hsi) (by simpa [isFresh] using hf)).symm

theorem transPiece_kind {ai si : Nat} (s t : List NNode) :
    (X.transPiece ai si s t).kind ≠ .forward := by
  unfold transPiece
  by_cases h1 : (lastN s).1 ≤ B.word.length <;> by_cases h2 : B.word.length < (hdN t).1 <;> simp [h1, h2]

end Cov

/-! ## The active items of an interval -/

theorem active_nil (I : Instance k) (D : Diagram k) (ai pi : Nat) (o : Observer k) {P : Piece}
    (hP : P.kind ≠ .forward) : (compilePiece I D ai pi o P).active = [] := by
  unfold compilePiece
  cases finOf o.size P.lc with
  | none => rfl
  | some lc =>
    cases finOf o.size P.rc with
    | none => rfl
    | some rc =>
      cases hk : P.kind with
      | core => rfl
      | forward => exact absurd hk hP
      | enter => rfl
      | exit => cases P.label <;> rfl
      | wrap => rfl

theorem filter_forwardActive_aux (i g : Nat) {β : Type} (f : Nat → β) : ∀ (L : Nat),
    ((List.range L).map fun t => (i + t, f t)).filter (fun x => decide (x.1 = g)) =
      if i ≤ g ∧ g < i + L then [(g, f (g - i))] else [] := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, List.filter_append, ih]
    have hsingle : (([(i + L, f L)] : List (Nat × β)).filter fun x => decide (x.1 = g)) =
        if i + L = g then [(i + L, f L)] else [] := by
      by_cases h2 : i + L = g
      · simp [h2]
      · simp [h2]
    simp only [List.map_cons, List.map_nil]
    rw [hsingle]
    by_cases h1 : i ≤ g ∧ g < i + L
    · have h2 : ¬ i + L = g := by omega
      rw [if_pos h1, if_neg h2, if_pos ⟨h1.1, by omega⟩]
      rfl
    · rw [if_neg h1]
      by_cases h2 : i + L = g
      · rw [if_pos h2, if_pos ⟨by omega, by omega⟩]
        subst h2
        simp
      · rw [if_neg h2, if_neg (by omega)]
        rfl

namespace Cov
variable {I : Instance k} {B : Reference k} {E : Ext I B} {c : Clause k} (X : Cov I B E c)

/-- Does piece `pi` of atom `ai` cover interval `g`? -/
def coversPi (ai pi g : Nat) : Bool :=
  let P := (X.pieces ai).getD pi default
  decide (P.kind = .forward) && decide (P.source ≤ g ∧ g < P.target)

/-- The contributing pieces of interval `g`, in emission order. -/
def contribs (g : Nat) : List (Nat × Nat) :=
  (List.range c.atoms.length).flatMap fun ai =>
    ((List.range (X.pieces ai).length).filter fun pi => X.coversPi ai pi g).map fun pi => (ai, pi)

/-- The active item of a contributing piece. -/
def itemOf (g : Nat) (cp : Nat × Nat) : Active k :=
  (obsAt c cp.1, ctlAt (X.blk cp.1 (cp.2 / 2)) (X.pos g), ctlAt (X.blk cp.1 (cp.2 / 2)) (X.pos (g + 1)))

theorem allEmitted_active :
    (allEmitted I c X.D).active = (List.range c.atoms.length).flatMap fun ai =>
      (List.range (X.pieces ai).length).flatMap fun pi =>
        (compilePiece I X.D ai pi (obsAt c ai) ((X.pieces ai).getD pi default)).active := by
  unfold allEmitted
  rw [foldl_appendEmitted_proj _ active_append, List.map_map, ← List.flatMap_def]
  show [] ++ _ = _
  rw [List.nil_append]
  apply flatMap_congr_left
  intro ai hai
  have hai' : ai < c.atoms.length := List.mem_range.mp hai
  simp only [Function.comp, List.getElem?_eq_getElem hai']
  unfold compileAtom
  rw [foldl_appendEmitted_proj _ active_append, List.map_map, ← List.flatMap_def]
  show [] ++ _ = _
  rw [List.nil_append, X.piecesOf_eq hai', obsAt_eq hai']
  rfl

/-- A covering piece is a fresh block piece. -/
theorem coversPi_block {ai pi g : Nat} (hai : ai < c.atoms.length) (hpi : pi < (X.pieces ai).length)
    (hc : X.coversPi ai pi g = true) :
    ∃ si, pi = 2 * si ∧ si < X.segCount ai ∧ isFresh B.word.length (X.blk ai si) = true ∧
      X.idx (hdPos (X.blk ai si)) ≤ g ∧ g < X.idx (lastPos (X.blk ai si)) := by
  rw [X.pieces_length] at hpi
  rcases pi_cases hpi with ⟨si, rfl, hsi⟩ | ⟨si, rfl, hsi⟩
  · refine ⟨si, rfl, hsi, ?_⟩
    unfold coversPi at hc
    rw [X.pieces_getD_even hsi] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hf : isFresh B.word.length (X.blk ai si) = true
    · rw [X.blockPiece_fresh hf] at hc
      exact ⟨hf, hc.2⟩
    · rw [X.blockPiece_old hf] at hc
      exact absurd hc.1 (by simp)
  · exfalso
    unfold coversPi at hc
    rw [X.pieces_getD_odd hsi] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact X.transPiece_kind _ _ hc.1

/-- The filtered active list of one piece. -/
theorem piece_active_filter {ai pi g : Nat} (hai : ai < c.atoms.length) (hpi : pi < (X.pieces ai).length) :
    (((compilePiece I X.D ai pi (obsAt c ai) ((X.pieces ai).getD pi default)).active.filter
        fun x => decide (x.1 = g)).map fun x => x.2) =
      if X.coversPi ai pi g = true then [X.itemOf g (ai, pi)] else [] := by
  have hlen := X.pieces_length ai
  rw [hlen] at hpi
  rcases pi_cases hpi with ⟨si, rfl, hsi⟩ | ⟨si, rfl, hsi⟩
  · rw [X.pieces_getD_even hsi]
    by_cases hf : isFresh B.word.length (X.blk ai si) = true
    · -- a fresh block piece
      have hne := X.blk_ne_nil hai hsi
      have hhd := X.blk_hd_mem_M hai hsi hf
      have hlast := X.blk_last_mem_M hai hsi hf
      have hlc : hdCtl (X.blk ai si) < (obsAt c ai).size := by
        rw [hdCtl_hdN]; exact X.blk_ctl_lt hai hsi (hdN_mem hne)
      have hrc : lastCtl (X.blk ai si) < (obsAt c ai).size := by
        rw [lastCtl_lastN hne]; exact X.blk_ctl_lt hai hsi (lastN_mem hne)
      have hcov : X.coversPi ai (2 * si) g =
          decide (X.idx (hdPos (X.blk ai si)) ≤ g ∧ g < X.idx (lastPos (X.blk ai si))) := by
        unfold coversPi
        rw [X.pieces_getD_even hsi, X.blockPiece_fresh hf]
        simp
      rw [hcov]
      have e1 := X.block_forwardControls hai hsi hf (t := g - X.idx (hdPos (X.blk ai si)))
      have e2 := X.block_forwardControls hai hsi hf (t := g - X.idx (hdPos (X.blk ai si)) + 1)
      rw [X.blockPiece_fresh hf] at e1 e2 ⊢
      simp only [compilePiece, finOf_pos hlc, finOf_pos hrc]
      by_cases hst : X.idx (hdPos (X.blk ai si)) = X.idx (lastPos (X.blk ai si))
      · rw [if_pos hst]
        simp only [List.filter_nil, List.map_nil]
        rw [if_neg (by rw [decide_eq_true_eq]; omega)]
      · rw [if_neg hst]
        have hle : X.idx (hdPos (X.blk ai si)) ≤ X.idx (lastPos (X.blk ai si)) := by
          apply X.idx_le hhd hlast
          rw [X.blk_fresh_lastPos hai hsi hf]; omega
        have hlt : X.idx (hdPos (X.blk ai si)) < X.idx (lastPos (X.blk ai si)) := Nat.lt_of_le_of_ne hle hst
        unfold forwardActive
        rw [filter_forwardActive_aux]
        by_cases hg : X.idx (hdPos (X.blk ai si)) ≤ g ∧ g < X.idx (lastPos (X.blk ai si))
        · rw [if_pos ⟨hg.1, by omega⟩, if_pos (by simpa using hg)]
          simp only [List.map_cons, List.map_nil]
          have e1' := e1 (by omega)
          have e2' := e2 (by omega)
          rw [show X.idx (hdPos (X.blk ai si)) + (g - X.idx (hdPos (X.blk ai si))) = g by omega] at e1'
          rw [show X.idx (hdPos (X.blk ai si)) + (g - X.idx (hdPos (X.blk ai si)) + 1) = g + 1 by omega] at e2'
          rw [e1', e2']
          unfold itemOf
          rw [show 2 * si / 2 = si by omega]
        · rw [if_neg (by omega), if_neg (by simpa using hg)]
          rfl
    · -- an old block piece: no active items
      have hcov : X.coversPi ai (2 * si) g = false := by
        unfold coversPi
        rw [X.pieces_getD_even hsi, X.blockPiece_old hf]
        simp
      rw [hcov, if_neg (by simp), active_nil _ _ _ _ _ (by rw [X.blockPiece_old hf]; simp)]
      rfl
  · rw [X.pieces_getD_odd hsi]
    have hcov : X.coversPi ai (2 * si + 1) g = false := by
      unfold coversPi
      rw [X.pieces_getD_odd hsi]
      simp [X.transPiece_kind]
    rw [hcov, if_neg (by simp), active_nil _ _ _ _ _ (X.transPiece_kind _ _)]
    rfl

/-- The active items of interval `g` are the items of its contributing pieces, in order. -/
theorem itemsAt_eq (g : Nat) : itemsAt I c X.D g = (X.contribs g).map (X.itemOf g) := by
  unfold itemsAt contribs
  rw [X.allEmitted_active, List.filter_flatMap, List.map_flatMap, List.map_flatMap]
  apply flatMap_congr_left
  intro ai hai
  have hai' := List.mem_range.mp hai
  rw [List.filter_flatMap, List.map_flatMap, List.map_map, filter_map_eq_flatMap]
  apply flatMap_congr_left
  intro pi hpi
  have hpi' := List.mem_range.mp hpi
  rw [X.piece_active_filter hai' hpi']
  rfl

end Cov

end RankQueryCoverage
end Subtail
