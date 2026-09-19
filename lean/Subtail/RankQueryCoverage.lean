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

end RankQueryCoverage
end Subtail
