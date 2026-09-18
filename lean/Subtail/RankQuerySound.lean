import Subtail.RankQueryCompiler

/-!
# Towards the reverse Closure direction: generator traces of the interval product

Issue #29 (stage 4c).  A base model of a compiled clause contains, for every
physical interval, an accepted run of the shared-interval product observer.
This module extracts from such a run a GENERATOR TRACE: the emitted letters,
the actual reverse states, the cursor walk along the base `K` edges, the safety
facts checked by the product, and the fact that no intermediate vertex is the
old endpoint.  Concatenated traces then give one labelled extension word whose
literal first return is proved through `FirstReturnGraph.generator_first_hit_iff`.

Nothing here yet assembles the original query on the extension; that is the
remaining part of the reverse direction.  No `sorry`, no custom axiom.
-/
namespace Subtail
namespace RankQuerySound
open TerminalRank RankMilestones RankQuery RankQueryCompiler

variable {k : Nat}

/-! ## Base-graph colours by position and the cursor walk -/

/-- The colour of position `v` of the literal prefix graph of `B` (any `Nat`). -/
def colB (I : Instance k) (B : Reference k) (v : Nat) : Colour k :=
  ⟨B.label v, mask I B v, B.word[v]?, decide (v = 0), decide (v = B.word.length)⟩

theorem prefixGraph_colour (I : Instance k) (B : Reference k) (j : Fin (prefixGraph I B).size) :
    (prefixGraph I B).colour j = colB I B j.val := rfl

/-- Reading letters from cursor `v` along the literal `K` edges of `P(B)`. -/
def walkTo (B : Reference k) (v : Nat) : List Bool → Nat
  | [] => v
  | b :: bs => walkTo B (advance B.word v b) bs

theorem walkTo_append (B : Reference k) (v : Nat) (l₁ l₂ : List Bool) :
    walkTo B v (l₁ ++ l₂) = walkTo B (walkTo B v l₁) l₂ := by
  induction l₁ generalizing v with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, walkTo, ih]

theorem walkTo_le (B : Reference k) {v : Nat} (hv : v ≤ B.word.length) (l : List Bool) :
    walkTo B v l ≤ B.word.length := by
  induction l generalizing v with
  | nil => exact hv
  | cons b bs ih => exact ih (advance_le _ _ _)

/-! ## Generator traces -/

/-- A trace of the interval product from cursor `v` with decoded control `x`:
each step emits the pending bit `b` of the current control along the base
`K_b` edge and moves to a control `y` accepted by `intervalStep`; every control
is allowed at its cursor.  The list records `(letter, actual state after)`. -/
inductive Gen (I : Instance k) (B : Reference k) (items : List (Active k)) :
    Nat → IControl k → List (Bool × Fin k) → Nat → IControl k → Prop
  | nil {v : Nat} {x : IControl k}
      (hx : intervalAllows I items x (colB I B v) = true) :
      Gen I B items v x [] v x
  | cons {v : Nat} {x y z : IControl k} {b : Bool} {ext : List (Bool × Fin k)} {v' : Nat}
      (hx : intervalAllows I items x (colB I B v) = true)
      (hb : x.next = some b)
      (hs : intervalStep I items x y (colB I B v) (.K b) (colB I B (advance B.word v b)) = true)
      (rest : Gen I B items (advance B.word v b) y ext v' z) :
      Gen I B items v x ((b, y.state) :: ext) v' z

theorem gen_snoc {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v v' : Nat} {x y z : IControl k} {ext : List (Bool × Fin k)} {b : Bool}
    (h : Gen I B items v x ext v' y) (hb : y.next = some b)
    (hs : intervalStep I items y z (colB I B v') (.K b) (colB I B (advance B.word v' b)) = true)
    (hz : intervalAllows I items z (colB I B (advance B.word v' b)) = true) :
    Gen I B items v x (ext ++ [(b, z.state)]) (advance B.word v' b) z := by
  induction h with
  | nil hx => exact Gen.cons hx hb hs (Gen.nil hz)
  | cons hx hb' hs' _ ih => exact Gen.cons hx hb' hs' (ih hb hs hz)

/-- The pending bit and the emitted label of one product step. -/
theorem intervalStep_label {I : Instance k} {items : List (Active k)} {x y : IControl k}
    {c d : Colour k} {l : Label} (h : intervalStep I items x y c l d = true) :
    ∃ b, x.next = some b ∧ l = .K b := by
  unfold intervalStep at h
  cases hx : x.next with
  | none => simp [hx] at h
  | some b =>
    refine ⟨b, rfl, ?_⟩
    simp only [hx, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1.1.1.1.1

/-- Every accepted run of the interval product is a generator trace. -/
theorem run_gen (I : Instance k) (B : Reference k) (items : List (Active k))
    (ql : Fin k) (nl : Option Bool) (qr : Fin k) (nr : Option Bool)
    {x y : Node (prefixGraph I B) (intervalObs I items ql nl qr nr)}
    (h : Run (prefixGraph I B) (intervalObs I items ql nl qr nr) x y) :
    ∃ (x0 x1 : IControl k) (ext : List (Bool × Fin k)),
      decodeI items x.2.val = some x0 ∧ decodeI items y.2.val = some x1 ∧
      Gen I B items x.1.val x0 ext y.1.val x1 := by
  induction h with
  | refl hx =>
    simp only [Allowed, intervalObs] at hx
    cases hd : decodeI items x.2.val with
    | none => simp [hd] at hx
    | some x0 =>
      simp only [hd] at hx
      exact ⟨x0, x0, [], rfl, rfl, Gen.nil hx⟩
  | @step y' z' _ hs ih =>
    obtain ⟨x0, x1, ext, hd0, hd1, hg⟩ := ih
    obtain ⟨l, he, hm, hz⟩ := hs
    simp only [intervalObs, hd1] at hm
    have hm' := List.mem_filter.mp hm
    cases hd2 : decodeI items z'.2.val with
    | none => simp [hd2] at hm'
    | some x2 =>
      simp only [hd2] at hm'
      have hstep := hm'.2
      obtain ⟨b, hb, rfl⟩ := intervalStep_label hstep
      have hedge : z'.1.val = advance B.word y'.1.val b := by
        simp only [prefixGraph] at he
        have := congrArg Fin.val (Option.some.inj he)
        exact this.symm
      simp only [Allowed, intervalObs, hd2] at hz
      rw [prefixGraph_colour, prefixGraph_colour, hedge] at hstep
      rw [prefixGraph_colour, hedge] at hz
      exact ⟨x0, x2, ext ++ [(b, x2.state)], hd0, rfl, hedge ▸ gen_snoc hg hb hstep hz⟩

/-! ## Facts carried by a trace -/

theorem gen_walk {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v v' : Nat} {x z : IControl k} {ext : List (Bool × Fin k)}
    (h : Gen I B items v x ext v' z) : walkTo B v (ext.map Prod.fst) = v' := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ _ ih => simpa [walkTo] using ih

/-- The actual state after the whole trace. -/
def lastState (q : Fin k) (ext : List (Bool × Fin k)) : Fin k :=
  match ext.getLast? with
  | some (_, p) => p
  | none => q

theorem lastState_cons (q : Fin k) (b : Bool) (p : Fin k) (ext : List (Bool × Fin k)) :
    lastState q ((b, p) :: ext) = lastState p ext := by
  cases ext with
  | nil => rfl
  | cons e rest =>
    simp only [lastState, List.getLast?_cons_cons]
    cases h : (e :: rest).getLast? with
    | none => simp at h
    | some pr => rfl

theorem gen_last {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v v' : Nat} {x z : IControl k} {ext : List (Bool × Fin k)}
    (h : Gen I B items v x ext v' z) : lastState x.state ext = z.state := by
  induction h with
  | nil _ => rfl
  | cons _ _ _ _ ih => rw [lastState_cons]; exact ih

/-- Reverse-run consistency of a labelled extension from state `q`. -/
def RevRun (I : Instance k) : Fin k → List (Bool × Fin k) → Prop
  | _, [] => True
  | q, (b, p) :: ext => step I p b = some q ∧ RevRun I p ext

/-- The safety facts of a labelled extension read from cursor `v`. -/
def SafeWalk (I : Instance k) (B : Reference k) : Nat → List (Bool × Fin k) → Prop
  | _, [] => True
  | v, (b, p) :: ext =>
      I.bad.get p = false ∧ (I.flags.get p).get p = false ∧
      (mask I B (advance B.word v b)).get p = false ∧
      SafeWalk I B (advance B.word v b) ext

theorem intervalStep_facts {I : Instance k} {items : List (Active k)} {x y : IControl k}
    {c d : Colour k} {b : Bool} (h : intervalStep I items x y c (.K b) d = true)
    (hb : x.next = some b) :
    c.isEnd = false ∧ y.seen = 1 ∧ step I y.state b = some x.state ∧
      I.bad.get y.state = false ∧ (I.flags.get y.state).get y.state = false ∧
      d.mask.get y.state = false ∧ (y.next.isNone == d.isEnd) = true := by
  unfold intervalStep at h
  simp only [hb, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hend⟩, hseen⟩, hstep⟩, hbad⟩, hflag⟩, hmask⟩, hnext⟩, -⟩ := h
  exact ⟨hend, hseen, hstep, hbad, hflag, hmask, by simpa using hnext⟩

theorem intervalAllows_facts {I : Instance k} {items : List (Active k)} {x : IControl k}
    {c : Colour k} (h : intervalAllows I items x c = true) :
    I.bad.get x.state = false ∧ (I.flags.get x.state).get x.state = false ∧
      c.mask.get x.state = false ∧ (x.next.isNone == c.isEnd) = true := by
  unfold intervalAllows at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hbad, hflag⟩, hmask⟩, hnext⟩, -⟩ := h
  exact ⟨hbad, hflag, hmask, hnext⟩

theorem gen_revRun {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v v' : Nat} {x z : IControl k} {ext : List (Bool × Fin k)}
    (h : Gen I B items v x ext v' z) : RevRun I x.state ext := by
  induction h with
  | nil _ => trivial
  | cons _ hb hs _ ih => exact ⟨(intervalStep_facts hs hb).2.2.1, ih⟩

theorem gen_safeWalk {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v v' : Nat} {x z : IControl k} {ext : List (Bool × Fin k)}
    (h : Gen I B items v x ext v' z) : SafeWalk I B v ext := by
  induction h with
  | nil _ => trivial
  | cons _ hb hs _ ih =>
    have f := intervalStep_facts hs hb
    exact ⟨f.2.2.2.1, f.2.2.2.2.1, by simpa [colB] using f.2.2.2.2.2.1, ih⟩

/-- A control with a pending bit is never at the old endpoint. -/
theorem gen_start_ne {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v : Nat} {x : IControl k} {b : Bool}
    (hx : intervalAllows I items x (colB I B v) = true) (hb : x.next = some b) :
    v ≠ B.word.length := by
  have f := (intervalAllows_facts hx).2.2.2
  simp only [hb, Option.isNone_some, colB, beq_iff_eq] at f
  intro hv
  simp [hv] at f

/-- No intermediate cursor of a trace is the old endpoint. -/
theorem gen_noHit {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v v' : Nat} {x z : IControl k} {ext : List (Bool × Fin k)}
    (h : Gen I B items v x ext v' z) :
    ∀ i, i < ext.length → walkTo B v ((ext.map Prod.fst).take i) ≠ B.word.length := by
  induction h with
  | nil _ => intro i hi; simp at hi
  | cons hx hb _ _ ih =>
    intro i hi
    cases i with
    | zero => simpa [walkTo] using gen_start_ne hx hb
    | succ i =>
      simp only [List.map_cons, List.take_succ_cons, walkTo]
      exact ih i (by simpa using hi)

/-- The first emitted letter of a nonempty trace is the pending bit of its start. -/
theorem gen_head {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v v' : Nat} {x z : IControl k} {ext : List (Bool × Fin k)}
    (h : Gen I B items v x ext v' z) (hne : ext ≠ []) :
    (ext.map Prod.fst).head? = x.next := by
  cases h with
  | nil _ => exact absurd rfl hne
  | cons _ hb _ _ => simp [hb]

/-- An empty trace does not move and does not change the control. -/
theorem gen_nil_eq {I : Instance k} {B : Reference k} {items : List (Active k)}
    {v v' : Nat} {x z : IControl k}
    (h : Gen I B items v x [] v' z) : v = v' ∧ x = z := by
  cases h with
  | nil _ => exact ⟨rfl, rfl⟩

/-! ## The extension reference and its literal first return -/

/-- The actual state after `i` letters of a labelled extension from `q`. -/
def stateAt (q : Fin k) (ext : List (Bool × Fin k)) : Nat → Fin k
  | 0 => q
  | i + 1 => match ext[i]? with
    | some (_, p) => p
    | none => q

/-- `B` extended by a labelled trace; labels beyond the extension are irrelevant. -/
def extRef (B : Reference k) (ext : List (Bool × Fin k)) : Reference k where
  word := B.word ++ ext.map Prod.fst
  label := fun j => if j ≤ B.word.length then B.label j
    else stateAt (B.label B.word.length) ext (j - B.word.length)

theorem extRef_word (B : Reference k) (ext : List (Bool × Fin k)) :
    (extRef B ext).word = B.word ++ ext.map Prod.fst := rfl

theorem extRef_length (B : Reference k) (ext : List (Bool × Fin k)) :
    (extRef B ext).word.length = B.word.length + ext.length := by
  simp [extRef]

theorem extRef_take (B : Reference k) (ext : List (Bool × Fin k)) :
    (extRef B ext).word.take B.word.length = B.word := by
  simp [extRef]

theorem extRef_take_le (B : Reference k) (ext : List (Bool × Fin k)) {j : Nat}
    (hj : j ≤ B.word.length) : (extRef B ext).word.take j = B.word.take j := by
  simp [extRef, List.take_append_of_le_length hj]

theorem extRef_label_le (B : Reference k) (ext : List (Bool × Fin k)) {j : Nat}
    (hj : j ≤ B.word.length) : (extRef B ext).label j = B.label j := by
  simp [extRef, hj]

theorem extRef_label_add (B : Reference k) (ext : List (Bool × Fin k)) (i : Nat) :
    (extRef B ext).label (B.word.length + i) = stateAt (B.label B.word.length) ext i := by
  cases i with
  | zero => simp [extRef, stateAt]
  | succ i =>
    have h : ¬ (B.word.length + (i + 1) ≤ B.word.length) := by omega
    simp only [extRef, h, if_false, Nat.add_sub_cancel_left]

theorem extRef_getElem? (B : Reference k) (ext : List (Bool × Fin k)) (i : Nat) :
    (extRef B ext).word[B.word.length + i]? = (ext.map Prod.fst)[i]? := by
  simp [extRef, List.getElem?_append_right]

theorem extRef_getElem?_lt (B : Reference k) (ext : List (Bool × Fin k)) {j : Nat}
    (hj : j < B.word.length) : (extRef B ext).word[j]? = B.word[j]? := by
  simp [extRef, List.getElem?_append_left hj]

/-- The generator cursor of the extended word is the literal walk on `P(B)`. -/
theorem cursor_eq_walk (B : Reference k) (letters : List Bool) :
    ∀ {d : Nat}, d ≤ letters.length →
      FirstReturnGraph.cursor (B.word ++ letters) B.word.length d =
        walkTo B (failureParent B.word) (letters.take d) := by
  intro d
  induction d with
  | zero =>
    intro _
    simp [FirstReturnGraph.cursor, walkTo]
  | succ d ih =>
    intro hd
    have hd' : d < letters.length := by omega
    have hle : d ≤ letters.length := Nat.le_of_lt hd'
    have hfp : failureParent B.word ≤ B.word.length := by
      have := failureParent_take_le B.word B.word.length
      simpa using this
    have hcur : FirstReturnGraph.cursor (B.word ++ letters) B.word.length d ≤ B.word.length := by
      rw [ih hle]
      exact walkTo_le B hfp _
    rw [FirstReturnGraph.cursor, List.take_left, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.getElem?_eq_getElem hd', Option.getD_some,
      ← RankQueryFirstReturn.advance_eq hcur, ih hle, List.take_succ_eq_append_getElem hd',
      walkTo_append]
    rfl

/-- Positive length, a final hit and no intermediate hit give a literal first return. -/
theorem extRef_firstReturn (B : Reference k) (hm : 0 < B.word.length) (letters : List Bool)
    (hL : 0 < letters.length)
    (hend : walkTo B (failureParent B.word) letters = B.word.length)
    (hno : ∀ i, 0 < i → i < letters.length →
      walkTo B (failureParent B.word) (letters.take i) ≠ B.word.length) :
    FirstReturn (B.word ++ letters) B.word.length (B.word ++ letters).length := by
  have hlen : (B.word ++ letters).length = B.word.length + letters.length := List.length_append
  apply (FirstReturnGraph.generator_first_hit_iff hm).mp
  refine ⟨by omega, ?_, ?_⟩
  · rw [hlen, Nat.add_sub_cancel_left, cursor_eq_walk B letters (Nat.le_refl _), List.take_length]
    exact hend
  · intro d hd
    rw [hlen, Nat.add_sub_cancel_left] at hd
    rw [cursor_eq_walk B letters (Nat.le_of_lt hd)]
    have hfp : failureParent B.word ≤ B.word.length := by
      have := (failureParent_spec B.word hm).2.1
      omega
    have hle := walkTo_le B hfp (letters.take d)
    cases d with
    | zero =>
      simp only [List.take_zero, walkTo]
      have := (failureParent_spec B.word hm).2.1
      omega
    | succ d =>
      have := hno (d + 1) (Nat.succ_pos d) hd
      omega

/-! ## Safety of the extension reference -/

theorem any_congr {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem mem_borders_le {w : Word} {j h : Nat} (hh : h ∈ borderLengths (w.take j)) : h ≤ j := by
  have := (mem_borderLengths.mp hh).1
  simp only [List.length_take] at this
  omega

/-- Masks of old positions do not change under extension. -/
theorem extRef_mask_le (I : Instance k) (B : Reference k) (ext : List (Bool × Fin k)) {j : Nat}
    (hj : j ≤ B.word.length) : mask I (extRef B ext) j = mask I B j := by
  simp only [mask, extRef_take_le B ext hj]
  congr 1
  funext p
  apply any_congr
  intro h hh
  rw [extRef_label_le B ext (Nat.le_trans (mem_borders_le hh) hj)]

/-- The surgery mask depends on labels only at border positions. -/
theorem frMask_congr {w : Word} (col : Fin k → Fin k → Bool) {r r' : Nat → Fin k} {j : Nat}
    (h : ∀ i, i ≤ j → r i = r' i) (q : Fin k) :
    FirstReturnGraph.mask w col r j q = FirstReturnGraph.mask w col r' j q := by
  unfold FirstReturnGraph.mask
  apply any_congr
  intro i hi
  rw [h i (mem_borders_le hi)]

theorem stateAt_succ (q : Fin k) (ext : List (Bool × Fin k)) {i : Nat} (hi : i < ext.length) :
    stateAt q ext (i + 1) = (ext[i]).2 := by
  simp [stateAt, List.getElem?_eq_getElem hi]

theorem stateAt_cons (q : Fin k) (b : Bool) (p : Fin k) (rest : List (Bool × Fin k)) {i : Nat}
    (hi : i ≤ rest.length) : stateAt q ((b, p) :: rest) (i + 1) = stateAt p rest i := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [stateAt, List.getElem?_cons_succ, List.getElem?_eq_getElem (by omega : i < rest.length)]

theorem revRun_step {I : Instance k} : ∀ {q : Fin k} {ext : List (Bool × Fin k)},
    RevRun I q ext → ∀ i, (hi : i < ext.length) →
      step I (stateAt q ext (i + 1)) (ext[i]).1 = some (stateAt q ext i) := by
  intro q ext
  induction ext generalizing q with
  | nil => intro _ i hi; simp at hi
  | cons e rest ih =>
    intro h i hi
    obtain ⟨b, p⟩ := e
    obtain ⟨hstep, hrest⟩ := h
    cases i with
    | zero => simpa [stateAt] using hstep
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      rw [stateAt_cons _ _ _ _ (by omega), stateAt_cons _ _ _ _ (by omega), List.getElem_cons_succ]
      exact ih hrest i hi'

theorem safeWalk_get {I : Instance k} {B : Reference k} : ∀ {v : Nat} {ext : List (Bool × Fin k)},
    SafeWalk I B v ext → ∀ i, (hi : i < ext.length) →
      I.bad.get (ext[i]).2 = false ∧ (I.flags.get (ext[i]).2).get (ext[i]).2 = false ∧
      (mask I B (walkTo B v ((ext.map Prod.fst).take (i + 1)))).get (ext[i]).2 = false := by
  intro v ext
  induction ext generalizing v with
  | nil => intro _ i hi; simp at hi
  | cons e rest ih =>
    intro h i hi
    obtain ⟨b, p⟩ := e
    obtain ⟨hbad, hflag, hmask, hrest⟩ := h
    cases i with
    | zero => exact ⟨hbad, hflag, by simpa [walkTo] using hmask⟩
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      have := ih hrest i hi'
      simpa [walkTo] using this

/-- **Safety of the reconstructed extension.**  A labelled trace that is
reverse-consistent, safe along the walk from the failure parent, and returns
first at its end is a safe reference. -/
theorem extRef_safe (I : Instance k) (B : Reference k) (hB : SafeReference I B)
    (ext : List (Bool × Fin k)) (hL : 0 < ext.length)
    (hrev : RevRun I (B.label B.word.length) ext)
    (hsafe : SafeWalk I B (failureParent B.word) ext)
    (hend : walkTo B (failureParent B.word) (ext.map Prod.fst) = B.word.length)
    (hno : ∀ i, 0 < i → i < ext.length →
      walkTo B (failureParent B.word) ((ext.map Prod.fst).take i) ≠ B.word.length) :
    SafeReference I (extRef B ext) := by
  have hm : 0 < B.word.length := hB.nonempty
  have hlen := extRef_length B ext
  have hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length :=
    extRef_firstReturn B hm (ext.map Prod.fst) (by simpa using hL) hend
      (by simpa using hno)
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [extRef_label_le B ext (Nat.zero_le _)]
    exact hB.accepting
  · intro j hj
    by_cases hjm : j < B.word.length
    · rw [extRef_label_le B ext (by omega), extRef_label_le B ext (by omega)]
      have hw : (extRef B ext).word[j]'hj = B.word[j]'hjm := by
        have := extRef_getElem?_lt B ext hjm
        rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjm] at this
        exact Option.some.inj this
      rw [hw]
      exact hB.run j hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = B.word.length + i := ⟨j - B.word.length, by omega⟩
      have hi : i < ext.length := by omega
      rw [show B.word.length + i + 1 = B.word.length + (i + 1) from rfl, extRef_label_add,
        extRef_label_add]
      have hw : (extRef B ext).word[B.word.length + i]'hj = (ext[i]).1 := by
        have := extRef_getElem? B ext i
        rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (by simpa using hi)] at this
        simpa using Option.some.inj this
      rw [hw]
      exact revRun_step hrev i hi
  · intro j hj
    by_cases hjm : j ≤ B.word.length
    · rw [extRef_label_le B ext hjm]
      exact hB.safe j hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = B.word.length + (i + 1) := ⟨j - B.word.length - 1, by omega⟩
      have hi : i < ext.length := by omega
      rw [extRef_label_add, stateAt_succ _ _ hi]
      exact (safeWalk_get hsafe i hi).1
  · intro j hj
    by_cases hjm : j ≤ B.word.length
    · rw [extRef_label_le B ext hjm, extRef_mask_le I B ext hjm]
      exact hB.border j hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = B.word.length + (i + 1) := ⟨j - B.word.length - 1, by omega⟩
      have hi : i < ext.length := by omega
      have hfp : failureParent B.word ≤ B.word.length := by
        have := failureParent_take_le B.word B.word.length
        simpa using this
      let col : Fin k → Fin k → Bool := fun p t => (I.flags.get p).get t
      rw [RankQueryFirstReturn.mask_get_eq]
      rw [FirstReturnGraph.fresh_clear_iff hm hr (by omega) hj col]
      rw [extRef_label_add, stateAt_succ _ _ hi]
      obtain ⟨-, hflag, hmask⟩ := safeWalk_get hsafe i hi
      refine ⟨hflag, ?_⟩
      rw [extRef_take, Nat.add_sub_cancel_left, extRef_word,
        cursor_eq_walk B (ext.map Prod.fst) (by simp; omega)]
      have hcur : walkTo B (failureParent B.word) ((ext.map Prod.fst).take (i + 1)) ≤ B.word.length :=
        walkTo_le B hfp _
      rw [frMask_congr col (r := (extRef B ext).label) (r' := B.label)
        (fun h hh => extRef_label_le B ext (Nat.le_trans hh hcur))]
      rw [← RankQueryFirstReturn.mask_get_eq]
      exact hmask

/-! ## Reading the compiled clause -/

section Compiled
variable (I : Instance k) (c : Clause k) (D : Diagram k)

theorem mem_tests_end :
    (endVar D, fun col => decide (col = D.oldEnd)) ∈ (compileValid I c D).tests :=
  List.mem_cons_self ..

theorem mem_tests_notEnd {j : Nat} (hj : j < D.groups - 1) :
    (zVar D j, fun (col : Colour k) => !col.isEnd) ∈ (compileValid I c D).tests :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))

theorem mem_tests_query {v : Fin c.vars} {t : Colour k → Bool} (h : (v, t) ∈ c.tests) :
    queryTest I D v.val t ∈ (compileValid I c D).tests :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨(v, t), h, rfl⟩)))

theorem mem_tests_emitted {t : Var D × (Colour k → Bool)} (h : t ∈ (allEmitted I c D).tests) :
    t ∈ (compileValid I c D).tests :=
  List.mem_cons_of_mem _ (List.mem_append_right _ h)

theorem mem_equal_last : (zVar D (D.groups - 1), endVar D) ∈ (compileValid I c D).equal :=
  List.mem_cons_self ..

theorem mem_equal_core {e : Var D × Var D} (h : e ∈ corePairs D c.equal) :
    e ∈ (compileValid I c D).equal :=
  List.mem_cons_of_mem _ (List.mem_append_left _ h)

theorem mem_equal_emitted {e : Var D × Var D} (h : e ∈ (allEmitted I c D).equal) :
    e ∈ (compileValid I c D).equal :=
  List.mem_cons_of_mem _ (List.mem_append_right _ h)

theorem unequal_eq : (compileValid I c D).unequal = corePairs D c.unequal := rfl

theorem mem_atoms_F : (⟨oneEdge .F, endVar D, initVar D⟩ : Atom k _) ∈ (compileValid I c D).atoms :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))

theorem mem_atoms_K :
    (⟨edgeObs (.K D.firstBit) (fun _ => true)
        (fun col => !col.mask.get (markState D 0) && (col.isEnd == decide (D.groups = 1))) none,
      initVar D, zVar D 0⟩ : Atom k _) ∈ (compileValid I c D).atoms :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem mem_atoms_emitted {a : Atom k (2 + D.groups + D.coreVars)}
    (h : a ∈ (allEmitted I c D).atoms) : a ∈ (compileValid I c D).atoms :=
  List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_atoms_interval {g : Nat} (hg : g < D.groups - 1) :
    intervalAtom I c D g ∈ (compileValid I c D).atoms :=
  List.mem_append_right _ (List.mem_map.mpr ⟨g, List.mem_range.mpr hg, rfl⟩)

/-- The validity facts used by the reverse direction. -/
theorem valid_facts (h : validDiagram I c D = true) :
    0 < D.groups ∧ D.states.length = D.groups ∧ D.nextBits.length = D.groups ∧
    D.loc.length = c.vars ∧ D.pieces.length = c.atoms.length ∧
    D.nextBits.getLast? = some none ∧ (D.nextBits.take (D.groups - 1)).all Option.isSome = true ∧
    D.oldEnd.isEnd = true ∧ D.oldEnd.root = false ∧ D.oldEnd.next = none ∧
    step I (markState D 0) D.firstBit = some D.oldEnd.state ∧
    I.bad.get (markState D 0) = false ∧ (I.flags.get (markState D 0)).get (markState D 0) = false := by
  simp only [validDiagram, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Every mark before the last has a pending bit; the last mark is END. -/
theorem nextOf_isSome (h : validDiagram I c D = true) {g : Nat} (hg : g < D.groups - 1) :
    ∃ b, nextOf D g = some b := by
  obtain ⟨-, -, hlen, -, -, -, hall, -⟩ := valid_facts I c D h
  have hg' : g < D.nextBits.length := by omega
  have hmem : D.nextBits[g] ∈ D.nextBits.take (D.groups - 1) := by
    rw [List.mem_iff_getElem]
    exact ⟨g, by simp [List.length_take]; omega, by simp⟩
  have := (List.all_eq_true.mp hall) _ hmem
  simp only [nextOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg', Option.getD_some]
  cases hb : D.nextBits[g] with
  | none => simp [hb] at this
  | some b => exact ⟨b, rfl⟩

theorem nextOf_last (h : validDiagram I c D = true) : nextOf D (D.groups - 1) = none := by
  obtain ⟨hn, -, hlen, -, -, hlast, -⟩ := valid_facts I c D h
  have hpos : 0 < D.nextBits.length := by omega
  rw [List.getLast?_eq_getElem? ] at hlast
  simp only [nextOf, List.getD_eq_getElem?_getD]
  have : D.nextBits.length - 1 = D.groups - 1 := by omega
  rw [← this, hlast]
  rfl

end Compiled

/-! ## Two-control edge observers accept exactly their edge -/

/-- A run of an observer that only moves from control `0` to control `1`. -/
theorem two_control_run {G : Graph k} {O : Observer k}
    (hmove : ∀ q c l d p, p ∈ O.move q c l d → q.val = 0 ∧ p.val = 1)
    {u : Fin G.size} {q0 : Fin O.size} (hq : q0.val = 0) {y : Node G O}
    (h : Run G O (u, q0) y) :
    y = (u, q0) ∨ (y.2.val = 1 ∧ ∃ l, G.edge u l = some y.1 ∧
      y.2 ∈ O.move q0 (G.colour u) l (G.colour y.1) ∧ Allowed G O y) := by
  induction h with
  | refl _ => exact Or.inl rfl
  | @step y' z' _ hs ih =>
    obtain ⟨l, he, hm, hz⟩ := hs
    rcases ih with rfl | ⟨h1, -⟩
    · exact Or.inr ⟨(hmove _ _ _ _ _ hm).2, l, he, hm, hz⟩
    · have := (hmove _ _ _ _ _ hm).1
      omega

theorem oneEdge_move {l l' : Label} {q p : Fin (oneEdge (k := k) l).size} {c d : Colour k}
    (hp : p ∈ (oneEdge l).move q c l' d) : q.val = 0 ∧ p.val = 1 ∧ l' = l := by
  simp only [oneEdge] at hp
  split at hp
  · rename_i hc
    have hp' := List.mem_singleton.mp hp
    exact ⟨hc.1, by rw [hp'], hc.2⟩
  · exact absurd hp (List.not_mem_nil)

theorem edgeObs_move {l l' : Label} {left right : Colour k → Bool} {sem : Option (Portal k)}
    {q p : Fin (edgeObs l left right sem).size} {c d : Colour k}
    (hp : p ∈ (edgeObs l left right sem).move q c l' d) :
    q.val = 0 ∧ p.val = 1 ∧ l' = l ∧ semOK sem c d = true := by
  simp only [edgeObs] at hp
  split at hp
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have hp' := List.mem_singleton.mp hp
    exact ⟨hc.1.1, by rw [hp'], hc.1.2, hc.2⟩
  · exact absurd hp (List.not_mem_nil)

theorem accepts_oneEdge {G : Graph k} {l : Label} {u v : Fin G.size}
    (h : Accepts G (oneEdge l) u v) : G.edge u l = some v := by
  obtain ⟨q, hq, p, hp, hr⟩ := h
  have hq' : q.val = 0 := by rw [List.mem_singleton.mp hq]
  have hp' : p.val = 1 := by rw [List.mem_singleton.mp hp]
  rcases two_control_run (fun _ _ _ _ _ hm => ⟨(oneEdge_move hm).1, (oneEdge_move hm).2.1⟩) hq' hr
    with heq | ⟨-, l', he, hm, -⟩
  · have := congrArg (fun n : Node G (oneEdge l) => n.2.val) heq
    simp only at this
    omega
  · rw [← (oneEdge_move hm).2.2]
    exact he

theorem accepts_edgeObs {G : Graph k} {l : Label} {left right : Colour k → Bool}
    {sem : Option (Portal k)} {u v : Fin G.size}
    (h : Accepts G (edgeObs l left right sem) u v) :
    G.edge u l = some v ∧ left (G.colour u) = true ∧ right (G.colour v) = true ∧
      semOK sem (G.colour u) (G.colour v) = true := by
  obtain ⟨q, hq, p, hp, hr⟩ := h
  have hq' : q.val = 0 := by rw [List.mem_singleton.mp hq]
  have hp' : p.val = 1 := by rw [List.mem_singleton.mp hp]
  have hl : left (G.colour u) = true := by
    have ha := allowed_of_run G _ hr
    simp only [Allowed, edgeObs] at ha
    rwa [if_pos hq'] at ha
  rcases two_control_run (fun _ _ _ _ _ hm => ⟨(edgeObs_move hm).1, (edgeObs_move hm).2.1⟩) hq' hr
    with heq | ⟨-, l', he, hm, hz⟩
  · have := congrArg (fun n : Node G (edgeObs l left right sem) => n.2.val) heq
    simp only at this
    omega
  · obtain ⟨-, -, hl', hsem⟩ := edgeObs_move hm
    subst hl'
    refine ⟨he, hl, ?_, hsem⟩
    simp only [Allowed, edgeObs] at hz
    rwa [if_neg (by omega)] at hz

/-! ## Concatenating traces -/

/-- No cursor before the end of a labelled extension is the old endpoint. -/
def NoHit (B : Reference k) (v : Nat) (l : List (Bool × Fin k)) : Prop :=
  ∀ i, i < l.length → walkTo B v ((l.map Prod.fst).take i) ≠ B.word.length

theorem noHit_append {B : Reference k} {v : Nat} {l₁ l₂ : List (Bool × Fin k)}
    (h₁ : NoHit B v l₁) (h₂ : NoHit B (walkTo B v (l₁.map Prod.fst)) l₂) : NoHit B v (l₁ ++ l₂) := by
  intro i hi
  rw [List.map_append]
  by_cases hlt : i < l₁.length
  · rw [List.take_append_of_le_length (by simpa using Nat.le_of_lt hlt)]
    exact h₁ i hlt
  · have hlen : (l₁.map Prod.fst).length = l₁.length := List.length_map ..
    obtain ⟨j, rfl⟩ : ∃ j, i = (l₁.map Prod.fst).length + j := ⟨i - l₁.length, by omega⟩
    rw [List.take_length_add_append, walkTo_append]
    apply h₂
    simp only [List.length_append] at hi
    omega

theorem safeWalk_append {I : Instance k} {B : Reference k} : ∀ {v : Nat} {l₁ l₂ : List (Bool × Fin k)},
    SafeWalk I B v l₁ → SafeWalk I B (walkTo B v (l₁.map Prod.fst)) l₂ → SafeWalk I B v (l₁ ++ l₂) := by
  intro v l₁
  induction l₁ generalizing v with
  | nil => intro l₂ _ h₂; simpa [walkTo] using h₂
  | cons e rest ih =>
    intro l₂ h₁ h₂
    obtain ⟨b, p⟩ := e
    obtain ⟨hbad, hflag, hmask, hrest⟩ := h₁
    exact ⟨hbad, hflag, hmask, ih hrest (by simpa [walkTo] using h₂)⟩

theorem lastState_append (q : Fin k) (l₁ l₂ : List (Bool × Fin k)) :
    lastState q (l₁ ++ l₂) = lastState (lastState q l₁) l₂ := by
  induction l₁ generalizing q with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨b, p⟩ := e
    rw [List.cons_append, lastState_cons, lastState_cons, ih]

theorem revRun_append {I : Instance k} : ∀ {q : Fin k} {l₁ l₂ : List (Bool × Fin k)},
    RevRun I q l₁ → RevRun I (lastState q l₁) l₂ → RevRun I q (l₁ ++ l₂) := by
  intro q l₁
  induction l₁ generalizing q with
  | nil => intro l₂ _ h₂; simpa [lastState] using h₂
  | cons e rest ih =>
    intro l₂ h₁ h₂
    obtain ⟨b, p⟩ := e
    obtain ⟨hstep, hrest⟩ := h₁
    rw [lastState_cons] at h₂
    exact ⟨hstep, ih hrest h₂⟩

/-! ## Initial and final controls of the interval product -/

theorem interval_initial_spec {I : Instance k} {items : List (Active k)} {ql qr : Fin k}
    {nl nr : Option Bool} {q : Fin (intervalObs I items ql nl qr nr).size}
    (hq : q ∈ (intervalObs I items ql nl qr nr).initial) :
    ∃ x : IControl k, decodeI items q.val = some x ∧ x.state = ql ∧ x.next = nl ∧ x.seen = 0 ∧
      x.controls = items.map fun a => a.2.1 := by
  simp only [intervalObs] at hq
  have hq' := (List.mem_filter.mp hq).2
  cases hd : decodeI items q.val with
  | none => simp [hd] at hq'
  | some x =>
    simp only [hd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq'
    exact ⟨x, rfl, hq'.1.1.1, hq'.1.1.2, hq'.1.2, hq'.2⟩

theorem interval_final_spec {I : Instance k} {items : List (Active k)} {ql qr : Fin k}
    {nl nr : Option Bool} {q : Fin (intervalObs I items ql nl qr nr).size}
    (hq : q ∈ (intervalObs I items ql nl qr nr).final) :
    ∃ x : IControl k, decodeI items q.val = some x ∧ x.state = qr ∧ x.next = nr ∧ x.seen = 1 ∧
      x.controls = items.map fun a => a.2.2 := by
  simp only [intervalObs] at hq
  have hq' := (List.mem_filter.mp hq).2
  cases hd : decodeI items q.val with
  | none => simp [hd] at hq'
  | some x =>
    simp only [hd, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hq'
    exact ⟨x, rfl, hq'.1.1.1, hq'.1.1.2, hq'.1.2, hq'.2⟩

/-- An accepted interval atom yields a trace between its two origins with the
prescribed boundary controls. -/
theorem interval_trace (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k)
    {g : Nat} {u v : Fin (prefixGraph I B).size}
    (h : Accepts (prefixGraph I B) (intervalAtom I c D g).observer u v) :
    ∃ (x0 x1 : IControl k) (ext : List (Bool × Fin k)),
      Gen I B (itemsAt I c D g) u.val x0 ext v.val x1 ∧
      x0.state = markState D g ∧ x0.next = nextOf D g ∧ x0.seen = 0 ∧
      x0.controls = (itemsAt I c D g).map (fun a => a.2.1) ∧
      x1.state = markState D (g + 1) ∧ x1.next = nextOf D (g + 1) ∧ x1.seen = 1 ∧
      x1.controls = (itemsAt I c D g).map (fun a => a.2.2) := by
  obtain ⟨q, hq, p, hp, hr⟩ := h
  obtain ⟨x0, x1, ext, hd0, hd1, hgen'⟩ := run_gen I B _ _ _ _ _ hr
  obtain ⟨y0, hy0, hs0, hn0, hseen0, hc0⟩ := interval_initial_spec hq
  obtain ⟨y1, hy1, hs1, hn1, hseen1, hc1⟩ := interval_final_spec hp
  have e0 : y0 = x0 := Option.some.inj (hy0.symm.trans hd0)
  have e1 : y1 = x1 := Option.some.inj (hy1.symm.trans hd1)
  subst e0 e1
  exact ⟨y0, y1, ext, hgen', hs0, hn0, hseen0, hc0, hs1, hn1, hseen1, hc1⟩

/-! ## Assembly: a base model determines one first-return extension -/

/-- The data a base model `σ` of the compiled clause determines. -/
structure Recon (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k)
    (σ : Var D → Fin (prefixGraph I B).size) where
  exts : Nat → List (Bool × Fin k)
  x0 : Nat → IControl k
  x1 : Nat → IControl k
  gen : ∀ g, g < D.groups - 1 →
    Gen I B (itemsAt I c D g) (σ (zVar D g)).val (x0 g) (exts g) (σ (zVar D (g + 1))).val (x1 g)
  x0_state : ∀ g, g < D.groups - 1 → (x0 g).state = markState D g
  x0_next : ∀ g, g < D.groups - 1 → (x0 g).next = nextOf D g
  x0_controls : ∀ g, g < D.groups - 1 → (x0 g).controls = (itemsAt I c D g).map fun a => a.2.1
  x1_state : ∀ g, g < D.groups - 1 → (x1 g).state = markState D (g + 1)
  x1_next : ∀ g, g < D.groups - 1 → (x1 g).next = nextOf D (g + 1)
  x1_seen : ∀ g, g < D.groups - 1 → (x1 g).seen = 1
  x1_controls : ∀ g, g < D.groups - 1 → (x1 g).controls = (itemsAt I c D g).map fun a => a.2.2
  end_pos : (σ (endVar D)).val = B.word.length
  end_colour : colB I B (σ (endVar D)).val = D.oldEnd
  init_pos : (σ (initVar D)).val = failureParent B.word
  z0_pos : (σ (zVar D 0)).val = advance B.word (failureParent B.word) D.firstBit
  z0_mask : (mask I B (σ (zVar D 0)).val).get (markState D 0) = false
  z0_end : ((σ (zVar D 0)).val = B.word.length) ↔ D.groups = 1
  zlast : σ (zVar D (D.groups - 1)) = σ (endVar D)
  z_notEnd : ∀ j, j < D.groups - 1 → (σ (zVar D j)).val ≠ B.word.length

namespace Recon
variable {I : Instance k} {c : Clause k} {D : Diagram k} {B : Reference k}
  {σ : Var D → Fin (prefixGraph I B).size}

/-- The traces of the first `g` intervals, concatenated. -/
def pre (r : Recon I c D B σ) (g : Nat) : List (Bool × Fin k) := (List.range g).flatMap r.exts

/-- The whole labelled extension: the first emission, then every interval trace. -/
def ext (r : Recon I c D B σ) : List (Bool × Fin k) :=
  (D.firstBit, markState D 0) :: r.pre (D.groups - 1)

theorem pre_zero (r : Recon I c D B σ) : r.pre 0 = [] := rfl

theorem pre_succ (r : Recon I c D B σ) (g : Nat) : r.pre (g + 1) = r.pre g ++ r.exts g := by
  simp [pre, List.range_succ]

theorem pre_walk (r : Recon I c D B σ) : ∀ g, g ≤ D.groups - 1 →
    walkTo B (σ (zVar D 0)).val ((r.pre g).map Prod.fst) = (σ (zVar D g)).val := by
  intro g
  induction g with
  | zero => intro _; rfl
  | succ g ih =>
    intro hg
    rw [pre_succ, List.map_append, walkTo_append, ih (by omega), gen_walk (r.gen g (by omega))]

theorem pre_revRun (r : Recon I c D B σ) : ∀ g, g ≤ D.groups - 1 →
    RevRun I (markState D 0) (r.pre g) ∧ lastState (markState D 0) (r.pre g) = markState D g := by
  intro g
  induction g with
  | zero => intro _; exact ⟨trivial, rfl⟩
  | succ g ih =>
    intro hg
    obtain ⟨hrev, hlast⟩ := ih (by omega)
    have hgen := r.gen g (by omega)
    rw [pre_succ]
    refine ⟨revRun_append hrev ?_, ?_⟩
    · rw [hlast, ← r.x0_state g (by omega)]
      exact gen_revRun hgen
    · rw [lastState_append, hlast, ← r.x0_state g (by omega), gen_last hgen,
        r.x1_state g (by omega)]

theorem pre_safe (r : Recon I c D B σ) : ∀ g, g ≤ D.groups - 1 →
    SafeWalk I B (σ (zVar D 0)).val (r.pre g) := by
  intro g
  induction g with
  | zero => intro _; trivial
  | succ g ih =>
    intro hg
    rw [pre_succ]
    refine safeWalk_append (ih (by omega)) ?_
    rw [r.pre_walk g (by omega)]
    exact gen_safeWalk (r.gen g (by omega))

theorem pre_noHit (r : Recon I c D B σ) : ∀ g, g ≤ D.groups - 1 →
    NoHit B (σ (zVar D 0)).val (r.pre g) := by
  intro g
  induction g with
  | zero => intro _ i hi; simp [pre] at hi
  | succ g ih =>
    intro hg
    rw [pre_succ]
    refine noHit_append (ih (by omega)) ?_
    rw [r.pre_walk g (by omega)]
    exact gen_noHit (r.gen g (by omega))

theorem end_state (r : Recon I c D B σ) : D.oldEnd.state = B.label B.word.length := by
  have := congrArg Colour.state r.end_colour
  simp only [colB] at this
  rw [← this, r.end_pos]

/-- **Single generator.**  The extension determined by a base model is a safe
first-return extension of the base. -/
theorem firstReturnExt (r : Recon I c D B σ) (hB : SafeReference I B)
    (hv : validDiagram I c D = true) : FirstReturnExt I B (extRef B r.ext) := by
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, hstep, hbad, hflag⟩ := valid_facts I c D hv
  have hm : 0 < B.word.length := hB.nonempty
  have hL : 0 < r.ext.length := by simp [ext]
  have hrev : RevRun I (B.label B.word.length) r.ext := by
    refine ⟨?_, (r.pre_revRun (D.groups - 1) (Nat.le_refl _)).1⟩
    rw [← r.end_state]
    exact hstep
  have hz0 : advance B.word (failureParent B.word) D.firstBit = (σ (zVar D 0)).val := r.z0_pos.symm
  have hsafe : SafeWalk I B (failureParent B.word) r.ext := by
    refine ⟨hbad, hflag, ?_, ?_⟩
    · rw [hz0]; exact r.z0_mask
    · rw [hz0]; exact r.pre_safe (D.groups - 1) (Nat.le_refl _)
  have hend : walkTo B (failureParent B.word) (r.ext.map Prod.fst) = B.word.length := by
    simp only [ext, List.map_cons, walkTo]
    rw [hz0, r.pre_walk (D.groups - 1) (Nat.le_refl _), r.zlast, r.end_pos]
  have hno : ∀ i, 0 < i → i < r.ext.length →
      walkTo B (failureParent B.word) ((r.ext.map Prod.fst).take i) ≠ B.word.length := by
    intro i hi hilen
    cases i with
    | zero => omega
    | succ i =>
      simp only [ext, List.map_cons, List.take_succ_cons, walkTo]
      rw [hz0]
      apply r.pre_noHit (D.groups - 1) (Nat.le_refl _)
      simp only [ext, List.length_cons] at hilen
      omega
  refine ⟨extRef_safe I B hB r.ext hL hrev hsafe hend hno, List.prefix_append _ _,
    fun j hj => extRef_label_le B r.ext hj, ?_⟩
  exact extRef_firstReturn B hm (r.ext.map Prod.fst) (by simpa using hL) hend (by simpa using hno)

end Recon

/-- Every base model of a valid compiled clause yields the reconstruction data. -/
theorem exists_recon (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k)
    (hv : validDiagram I c D = true) (σ : Var D → Fin (prefixGraph I B).size)
    (htests : ∀ t ∈ (compileValid I c D).tests, t.2 ((prefixGraph I B).colour (σ t.1)) = true)
    (hequal : ∀ e ∈ (compileValid I c D).equal, σ e.1 = σ e.2)
    (hatoms : ∀ a ∈ (compileValid I c D).atoms,
      Accepts (prefixGraph I B) a.observer (σ a.source) (σ a.target)) :
    Nonempty (Recon I c D B σ) := by
  obtain ⟨hn, -, -, -, -, -, -, hisEnd, -, -, -, -, -⟩ := valid_facts I c D hv
  -- the old endpoint
  have hend := htests _ (mem_tests_end I c D)
  have hcol : colB I B (σ (endVar D)).val = D.oldEnd := of_decide_eq_true hend
  have hend_pos : (σ (endVar D)).val = B.word.length := by
    have := congrArg Colour.isEnd hcol
    simp only [colB] at this
    exact of_decide_eq_true (this.trans hisEnd)
  -- the failure edge from the endpoint
  have hF := accepts_oneEdge (hatoms _ (mem_atoms_F I c D))
  have hinit : (σ (initVar D)).val = failureParent B.word := by
    have this : failureParent (B.word.take (σ (endVar D)).val) = (σ (initVar D)).val :=
      congrArg Fin.val (Option.some.inj hF)
    rw [← this, hend_pos, List.take_length]
  -- the first emission
  obtain ⟨hKe, -, hKr, -⟩ := accepts_edgeObs (hatoms _ (mem_atoms_K I c D))
  have hz0 : (σ (zVar D 0)).val = advance B.word (failureParent B.word) D.firstBit := by
    have this : advance B.word (σ (initVar D)).val D.firstBit = (σ (zVar D 0)).val :=
      congrArg Fin.val (Option.some.inj hKe)
    rw [← this, hinit]
  simp only [prefixGraph_colour, colB, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hKr
  have hz0_end : ((σ (zVar D 0)).val = B.word.length) ↔ D.groups = 1 :=
    decide_eq_decide.mp hKr.2
  -- the last origin is the endpoint; earlier origins are not
  have hzlast := hequal _ (mem_equal_last I c D)
  have hnot : ∀ j, j < D.groups - 1 → (σ (zVar D j)).val ≠ B.word.length := by
    intro j hj
    have := htests _ (mem_tests_notEnd I c D hj)
    simp only [prefixGraph_colour, colB, Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this
  -- the interval traces
  have hall : ∀ g, ∃ t : IControl k × IControl k × List (Bool × Fin k), g < D.groups - 1 →
      Gen I B (itemsAt I c D g) (σ (zVar D g)).val t.1 t.2.2 (σ (zVar D (g + 1))).val t.2.1 ∧
      t.1.state = markState D g ∧ t.1.next = nextOf D g ∧ t.1.seen = 0 ∧
      t.1.controls = (itemsAt I c D g).map (fun a => a.2.1) ∧
      t.2.1.state = markState D (g + 1) ∧ t.2.1.next = nextOf D (g + 1) ∧ t.2.1.seen = 1 ∧
      t.2.1.controls = (itemsAt I c D g).map (fun a => a.2.2) := by
    intro g
    by_cases hg : g < D.groups - 1
    · obtain ⟨x0, x1, ext, hgen, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        interval_trace I c D B (hatoms _ (mem_atoms_interval I c D hg))
      exact ⟨(x0, x1, ext), fun _ => ⟨hgen, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩
    · exact ⟨(⟨markState D 0, none, 0, []⟩, ⟨markState D 0, none, 0, []⟩, []), fun h => absurd h hg⟩
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice hall
  exact ⟨{ exts := fun g => (f g).2.2, x0 := fun g => (f g).1, x1 := fun g => (f g).2.1,
           gen := fun g hg => (hf g hg).1,
           x0_state := fun g hg => (hf g hg).2.1, x0_next := fun g hg => (hf g hg).2.2.1,
           x0_controls := fun g hg => (hf g hg).2.2.2.2.1,
           x1_state := fun g hg => (hf g hg).2.2.2.2.2.1, x1_next := fun g hg => (hf g hg).2.2.2.2.2.2.1,
           x1_seen := fun g hg => (hf g hg).2.2.2.2.2.2.2.1,
           x1_controls := fun g hg => (hf g hg).2.2.2.2.2.2.2.2,
           end_pos := hend_pos, end_colour := hcol, init_pos := hinit, z0_pos := hz0,
           z0_mask := hKr.1, z0_end := hz0_end, zlast := hzlast, z_notEnd := hnot }⟩

/-- **Reverse direction, first half (single generator).**  A base model of a
compiled diagram clause determines one safe first-return extension of the base. -/
theorem compiled_extension (I : Instance k) (c : Clause k) (D : Diagram k) (B : Reference k)
    (hB : SafeReference I B) {P : Clause k} (hP : compileDiagram I c D = some P)
    (hsat : SatClause (prefixGraph I B) P) :
    ∃ C : Reference k, FirstReturnExt I B C := by
  unfold compileDiagram at hP
  split at hP
  · rename_i hv
    have hPe : P = compileValid I c D := (Option.some.inj hP).symm
    subst hPe
    obtain ⟨σ, htests, hequal, -, hatoms⟩ := hsat
    obtain ⟨r⟩ := exists_recon I c D B hv σ htests hequal hatoms
    exact ⟨extRef B r.ext, r.firstReturnExt hB hv⟩
  · contradiction

/-! ## Colours and edges of the extension graph -/

theorem get_ofFn (f : Fin k → Bool) (p : Fin k) : (Vector.ofFn f).get p = f p := by
  simp [Vector.get] <;> rfl

theorem next_iff_getElem? {w : Word} {i : Nat} (hi : i < w.length) (b : Bool) :
    FirstReturnGraph.Next w i b ↔ w[i]? = some b := by
  unfold FirstReturnGraph.Next
  rw [List.take_succ_eq_append_getElem hi, List.getElem?_eq_getElem hi]
  constructor
  · intro h
    have := List.append_cancel_left h
    simp only [List.cons.injEq, and_true] at this
    rw [this]
  · intro h
    rw [Option.some.inj h]

section ExtGraph
variable (I : Instance k) (B : Reference k) (ext : List (Bool × Fin k))

theorem colC_old {j : Nat} (hj : j < B.word.length) :
    colB I (extRef B ext) j = colB I B j := by
  have hjC : ¬ j = (extRef B ext).word.length := by rw [extRef_length]; omega
  have hjm : ¬ j = B.word.length := by omega
  simp only [colB, extRef_label_le B ext (Nat.le_of_lt hj), extRef_mask_le I B ext (Nat.le_of_lt hj),
    extRef_getElem?_lt B ext hj, decide_eq_false hjC, decide_eq_false hjm]

theorem colC_m (a : Bool) (p : Fin k) (rest : List (Bool × Fin k)) :
    colB I (extRef B ((a, p) :: rest)) B.word.length = coreMap a (colB I B B.word.length) := by
  have hne : ¬ B.word.length = (extRef B ((a, p) :: rest)).word.length := by
    rw [extRef_length]; simp
  have hw : (extRef B ((a, p) :: rest)).word[B.word.length]? = some a := by
    have := extRef_getElem? B ((a, p) :: rest) 0
    simpa using this
  simp only [colB, coreMap, extRef_label_le B _ (Nat.le_refl _), extRef_mask_le I B _ (Nat.le_refl _),
    hw, decide_eq_false hne, decide_true, if_true]

theorem cursor_le (hm : 0 < B.word.length) {d : Nat} (hd : d ≤ ext.length) :
    FirstReturnGraph.cursor (extRef B ext).word B.word.length d ≤ B.word.length := by
  rw [extRef_word, cursor_eq_walk B _ (by simpa using hd)]
  have hfp : failureParent B.word ≤ B.word.length := by
    have := failureParent_take_le B.word B.word.length
    simpa using this
  exact walkTo_le B hfp _

theorem frMask_ext (hm : 0 < B.word.length) {cur : Nat} (hcur : cur ≤ B.word.length) (q : Fin k) :
    FirstReturnGraph.mask ((extRef B ext).word.take B.word.length) (fun p t => (I.flags.get p).get t)
      (extRef B ext).label cur q = (mask I B cur).get q := by
  rw [extRef_take, frMask_congr _ (r' := B.label) (fun h hh => extRef_label_le B ext (Nat.le_trans hh hcur)),
    ← RankQueryFirstReturn.mask_get_eq]

/-- A fresh vertex has the colour the compiler's `freshMap` assigns at its cursor. -/
theorem colC_fresh (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    {j : Nat} (hmj : B.word.length < j) (hj : j ≤ (extRef B ext).word.length) :
    colB I (extRef B ext) j =
      freshMap I ((extRef B ext).label j) ((extRef B ext).word[j]?)
        (colB I B (FirstReturnGraph.cursor (extRef B ext).word B.word.length (j - B.word.length))) := by
  have h := RankQueryFirstReturn.colour_eq_surgery I (extRef B ext) hm hr ⟨j, by omega⟩
  refine (h : colB I (extRef B ext) j = _).trans ?_
  have h1 : ¬ j < B.word.length := by omega
  have h2 : ¬ j = B.word.length := by omega
  have hlen := extRef_length B ext
  have hcur := cursor_le B ext hm (d := j - B.word.length) (by omega)
  simp only [FirstReturnGraph.surgeryColour, h1, h2, if_false, RankQueryFirstReturn.toQueryColour,
    freshMap, colB]
  refine Colour.mk.injEq _ _ _ _ _ _ _ _ _ _ |>.mpr ⟨rfl, ?_, rfl, rfl, ?_⟩
  · simp only [orMask, column]
    congr 1
    funext q
    rw [get_ofFn, frMask_ext I B ext hm hcur q, Bool.or_comm]
  · by_cases hje : j = (extRef B ext).word.length
    · simp [hje]
    · have hlt : j < (extRef B ext).word.length := by omega
      simp [hje, List.getElem?_eq_getElem hlt]

end ExtGraph

section ExtEdges
variable (I : Instance k) (B : Reference k) (ext : List (Bool × Fin k))

/-- Edge destinations of the extension graph, by position. -/
def edgeC (j : Nat) (hj : j ≤ (extRef B ext).word.length) (l : Label) : Option Nat :=
  ((prefixGraph I (extRef B ext)).edge ⟨j, Nat.lt_succ_of_le hj⟩ l).map Fin.val

theorem edgeC_eq (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    {j : Nat} (hj : j ≤ (extRef B ext).word.length) (l : Label) :
    edgeC I B ext j hj l = RankQueryFirstReturn.rowTarget
      (FirstReturnGraph.surgeryEdges (extRef B ext).word B.word.length j) l :=
  RankQueryFirstReturn.edge_eq_surgery I (extRef B ext) hm hr ⟨j, Nat.lt_succ_of_le hj⟩ l

theorem edgeC_F_old (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    {j : Nat} (hj : j ≤ B.word.length) (hjC : j ≤ (extRef B ext).word.length) :
    edgeC I B ext j hjC .F = some (failureParent (B.word.take j)) := by
  rw [edgeC_eq I B ext hm hr]
  simp [RankQueryFirstReturn.rowTarget, FirstReturnGraph.surgeryEdges, hj, extRef_take]

theorem edgeC_F_fresh (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    {j : Nat} (hmj : B.word.length < j) (hjC : j ≤ (extRef B ext).word.length) :
    edgeC I B ext j hjC .F =
      some (FirstReturnGraph.cursor (extRef B ext).word B.word.length (j - B.word.length)) := by
  rw [edgeC_eq I B ext hm hr]
  have h : ¬ j ≤ B.word.length := by omega
  simp [RankQueryFirstReturn.rowTarget, FirstReturnGraph.surgeryEdges, h]

theorem edgeC_S (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    {j : Nat} (hjC : j ≤ (extRef B ext).word.length) :
    edgeC I B ext j hjC .S = if j < (extRef B ext).word.length then some (j + 1) else none := by
  rw [edgeC_eq I B ext hm hr]
  have hlen := extRef_length B ext
  have hmlt : B.word.length < (extRef B ext).word.length := hr.1
  by_cases h : j < B.word.length
  · have h2 : j < (extRef B ext).word.length := by omega
    have h1 : j < min B.word.length (extRef B ext).word.length := Nat.lt_min.mpr ⟨h, h2⟩
    simp [RankQueryFirstReturn.rowTarget, FirstReturnGraph.surgeryEdges, h, h1, h2]
  · simp [RankQueryFirstReturn.rowTarget, FirstReturnGraph.surgeryEdges, h]

theorem surgeryK_value (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    {j : Nat} (hjC : j ≤ (extRef B ext).word.length) (b : Bool) :
    edgeC I B ext j hjC (.K b) = some (FirstReturnGraph.surgeryK (extRef B ext).word B.word.length j b) := by
  rw [edgeC_eq I B ext hm hr]
  cases b <;> rfl

theorem edgeC_K_old (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    {j : Nat} (hj : j < B.word.length) (hjC : j ≤ (extRef B ext).word.length) (b : Bool) :
    edgeC I B ext j hjC (.K b) = some (advance B.word j b) := by
  rw [surgeryK_value I B ext hm hr, FirstReturnGraph.surgeryK, if_pos hj, extRef_take,
    RankQueryFirstReturn.advance_eq (Nat.le_of_lt hj)]

theorem edgeC_K_m (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    (hjC : B.word.length ≤ (extRef B ext).word.length) (b : Bool) :
    edgeC I B ext B.word.length hjC (.K b) =
      some (if (extRef B ext).word[B.word.length]? = some b then B.word.length + 1
        else advance B.word B.word.length b) := by
  rw [surgeryK_value I B ext hm hr, FirstReturnGraph.surgeryK, if_neg (Nat.lt_irrefl _), if_pos rfl,
    extRef_take, RankQueryFirstReturn.advance_eq (Nat.le_refl _)]
  have hmlt : B.word.length < (extRef B ext).word.length := hr.1
  simp only [next_iff_getElem? hmlt]

theorem edgeC_K_fresh (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length)
    {j : Nat} (hmj : B.word.length < j) (hj : j < (extRef B ext).word.length) (b : Bool) :
    edgeC I B ext j (Nat.le_of_lt hj) (.K b) =
      some (if (extRef B ext).word[j]? = some b then j + 1
        else advance B.word (FirstReturnGraph.cursor (extRef B ext).word B.word.length (j - B.word.length)) b) := by
  have h1 : ¬ j < B.word.length := by omega
  have h2 : ¬ j = B.word.length := by omega
  have hcur := cursor_le B ext hm (d := j - B.word.length) (by have := extRef_length B ext; omega)
  rw [surgeryK_value I B ext hm hr, FirstReturnGraph.surgeryK, if_neg h1, if_neg h2, if_pos hj,
    extRef_take, RankQueryFirstReturn.advance_eq hcur]
  simp only [next_iff_getElem? hj]

theorem edgeC_K_end (hm : 0 < B.word.length)
    (hr : FirstReturn (extRef B ext).word B.word.length (extRef B ext).word.length) (b : Bool) :
    edgeC I B ext (extRef B ext).word.length (Nat.le_refl _) (.K b) =
      some (if (extRef B ext).word[B.word.length]? = some b then B.word.length + 1
        else advance B.word B.word.length b) := by
  have hmlt : B.word.length < (extRef B ext).word.length := hr.1
  have h1 : ¬ (extRef B ext).word.length < B.word.length := by omega
  have h2 : ¬ (extRef B ext).word.length = B.word.length := by omega
  rw [surgeryK_value I B ext hm hr, FirstReturnGraph.surgeryK, if_neg h1, if_neg h2,
    if_neg (Nat.lt_irrefl _), extRef_take, RankQueryFirstReturn.advance_eq (Nat.le_refl _)]
  simp only [next_iff_getElem? hmlt]

/-- Recover the `Fin`-valued edge from its position value. -/
theorem edge_of_edgeC {j j' : Nat} (hj : j ≤ (extRef B ext).word.length) {l : Label}
    (h : edgeC I B ext j hj l = some j') :
    ∃ h' : j' < (prefixGraph I (extRef B ext)).size,
      (prefixGraph I (extRef B ext)).edge ⟨j, Nat.lt_succ_of_le hj⟩ l = some ⟨j', h'⟩ := by
  unfold edgeC at h
  cases he : (prefixGraph I (extRef B ext)).edge ⟨j, Nat.lt_succ_of_le hj⟩ l with
  | none => simp [he] at h
  | some w =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨w.isLt, rfl⟩

end ExtEdges

end RankQuerySound
end Subtail
