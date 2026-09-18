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

end RankQuerySound
end Subtail
