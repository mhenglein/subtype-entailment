import Subtail.Basic
import Subtail.TerminalRank

/-!
# Absorbing terminal restriction

This module isolates the finite-state continuation step used by the
semantic bridge.  `terminalize` keeps the original instance data and prunes
only unsafe edges.  Its accepting states are the safe original accepting
states which have no remaining edge.
-/
namespace Subtail
namespace AbsorbingTerminal

variable {k : Nat}

/-- A state is safe when it is neither bad nor diagonally flagged. -/
def safeState (I : Instance k) (q : Fin k) : Bool :=
  !(I.bad.get q) && !((I.flags.get q).get q)

/-- Absorption: a defined successor of an original final is a final with an
empty incoming flag column. -/
def Absorbing (I : Instance k) : Prop :=
  ∀ f : Fin k, I.final.get f = true → ∀ a : Bool, ∀ q : Fin k,
    step I f a = some q →
      I.final.get q = true ∧ ∀ p : Fin k, (I.flags.get p).get q = false

/-- A run with every prefix, including its starting cut, defined and safe. -/
def safeCut (I : Instance k) (q : Fin k) (w : Word) (i : Nat) : Prop :=
  ∃ r : Fin k, runFrom I q (w.take i) = some r ∧ safeState I r = true

def SafeRun (I : Instance k) (q : Fin k) (w : Word) (r : Fin k) : Prop :=
  runFrom I q w = some r ∧ ∀ i : Nat, i ≤ w.length → safeCut I q w i

/-- The transition relation retained by `terminalize`. -/
def terminalStep (I : Instance k) (q : Fin k) (a : Bool) : Option (Fin k) :=
  if safeState I q = true then
    match step I q a with
    | none => none
    | some r => if safeState I r = true then some r else none
  else none

/-- Original final, safe, and with no edge after unsafe-edge pruning. -/
def terminalFinal (I : Instance k) (q : Fin k) : Bool :=
  I.final.get q && safeState I q &&
    (terminalStep I q false).isNone && (terminalStep I q true).isNone

/-- Remove unsafe-source and unsafe-target transitions, retaining all other
instance fields.  Finality is always tested against the ORIGINAL finals. -/
def terminalize (I : Instance k) : Instance k :=
  { initial := I.initial
    transitions := Vector.ofFn (fun q =>
      (terminalStep I q false, terminalStep I q true))
    bad := I.bad
    final := Vector.ofFn (terminalFinal I)
    flags := I.flags }

/-- An original witness whose endpoint has a safe nonempty cyclic
continuation.  The cycle is finite and explicitly nonempty. -/
def InfWitness (I : Instance k) : Prop :=
  ∃ w : Word, ∃ q : Fin k, ∃ v : Word, ∃ r : Fin k, ∃ c : Word,
    Witness I w ∧ stateAt I w w.length = some q ∧
    SafeRun I q v r ∧ SafeRun I r c r ∧ c ≠ []

theorem vector_get_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp only [Vector.get, Vector.ofFn, Array.getElem_ofFn]
  congr 1

theorem safeState_iff (I : Instance k) (q : Fin k) :
    safeState I q = true ↔ I.bad.get q = false ∧ (I.flags.get q).get q = false := by
  simp [safeState, Bool.and_eq_true]

theorem safeCut_zero_iff (I : Instance k) (q : Fin k) (w : Word) :
    safeCut I q w 0 ↔ safeState I q = true := by
  constructor
  · rintro ⟨r, hr, hs⟩
    have hqr : r = q := (Option.some.inj (by simpa [runFrom] using hr)).symm
    simpa [hqr] using hs
  · intro hs
    exact ⟨q, by simp [runFrom], hs⟩

theorem terminalStep_eq (I : Instance k) {q r : Fin k} {a : Bool}
    (hq : safeState I q = true) (hr : safeState I r = true)
    (h : step I q a = some r) : terminalStep I q a = some r := by
  unfold terminalStep
  rw [if_pos hq]
  cases hs : step I q a with
  | none => simp [hs] at h
  | some s =>
    have hsr : s = r := by
      simp [hs] at h
      exact h
    subst r
    simp [hr]

theorem terminalStep_original_none (I : Instance k) {q : Fin k} {a : Bool}
    (hq : safeState I q = true) (h : step I q a = none) :
    terminalStep I q a = none := by
  simp [terminalStep, hq, h]

theorem terminalStep_safe_source (I : Instance k) {q r : Fin k} {a : Bool}
    (h : terminalStep I q a = some r) :
    safeState I q = true ∧ safeState I r = true ∧ step I q a = some r := by
  by_cases hq : safeState I q = true
  · unfold terminalStep at h
    rw [if_pos hq] at h
    cases hs : step I q a with
    | none => simp [hs] at h
    | some s =>
      by_cases hrs : safeState I s = true
      · have hsr : s = r := by simpa [hs, hrs] using h
        subst r
        exact ⟨hq, hrs, rfl⟩
      · simp [hs, hrs] at h
  · simp [terminalStep, hq] at h

theorem terminalize_step (I : Instance k) (q : Fin k) (a : Bool) :
    step (terminalize I) q a = terminalStep I q a := by
  cases a <;> simp [step, terminalize, vector_get_ofFn]

theorem safeCheck_terminalize (I : Instance k) (o : Option (Fin k)) :
    safeCheck (terminalize I) o = safeCheck I o := by
  cases o <;> rfl

theorem unflaggedCheck_terminalize (I : Instance k)
    (p q : Option (Fin k)) :
    unflaggedCheck (terminalize I) p q = unflaggedCheck I p q := by
  cases p <;> cases q <;> rfl

theorem terminalFinal_original (I : Instance k) {q : Fin k}
    (h : terminalFinal I q = true) : I.final.get q = true := by
  have hp : I.final.get q = true ∧ safeState I q = true ∧
      (terminalStep I q false).isNone = true ∧
      (terminalStep I q true).isNone = true := by
    simpa [terminalFinal, Bool.and_eq_true, and_assoc] using h
  exact hp.1

theorem safeCut_cons_of_step (I : Instance k) {q s : Fin k} {a : Bool}
    {w : Word} {i : Nat} (hstep : step I q a = some s)
    (h : safeCut I q (a :: w) (i + 1)) : safeCut I s w i := by
  rcases h with ⟨r, hr, hs⟩
  refine ⟨r, ?_, hs⟩
  have htake : (a :: w).take (i + 1) = [a] ++ w.take i := by
    simp [List.take]
  rw [htake, runFrom_append] at hr
  simp [runFrom, hstep] at hr
  exact hr

theorem runFrom_terminalize_to_original (I : Instance k) {q r : Fin k}
    {w : Word} (hsafe : ∀ i, i ≤ w.length → safeCut I q w i)
    (hJ : runFrom (terminalize I) q w = some r) :
    runFrom I q w = some r := by
  induction w generalizing q r with
  | nil => simpa [runFrom] using hJ
  | cons a w ih =>
    have hJ' : (terminalStep I q a).bind (fun s => runFrom (terminalize I) s w) =
        some r := by
      simpa [runFrom, terminalize_step] using hJ
    cases hts : terminalStep I q a with
    | none => simp [hts] at hJ'
    | some s =>
      have hstep : step I q a = some s :=
        (terminalStep_safe_source I hts).2.2
      have htail : runFrom (terminalize I) s w = some r := by
        simpa [hts] using hJ'
      have hsafeTail : ∀ i, i ≤ w.length → safeCut I s w i := by
        intro i hi
        apply safeCut_cons_of_step I hstep
        apply hsafe (i + 1)
        simp only [List.length_cons]
        omega
      have htail' := ih hsafeTail htail
      simp [runFrom, hstep, htail']

theorem runFrom_terminalize_to_original_safeJ (I : Instance k) {q r : Fin k}
    {w : Word}
    (hsafe : ∀ i, i ≤ w.length → safeCut (terminalize I) q w i)
    (hJ : runFrom (terminalize I) q w = some r) :
    runFrom I q w = some r := by
  induction w generalizing q r with
  | nil => simpa [runFrom] using hJ
  | cons a w ih =>
    have hJ' : (terminalStep I q a).bind (fun s => runFrom (terminalize I) s w) =
        some r := by
      simpa [runFrom, terminalize_step] using hJ
    cases hts : terminalStep I q a with
    | none => simp [hts] at hJ'
    | some s =>
      have hstepJ : step (terminalize I) q a = some s := by
        rw [terminalize_step]
        exact hts
      have hstep : step I q a = some s :=
        (terminalStep_safe_source I hts).2.2
      have htail : runFrom (terminalize I) s w = some r := by
        simpa [hts] using hJ'
      have hsafeTail : ∀ i, i ≤ w.length → safeCut (terminalize I) s w i := by
        intro i hi
        apply safeCut_cons_of_step (terminalize I) hstepJ
        apply hsafe (i + 1)
        simp only [List.length_cons]
        omega
      have htail' := ih hsafeTail htail
      simp [runFrom, hstep, htail']

theorem runFrom_original_to_terminalize_safeI (I : Instance k) {q r : Fin k}
    {w : Word} (hsafe : ∀ i, i ≤ w.length → safeCut I q w i)
    (hI : runFrom I q w = some r) :
    runFrom (terminalize I) q w = some r := by
  induction w generalizing q r with
  | nil => simpa [runFrom] using hI
  | cons a w ih =>
    have hI' : (step I q a).bind (fun s => runFrom I s w) = some r := by
      simpa [runFrom] using hI
    cases hs : step I q a with
    | none => simp [hs] at hI'
    | some s =>
      have htail : runFrom I s w = some r := by simpa [hs] using hI'
      have hqSafe : safeState I q = true :=
        (safeCut_zero_iff I q (a :: w)).mp (hsafe 0 (by simp))
      have hsSafe : safeState I s = true := by
        apply (safeCut_zero_iff I s w).mp
        apply safeCut_cons_of_step I hs
        apply hsafe 1
        simp only [List.length_cons]
        omega
      have hterm : terminalStep I q a = some s :=
        terminalStep_eq I hqSafe hsSafe hs
      have hsafeTail : ∀ i, i ≤ w.length → safeCut I s w i := by
        intro i hi
        apply safeCut_cons_of_step I hs
        apply hsafe (i + 1)
        simp only [List.length_cons]
        omega
      have htail' := ih hsafeTail htail
      simp [terminalize_step, runFrom, hterm, htail']

theorem stateAt_original_to_terminalize_safeI (I : Instance k) {w : Word}
    (hsafe : ∀ i, i ≤ w.length → safeCut I I.initial w i) :
    ∀ i, i ≤ w.length → stateAt (terminalize I) w i = stateAt I w i := by
  intro i hi
  have hsafePrefix : ∀ j, j ≤ (w.take i).length → safeCut I I.initial (w.take i) j := by
    intro j hj
    have hji : j ≤ i := by
      simp only [List.length_take] at hj
      omega
    rcases hsafe j (Nat.le_trans hji hi) with ⟨r, hr, hs⟩
    refine ⟨r, ?_, hs⟩
    simpa [List.take_take, Nat.min_eq_left hji] using hr
  rcases hsafe i hi with ⟨q, hrunI, _⟩
  have hrunJ := runFrom_original_to_terminalize_safeI I hsafePrefix hrunI
  have hstateJ : stateAt (terminalize I) w i = some q := by
    simpa [stateAt, terminalize] using hrunJ
  have hstateI : stateAt I w i = some q := by
    simpa [stateAt] using hrunI
  rw [hstateJ, hstateI]

theorem exists_terminalStep_of_not_terminal (I : Instance k) {q : Fin k}
    (h : ¬ ∀ a : Bool, terminalStep I q a = none) :
    ∃ a r, terminalStep I q a = some r := by
  cases h0 : terminalStep I q false with
  | some r => exact ⟨false, r, h0⟩
  | none =>
    cases h1 : terminalStep I q true with
    | some r => exact ⟨true, r, h1⟩
    | none =>
      exact False.elim (h (by
        intro a
        cases a
        · exact h0
        · exact h1))

theorem safeRun_one_of_terminalStep (I : Instance k) {q r : Fin k} {a : Bool}
    (h : terminalStep I q a = some r) : SafeRun I q [a] r := by
  have hs := terminalStep_safe_source I h
  refine ⟨?_, ?_⟩
  · simpa [runFrom, terminalize_step] using hs.2.2
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hcases : i = 0 ∨ i = 1 := by omega
    rcases hcases with rfl | rfl
    · exact (safeCut_zero_iff I q [a]).2 hs.1
    · refine ⟨r, ?_, hs.2.1⟩
      simpa [runFrom] using hs.2.2

theorem witness_safeCut (I : Instance k) {w : Word} (hw : Witness I w) :
    ∀ i, i ≤ w.length → safeCut I I.initial w i := by
  intro i hi
  have hs := hw.1 i hi
  cases hq : stateAt I w i with
  | none => simp [safeCheck, hq] at hs
  | some q =>
    have hbad : I.bad.get q = false := by
      simpa [safeCheck, hq] using hs
    have hdiag := hw.2.2 i hi i (Nat.le_refl i) (List.prefix_refl _)
    have hflag : (I.flags.get q).get q = false := by
      simpa [unflaggedCheck, hq] using hdiag
    refine ⟨q, ?_, (safeState_iff I q).2 ⟨hbad, hflag⟩⟩
    simpa [stateAt, hq]

theorem stateAt_terminalize_to_original_safeJ (I : Instance k) {w : Word}
    (hsafe : ∀ i, i ≤ w.length → safeCut (terminalize I) I.initial w i) :
    ∀ i, i ≤ w.length → stateAt I w i = stateAt (terminalize I) w i := by
  intro i hi
  have hsafePrefix : ∀ j, j ≤ (w.take i).length →
      safeCut (terminalize I) I.initial (w.take i) j := by
    intro j hj
    have hji : j ≤ i := by
      simp only [List.length_take] at hj
      omega
    rcases hsafe j (Nat.le_trans hji hi) with ⟨r, hr, hs⟩
    refine ⟨r, ?_, hs⟩
    simpa [List.take_take, Nat.min_eq_left hji] using hr
  cases hq : stateAt (terminalize I) w i with
  | none =>
    rcases hsafe i hi with ⟨q, hrun, hs⟩
    have hq' : stateAt (terminalize I) w i = some q := by
      simpa [stateAt, terminalize] using hrun
    rw [hq] at hq'
    simp at hq'
  | some q =>
    have hrunJ : runFrom (terminalize I) I.initial (w.take i) = some q := by
      simpa [stateAt, hq]
    have hrunI := runFrom_terminalize_to_original_safeJ I hsafePrefix hrunJ
    simpa [stateAt, hq] using hrunI

theorem terminalize_witness_to_original (I : Instance k) {w : Word}
    (hw : Witness (terminalize I) w) : Witness I w := by
  have hsafeJ' := witness_safeCut (terminalize I) hw
  have hsafeJ : ∀ i, i ≤ w.length →
      safeCut (terminalize I) I.initial w i := by
    intro i hi
    simpa [terminalize] using hsafeJ' i hi
  have hstate := stateAt_terminalize_to_original_safeJ I hsafeJ
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hstate i hi]
    rw [← safeCheck_terminalize I]
    exact hw.1 i hi
  · rw [hstate w.length (Nat.le_refl _)]
    cases hq : stateAt (terminalize I) w w.length with
    | none =>
      have hf := hw.2.1
      simp [finalCheck, hq] at hf
    | some q =>
      have hf := hw.2.1
      rw [hq] at hf
      have hterm : terminalFinal I q = true := by
        simpa [finalCheck, terminalize, vector_get_ofFn] using hf
      have hfin := terminalFinal_original I hterm
      simpa [finalCheck, hq] using hfin
  · intro j hj i hij ha
    have hil : i ≤ w.length := Nat.le_trans hij hj
    rw [hstate j hj, hstate i hil]
    rw [← unflaggedCheck_terminalize I]
    exact hw.2.2 j hj i hij ha

theorem safeCut_append_left (I : Instance k) {q : Fin k} {u v : Word}
    {i : Nat} (h : safeCut I q u i) (hi : i ≤ u.length) :
    safeCut I q (u ++ v) i := by
  rcases h with ⟨r, hr, hs⟩
  refine ⟨r, ?_, hs⟩
  simpa [List.take_append_of_le_length hi] using hr

theorem safeCut_append_right (I : Instance k) {q s : Fin k} {u v : Word}
    (hu : runFrom I q u = some s) {d : Nat} (h : safeCut I s v d) :
    safeCut I q (u ++ v) (u.length + d) := by
  rcases h with ⟨r, hr, hs⟩
  refine ⟨r, ?_, hs⟩
  have ht : (u ++ v).take (u.length + d) = u ++ v.take d := by
    rw [List.take_append]
    rw [List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  rw [ht, runFrom_append, hu]
  simpa using hr

theorem safeRun_append (I : Instance k) {q s r : Fin k} {u v : Word}
    (hu : SafeRun I q u s) (hv : SafeRun I s v r) :
    SafeRun I q (u ++ v) r := by
  refine ⟨?_, ?_⟩
  · rw [runFrom_append, hu.1]
    simpa using hv.1
  · intro i hi
    by_cases hleft : i ≤ u.length
    · exact safeCut_append_left I (hu.2 i hleft) hleft
    · have hright : i - u.length ≤ v.length := by
        have := hi
        simp only [List.length_append] at this
        omega
      have hs := hv.2 (i - u.length) hright
      have hidx : u.length + (i - u.length) = i := by omega
      rw [← hidx]
      exact safeCut_append_right I hu.1 hs

theorem safeRun_final (I : Instance k) (hA : Absorbing I)
    {q r : Fin k} {w : Word} (hq : I.final.get q = true)
    (hw : SafeRun I q w r) : I.final.get r = true := by
  induction w generalizing q r with
  | nil =>
    have hqr : q = r := Option.some.inj (by simpa [runFrom] using hw.1)
    simpa [hqr] using hq
  | cons a w ih =>
    have hrun := hw.1
    change (step I q a).bind (fun s => runFrom I s w) = some r at hrun
    cases hs : step I q a with
    | none => simp [hs] at hrun
    | some s =>
      have htail : runFrom I s w = some r := by simpa [hs] using hrun
      have hsafeTail : ∀ i, i ≤ w.length → safeCut I s w i := by
        intro i hi
        apply safeCut_cons_of_step I hs
        apply hw.2 (i + 1)
        simp only [List.length_cons]
        omega
      have hfs : I.final.get s = true := (hA q hq a s hs).1
      exact ih hfs ⟨htail, hsafeTail⟩

theorem safeRun_emptyIncoming (I : Instance k) (hA : Absorbing I)
    {q r : Fin k} {w : Word} (hq : I.final.get q = true)
    (hw : SafeRun I q w r) (hne : w ≠ []) :
    ∀ p : Fin k, (I.flags.get p).get r = false := by
  induction w generalizing q r with
  | nil => exact False.elim (hne rfl)
  | cons a w ih =>
    have hrun := hw.1
    change (step I q a).bind (fun s => runFrom I s w) = some r at hrun
    cases hs : step I q a with
    | none => simp [hs] at hrun
    | some s =>
      have htail : runFrom I s w = some r := by simpa [hs] using hrun
      have hfs : I.final.get s = true := (hA q hq a s hs).1
      cases w with
      | nil =>
        have hsr : s = r := by simpa [runFrom] using htail
        intro p
        simpa [hsr] using (hA q hq a s hs).2 p
      | cons b w =>
        have hsafeTail : ∀ i, i ≤ (b :: w).length → safeCut I s (b :: w) i := by
          intro i hi
          apply safeCut_cons_of_step I hs
          apply hw.2 (i + 1)
          simpa [List.length_cons] using Nat.succ_le_succ hi
        exact ih hfs ⟨htail, hsafeTail⟩ (by simp)

theorem safeRun_prefix (I : Instance k) {q r s : Fin k} {v : Word}
    (hv : SafeRun I q v r) {d : Nat} (hd : d ≤ v.length)
    (hr : runFrom I q (v.take d) = some s) :
    SafeRun I q (v.take d) s := by
  refine ⟨hr, ?_⟩
  intro i hi
  have hid : i ≤ d := by
    simp only [List.length_take] at hi
    omega
  rcases hv.2 i (by omega) with ⟨s, hs, hsafe⟩
  refine ⟨s, ?_, hsafe⟩
  simpa [List.take_take, Nat.min_eq_left hid] using hs

theorem stateAt_append_left (I : Instance k) {u v : Word} {i : Nat}
    (hi : i ≤ u.length) :
    stateAt I (u ++ v) i = stateAt I u i := by
  simp [stateAt, List.take_append_of_le_length hi]

theorem stateAt_append_right (I : Instance k) {s : Fin k} {u v : Word}
    (hu : runFrom I I.initial u = some s) (d : Nat) :
    stateAt I (u ++ v) (u.length + d) = runFrom I s (v.take d) := by
  have ht : (u ++ v).take (u.length + d) = u ++ v.take d := by
    rw [List.take_append]
    rw [List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
  rw [stateAt, ht, runFrom_append, hu]
  rfl

theorem agrees_append_left {u v : Word} {i j : Nat}
    (hi : i ≤ j) (hj : j ≤ u.length) (h : Agrees (u ++ v) i j) :
    Agrees u i j := by
  unfold Agrees at h ⊢
  rcases h with ⟨z, hz⟩
  have hm : u.length - j ≤ u.length - i := by omega
  have htake := congrArg (List.take (u.length - j)) hz
  have hleft : List.take (u.length - j) ((u ++ v).drop i) =
      List.take (u.length - j) (u.drop i) := by
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.take_append_of_le_length]
    simp only [List.length_drop]
    omega
  have hright : List.take (u.length - j) ((u ++ v).drop j) = u.drop j := by
    rw [List.drop_append_of_le_length hj]
    rw [List.take_append_of_le_length (by
      have hlen : (u.drop j).length = u.length - j := by simp
      omega)]
    exact List.take_of_length_le (by
      have hlen : (u.drop j).length = u.length - j := by simp
      omega)
  have hconcat : List.take (u.length - j) ((u ++ v).drop j ++ z) =
      List.take (u.length - j) ((u ++ v).drop j) := by
    rw [List.take_append_of_le_length]
    simp only [List.length_drop, List.length_append]
    omega
  rw [hconcat, hright, hleft] at htake
  have hp : List.take (u.length - j) (u.drop i) = u.drop j := by
    exact htake.symm
  refine ⟨(u.drop i).drop (u.length - j), ?_⟩
  rw [← hp, List.take_append_drop]

theorem witness_append_safeRun (I : Instance k) (hA : Absorbing I)
    {u v : Word} {q r : Fin k} (hu : Witness I u)
    (hq : stateAt I u u.length = some q) (hv : SafeRun I q v r) :
    Witness I (u ++ v) := by
  have hrunU : runFrom I I.initial u = some q := by
    simpa [stateAt] using hq
  have hqfinal : I.final.get q = true := by
    simpa [finalCheck, hq] using hu.2.1
  have hrfinal : I.final.get r = true := safeRun_final I hA hqfinal hv
  have hSafeFull : ∀ i, i ≤ (u ++ v).length →
      safeCheck I (stateAt I (u ++ v) i) = true := by
    intro i hi
    by_cases hleft : i ≤ u.length
    · rw [stateAt_append_left I hleft]
      exact hu.1 i hleft
    · have hd : i - u.length ≤ v.length := by
        simp only [List.length_append] at hi
        omega
      rcases hv.2 (i - u.length) hd with ⟨s, hs, hss⟩
      have hidx : u.length + (i - u.length) = i := by omega
      rw [← hidx, stateAt_append_right I hrunU, hs]
      have hbad := (safeState_iff I s).mp hss |>.1
      simpa [safeCheck] using hbad
  have hFinalFull : finalCheck I (stateAt I (u ++ v) (u ++ v).length) = true := by
    have hend : stateAt I (u ++ v) (u ++ v).length = some r := by
      rw [show (u ++ v).length = u.length + v.length by simp,
        stateAt_append_right I hrunU]
      simpa using hv.1
    rw [hend]
    simpa [finalCheck] using hrfinal
  refine ⟨hSafeFull, hFinalFull, ?_⟩
  intro j hj i hij ha
  by_cases hjold : j ≤ u.length
  · have hiold : i ≤ u.length := Nat.le_trans hij hjold
    have haold := agrees_append_left hij hjold ha
    rw [stateAt_append_left I hjold, stateAt_append_left I hiold]
    exact hu.2.2 j hjold i hij haold
  · have hdpos : 0 < j - u.length := by omega
    have hdle : j - u.length ≤ v.length := by
      simp only [List.length_append] at hj
      omega
    rcases hv.2 (j - u.length) hdle with ⟨s, hs, hss⟩
    have hidx : u.length + (j - u.length) = j := by omega
    have htarget : stateAt I (u ++ v) j = some s := by
      rw [← hidx, stateAt_append_right I hrunU, hs]
    have hprefix : SafeRun I q (v.take (j - u.length)) s :=
      safeRun_prefix I hv hdle hs
    have hprefix_ne : v.take (j - u.length) ≠ [] := by
      apply List.ne_nil_of_length_pos
      simpa [List.length_take, Nat.min_eq_left hdle] using hdpos
    have hempty := safeRun_emptyIncoming I hA hqfinal hprefix hprefix_ne
    have hsource_safe := hSafeFull i (Nat.le_trans hij hj)
    cases hsrc : stateAt I (u ++ v) i with
    | none =>
      have : safeCheck I none = true := by simpa [hsrc] using hsource_safe
      simp [safeCheck] at this
    | some p =>
      rw [htarget]
      simp [unflaggedCheck, hempty p]

theorem terminalize_witness_of_safe_terminal (I : Instance k)
    (hA : Absorbing I) {u v : Word} {q r : Fin k}
    (hu : Witness I u) (hq : stateAt I u u.length = some q)
    (hv : SafeRun I q v r)
    (hterm : ∀ a : Bool, terminalStep I r a = none) :
    Witness (terminalize I) (u ++ v) := by
  have hw := witness_append_safeRun I hA hu hq hv
  have hsafe := witness_safeCut I hw
  have hstate := stateAt_original_to_terminalize_safeI I hsafe
  have hsafeR : safeState I r = true := by
    rcases hv.2 v.length (Nat.le_refl _) with ⟨s, hs, hss⟩
    have hs' : runFrom I q v = some s := by simpa using hs
    have hsr : s = r := Option.some.inj (hs'.symm.trans hv.1)
    simpa [hsr] using hss
  have hfinalR : I.final.get r = true := safeRun_final I hA
    (by simpa [finalCheck, hq] using hu.2.1) hv
  have hterminalFinal : terminalFinal I r = true := by
    simp [terminalFinal, hfinalR, hsafeR, hterm]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hstate i hi]
    rw [safeCheck_terminalize]
    exact hw.1 i hi
  · have hend : stateAt I (u ++ v) (u ++ v).length = some r := by
      rw [show (u ++ v).length = u.length + v.length by simp,
        stateAt_append_right I (by simpa [stateAt] using hq)]
      simpa using hv.1
    have hendT : stateAt (terminalize I) (u ++ v) (u ++ v).length = some r :=
      hstate (u ++ v).length (Nat.le_refl _) ▸ hend
    rw [hendT]
    simpa [finalCheck, terminalize, vector_get_ofFn] using hterminalFinal
  · intro j hj i hij ha
    have hil : i ≤ (u ++ v).length := Nat.le_trans hij hj
    rw [hstate j hj, hstate i hil]
    rw [unflaggedCheck_terminalize]
    exact hw.2.2 j hj i hij ha

theorem safeRun_segment_of_equal_cut (I : Instance k)
    {q s : Fin k} {v : Word} (hv : SafeRun I q v s)
    {i j : Nat} (hi : i ≤ j) (hj : j ≤ v.length)
    {p : Fin k} (hpi : runFrom I q (v.take i) = some p)
    (hpj : runFrom I q (v.take j) = some p) :
    SafeRun I p ((v.drop i).take (j - i)) p := by
  let c : Word := (v.drop i).take (j - i)
  have hlen : c.length = j - i := by
    dsimp [c]
    simp only [List.length_take, List.length_drop]
    omega
  have ht : v.take j = v.take i ++ c := by
    dsimp [c]
    rw [show j = i + (j - i) by omega, List.take_add]
    have hsub : i + (j - i) - i = j - i := by omega
    rw [hsub]
  have hcycle : runFrom I p c = some p := by
    rw [ht, runFrom_append, hpi] at hpj
    simpa using hpj
  refine ⟨hcycle, ?_⟩
  intro d hd
  have hd' : d ≤ j - i := by
    rw [← hlen]
    exact hd
  have htd : v.take (i + d) = v.take i ++ c.take d := by
    dsimp [c]
    rw [List.take_add]
    rw [List.take_take, Nat.min_eq_left hd']
  rcases hv.2 (i + d) (by omega) with ⟨t, htRun, htSafe⟩
  refine ⟨t, ?_, htSafe⟩
  rw [htd, runFrom_append, hpi] at htRun
  simpa using htRun

def cutStates (I : Instance k) (q : Fin k) (w : Word) : List (Fin k) :=
  (List.range (w.length + 1)).map
    (fun i => (runFrom I q (w.take i)).getD q)

def CutsDistinct (I : Instance k) (q : Fin k) (w : Word) : Prop :=
  ∀ i, i ≤ w.length → ∀ j, j ≤ w.length → i ≠ j →
    runFrom I q (w.take i) ≠ runFrom I q (w.take j)

theorem map_nodup_of_injective_on {α β : Type} (f : α → β) (l : List α)
    (hn : l.Nodup)
    (hi : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
      have hba := hi b (by simp [hb]) a (by simp) he
      exact ha (hba ▸ hb)
    · exact ih hl (fun x hx y hy h => hi x (by simp [hx]) y (by simp [hy]) h)

theorem safeRun_cutStates_nodup (I : Instance k) {q r : Fin k} {w : Word}
    (hw : SafeRun I q w r) (hd : CutsDistinct I q w) :
    (cutStates I q w).Nodup := by
  apply map_nodup_of_injective_on
    (fun i => (runFrom I q (w.take i)).getD q) _ List.nodup_range
  intro i hi j hj heq
  have hi' : i ≤ w.length := by simp only [List.mem_range] at hi; omega
  have hj' : j ≤ w.length := by simp only [List.mem_range] at hj; omega
  by_cases hne : i = j
  · exact hne
  · exfalso
    apply hd i hi' j hj' hne
    rcases hw.2 i hi' with ⟨p, hp, _⟩
    rcases hw.2 j hj' with ⟨s, hs, _⟩
    have heps : p = s := by simpa [hp, hs] using heq
    simpa [hp, hs] using congrArg some heps

theorem safeRun_distinct_length_le (I : Instance k) {q r : Fin k} {w : Word}
    (hw : SafeRun I q w r) (hd : CutsDistinct I q w) :
    w.length + 1 ≤ k := by
  have hn := safeRun_cutStates_nodup I hw hd
  have hm := hn.length_le_of_subset
    (l₂ := List.finRange k) (fun x _ => List.mem_finRange x)
  simpa [cutStates] using hm

theorem safeRun_repeat_cut (I : Instance k) {q r : Fin k} {w : Word}
    (hw : SafeRun I q w r) (hbig : k ≤ w.length) :
    ∃ i j p, i < j ∧ j ≤ w.length ∧
      runFrom I q (w.take i) = some p ∧
      runFrom I q (w.take j) = some p := by
  by_cases hrep : ∃ i j p, i < j ∧ j ≤ w.length ∧
      runFrom I q (w.take i) = some p ∧
      runFrom I q (w.take j) = some p
  · exact hrep
  · exfalso
    have hdist : CutsDistinct I q w := by
      intro i hi j hj hne
      by_cases hij : i < j
      · intro heq
        apply hrep
        rcases hw.2 i hi with ⟨p, hp, _⟩
        exact ⟨i, j, p, hij, hj, hp, heq ▸ hp⟩
      · have hji : j < i := by omega
        intro heq
        apply hrep
        rcases hw.2 j hj with ⟨p, hp, _⟩
        exact ⟨j, i, p, hji, hi, hp, heq.symm ▸ hp⟩
    have hbound := safeRun_distinct_length_le I
      (q := q) (w := w) hw hdist
    omega

theorem infWitness_of_repeat (I : Instance k) {u v : Word} {q r p : Fin k}
    (hu : Witness I u) (hq : stateAt I u u.length = some q)
    (hv : SafeRun I q v r) {i j : Nat}
    (hij : i < j) (hj : j ≤ v.length)
    (hpi : runFrom I q (v.take i) = some p)
    (hpj : runFrom I q (v.take j) = some p) :
    InfWitness I := by
  have hi : i ≤ j := Nat.le_of_lt hij
  have hstem : SafeRun I q (v.take i) p :=
    safeRun_prefix I hv (by omega) hpi
  have hcycle : SafeRun I p ((v.drop i).take (j - i)) p :=
    safeRun_segment_of_equal_cut I hv hi hj hpi hpj
  refine ⟨u, q, v.take i, p, (v.drop i).take (j - i), hu, hq, hstem,
    hcycle, ?_⟩
  intro hnil
  have hmin : j - i ≤ v.length - i := by omega
  have hpos : 0 < ((v.drop i).take (j - i)).length := by
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left hmin]
    omega
  exact (List.ne_nil_of_length_pos hpos) hnil

theorem finite_growth (I : Instance k) (hA : Absorbing I)
    {u : Word} {q : Fin k} (hu : Witness I u)
    (hq : stateAt I u u.length = some q) :
    ∀ n, InfWitness I ∨
      (∃ w, Witness (terminalize I) w) ∨
      (∃ v r, v.length = n ∧ SafeRun I q v r) := by
  have hqSafe : safeState I q = true := by
    rcases witness_safeCut I hu u.length (Nat.le_refl _) with ⟨s, hs, hss⟩
    have hs' : runFrom I I.initial u = some s := by
      simpa [stateAt] using hs
    have hq' : runFrom I I.initial u = some q := by
      simpa [stateAt] using hq
    have heq : s = q := Option.some.inj (hs'.symm.trans hq')
    simpa [heq] using hss
  intro n
  induction n with
  | zero =>
    right
    right
    refine ⟨[], q, by simp, ?_⟩
    refine ⟨by simp [runFrom], ?_⟩
    intro i hi
    have hi0 : i = 0 := by simp only [List.length_nil] at hi; omega
    subst i
    exact (safeCut_zero_iff I q []).2 hqSafe
  | succ n ih =>
    rcases ih with hInf | hRest
    · exact Or.inl hInf
    · rcases hRest with hTerm | hPath
      · exact Or.inr (Or.inl hTerm)
      · rcases hPath with ⟨v, r, hlen, hv⟩
        by_cases hterminal : ∀ a : Bool, terminalStep I r a = none
        · exact Or.inr (Or.inl
            ⟨u ++ v, terminalize_witness_of_safe_terminal I hA hu hq hv hterminal⟩)
        · rcases exists_terminalStep_of_not_terminal I hterminal with
            ⟨a, s, hstep⟩
          have hone : SafeRun I r [a] s :=
            safeRun_one_of_terminalStep I hstep
          have hnew : SafeRun I q (v ++ [a]) s :=
            safeRun_append I hv hone
          exact Or.inr (Or.inr
            ⟨v ++ [a], s, by simp [hlen], hnew⟩)

theorem c031 (I : Instance k) (hA : Absorbing I) :
    (∃ w, Witness I w) ↔
      InfWitness I ∨ ∃ w, Witness (terminalize I) w := by
  constructor
  · rintro ⟨u, hu⟩
    cases hq : stateAt I u u.length with
    | none =>
      have hf := hu.2.1
      simp [finalCheck, hq] at hf
    | some q =>
      have hg := finite_growth I hA hu hq (k + 1)
      rcases hg with hInf | hRest
      · exact Or.inl hInf
      · rcases hRest with hTerm | hPath
        · exact Or.inr hTerm
        · rcases hPath with ⟨v, r, hlen, hv⟩
          have hbig : k ≤ v.length := by omega
          rcases safeRun_repeat_cut I hv hbig with
            ⟨i, j, p, hij, hj, hpi, hpj⟩
          exact Or.inl (infWitness_of_repeat I hu hq hv hij hj hpi hpj)
  · rintro (hInf | hTerm)
    · rcases hInf with ⟨u, q, v, r, c, hu, _, _, _, _⟩
      exact ⟨u, hu⟩
    · rcases hTerm with ⟨w, hw⟩
      exact ⟨w, terminalize_witness_to_original I hw⟩

theorem terminalize_terminal (I : Instance k) :
    TerminalRank.TerminalFinals (terminalize I) := by
  intro f hf a
  have hf' : terminalFinal I f = true := by
    simpa [terminalize, vector_get_ofFn] using hf
  have hparts : I.final.get f = true ∧ safeState I f = true ∧
      (terminalStep I f false).isNone = true ∧
      (terminalStep I f true).isNone = true := by
    simpa [terminalFinal, Bool.and_eq_true, and_assoc] using hf'
  have hfalse : terminalStep I f false = none :=
    Option.isNone_iff_eq_none.mp hparts.2.2.1
  have htrue : terminalStep I f true = none :=
    Option.isNone_iff_eq_none.mp hparts.2.2.2
  cases a
  · simpa [terminalize, step, vector_get_ofFn] using hfalse
  · simpa [terminalize, step, vector_get_ofFn] using htrue

end AbsorbingTerminal
end Subtail
