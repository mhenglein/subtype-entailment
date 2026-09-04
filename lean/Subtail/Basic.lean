import Std

/-!
Finite data and the direct witness condition of memo Definition 8.1.
The alphabet is binary. Types and possibly infinite trees are not yet formalized.
-/

namespace Subtail

abbrev Word := List Bool

/-- A finite input. Invalid transitions are represented by `none`. -/
structure Instance (k : Nat) where
  initial : Fin k
  transitions : Vector (Option (Fin k) × Option (Fin k)) k
  bad : Vector Bool k
  final : Vector Bool k
  flags : Vector (Vector Bool k) k
  deriving Repr

def step (I : Instance k) (q : Fin k) (a : Bool) : Option (Fin k) :=
  if a then (I.transitions.get q).2 else (I.transitions.get q).1

def runFrom (I : Instance k) (q : Fin k) : Word → Option (Fin k)
  | [] => some q
  | a :: w => (step I q a).bind (fun r => runFrom I r w)

def stateAt (I : Instance k) (w : Word) (i : Nat) : Option (Fin k) :=
  runFrom I I.initial (w.take i)

def safeCheck (I : Instance k) : Option (Fin k) → Bool
  | none => false
  | some q => !(I.bad.get q)

def finalCheck (I : Instance k) : Option (Fin k) → Bool
  | none => false
  | some q => I.final.get q

def unflaggedCheck (I : Instance k) : Option (Fin k) → Option (Fin k) → Bool
  | some q, some r => !((I.flags.get q).get r)
  | _, _ => false

/-- Suffix `j` is a prefix of suffix `i`, including empty and full suffixes. -/
def Agrees (w : Word) (i j : Nat) : Prop :=
  (w.drop j).IsPrefix (w.drop i)

/-- Exact direct predicate, with the start position included in every check. -/
def Witness (I : Instance k) (w : Word) : Prop :=
  (∀ i, i ≤ w.length → safeCheck I (stateAt I w i) = true) ∧
  finalCheck I (stateAt I w w.length) = true ∧
  ∀ j, j ≤ w.length → ∀ i, i ≤ j → Agrees w i j →
    unflaggedCheck I (stateAt I w i) (stateAt I w j) = true

/-- Executable finite enumeration; it does not use classical decidability. -/
def witnessCheck (I : Instance k) (w : Word) : Bool :=
  (List.range (w.length + 1)).all (fun i => safeCheck I (stateAt I w i)) &&
  finalCheck I (stateAt I w w.length) &&
  (List.range (w.length + 1)).all (fun j =>
    (List.range (j + 1)).all (fun i =>
      if (w.drop j).isPrefixOf (w.drop i) then
        unflaggedCheck I (stateAt I w i) (stateAt I w j)
      else true))

theorem witnessCheck_correct (I : Instance k) (w : Word) :
    witnessCheck I w = true ↔ Witness I w := by
  simp [witnessCheck, Witness, Agrees, List.all_eq_true, List.mem_range,
    Nat.lt_succ_iff, List.isPrefixOf_iff_prefix, and_assoc]
  intro _ _
  constructor
  · intro h j hj i hi ha
    rcases h j hj i hi with hn | hu
    · exact False.elim (hn ha)
    · exact hu
  · intro h j hj i hi
    by_cases ha : (w.drop j).IsPrefix (w.drop i)
    · exact Or.inr (h j hj i hi ha)
    · exact Or.inl ha

theorem stateAt_take (I : Instance k) (w : Word) {e i : Nat} (hi : i ≤ e) :
    stateAt I (w.take e) i = stateAt I w i := by
  simp [stateAt, List.take_take, Nat.min_eq_left hi]

theorem runFrom_append (I : Instance k) (q : Fin k) (u v : Word) :
    runFrom I q (u ++ v) = (runFrom I q u).bind (fun r => runFrom I r v) := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    simp only [List.cons_append, runFrom]
    cases h : step I q a with
    | none => rfl
    | some r => simpa using ih r

theorem stateAt_add (I : Instance k) (w : Word) (i d : Nat) :
    stateAt I w (i + d) =
      (stateAt I w i).bind (fun q => runFrom I q ((w.drop i).take d)) := by
  simp only [stateAt, List.take_add, runFrom_append]

end Subtail
