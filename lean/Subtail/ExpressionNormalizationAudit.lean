import Subtail.ExpressionNormalization

namespace Subtail.ExpressionNormalization
open TreeSemantics

theorem flat_pairs_length (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x,g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem definitions_length (R : Naming n) :
    R.definitions.length = 2 * R.pairs.length + R.botUsed.toNat := by
  cases hb : R.botUsed <;>
    simp [Naming.definitions, hb, flat_pairs_length, Nat.add_comm]

theorem normalized_length (G : Input n) (s t : Expr n) :
    (normalized G s t).length = G.length + 2 * (naming G s t).pairs.length +
      (naming G s t).botUsed.toNat := by
  simp only [normalized, List.length_append, List.length_map]
  rw [definitions_length]
  omega

theorem added_variables (G : Input n) (s t : Expr n) :
    (naming G s t).extra = (naming G s t).pairs.length + (naming G s t).botUsed.toNat := by
  simp [Naming.extra, Nat.add_comm]

theorem old_ne_slot (R : Naming n) (x : Fin n) (j : Fin R.pairs.length) :
    R.old x ≠ R.slot j := by
  intro h
  have he := congrArg Fin.val h
  have hx := x.isLt
  dsimp [Naming.old, Naming.slot] at he
  omega

theorem old_ne_bottom (R : Naming n) (x : Fin n) (hb : R.botUsed = true) :
    R.old x ≠ R.botIndex := by
  intro h
  have he := congrArg Fin.val h
  have hx := x.isLt
  simp [Naming.old, Naming.botIndex, hb] at he
  omega

/-- Every allocated slot, including unreferenced duplicate slots, is determined. -/
theorem extend_restrict (R : Naming n) (hc : R.Closed) (eta : Valuation R.total)
    (hm : Models R.definitions eta) : R.extend (R.restrict eta) = eta := by
  funext i
  by_cases ho : i.val < n
  · let x : Fin n := ⟨i.val,ho⟩
    have hi : R.old x = i := by apply Fin.ext; rfl
    rw [← hi, extend_old]
    rfl
  · by_cases hb : i.val < n + R.botUsed.toNat
    · have rb : R.botUsed = true := by
        cases he : R.botUsed
        · simp [he] at hb; omega
        · rfl
      have hi : i = R.botIndex := by
        apply Fin.ext
        simp only [Naming.botIndex, dif_pos rb]
        simp [rb] at hb
        omega
      rw [hi, extend_bottom R _ rb, models_bottom R eta hm rb]
    · let j : Fin R.pairs.length := ⟨i.val - (n + R.botUsed.toNat), by
        have := i.isLt
        dsimp [Naming.total, Naming.extra] at this
        omega⟩
      have hi : R.slot j = i := by
        apply Fin.ext
        dsimp [Naming.slot, j]
        omega
      rw [← hi, extend_slot, models_slot R eta hm]
      have hs := hc (R.pairs.get j) (List.get_mem _ _)
      rw [representative_correct R eta hm _ hs.1, representative_correct R eta hm _ hs.2]
      rfl

theorem unique_definition_extension (R : Naming n) (hc : R.Closed) (rho : Valuation n) :
    ∃! eta, Models R.definitions eta ∧ R.restrict eta = rho := by
  refine ⟨R.extend rho, ⟨extend_definitions R hc rho, restrict_extend R rho⟩, ?_⟩
  intro eta h
  have he := extend_restrict R hc eta h.1
  rw [h.2] at he
  exact he.symm

def infiniteInput : Input 1 := [(.prod (.var 0) .bot, .var 0)]

theorem infinite_input_model : ExprModels infiniteInput (fun _ => zeroSpine) := by
  intro c hc
  have he : c = (.prod (.var 0) .bot, .var 0) := by simpa [infiniteInput] using hc
  subst c
  exact zeroSpine_lower

theorem infinite_input_not_entails : ¬ ExprEntails infiniteInput (.var 0) .bot := by
  intro h
  exact h (fun _ => zeroSpine) infinite_input_model [] (by simp [eval, zeroSpine])

theorem normalized_infinite_input_not_entails :
    ¬ Entails (normalized infiniteInput (.var 0) .bot)
      ((naming infiniteInput (.var 0) .bot).ref (.var 0))
      ((naming infiniteInput (.var 0) .bot).ref .bot) := by
  intro h
  exact infinite_input_not_entails ((normalize_entails_iff _ _ _).mpr h)

theorem infinite_input_every_model_unbounded (rho : Valuation 1)
    (hm : ExprModels infiniteInput rho) (N : Nat) :
    ∃ w, (rho 0).nodes w ∧ N < w.length := by
  have step : Below (product (rho 0) bottom) (rho 0) := hm _ (by simp [infiniteInput])
  have all : ∀ j, (rho 0).nodes (List.replicate j false) := by
    intro j
    induction j with
    | zero => exact step [] trivial
    | succ j ih =>
      apply step
      simpa using ih
  exact ⟨List.replicate (N+1) false, all _, by simp⟩

def impossibleInput : Input 0 := [(.prod .bot .bot, .bot)]

theorem impossible_input_unsatisfiable : ¬ ∃ rho, ExprModels impossibleInput rho := by
  rintro ⟨rho, hm⟩
  exact hm _ (by simp [impossibleInput]) [] trivial

theorem normalized_impossible_unsatisfiable :
    ¬ Satisfiable (normalized impossibleInput .bot .bot) := by
  intro h
  exact impossible_input_unsatisfiable ((normalize_satisfiable_iff _ _ _).mpr h)

def nestedInput : Input 2 :=
  [(.prod (.prod (.var 0) .bot) (.prod (.var 0) .bot), .var 1)]

example : (naming nestedInput (.var 0) (.var 1)).extra = 4 := by decide
example : (normalized nestedInput (.var 0) (.var 1)).length = 8 := by decide
example : (naming ([] : Input 0) .bot .bot).total = 1 := by decide
example : (normalized ([] : Input 0) .bot .bot).length = 1 := by decide
example : (normalized ([] : Input 2) (.var 0) (.var 1)).length = 0 := by decide
example : (normalized ([] : Input 0) (.prod .bot .bot) .bot).length = 3 := by decide

/-- Native output for comparison with a separate Python syntax compiler. -/
structure Fixture where
  n : Nat
  premises : Input n
  left : Expr n
  right : Expr n

def smallExprs (n : Nat) : List (Expr n) :=
  let leaves := Expr.bot :: (List.finRange n).map Expr.var
  leaves ++ leaves.flatMap (fun l => leaves.map (fun r => Expr.prod l r))

def fixturesFor (n : Nat) : List Fixture :=
  (smallExprs n).flatMap fun s => (smallExprs n).flatMap fun t =>
    [⟨n, [], s, t⟩, ⟨n, [(s,t)], .bot, .bot⟩]

def fixtures : List Fixture :=
  fixturesFor 0 ++ fixturesFor 1 ++ fixturesFor 2 ++
  [⟨2, nestedInput, .var 0, .var 1⟩,
   ⟨1, infiniteInput, .var 0, .bot⟩,
   ⟨0, impossibleInput, .bot, .bot⟩,
   ⟨2, [(.bot,.var 0)], .var 1, .var 0⟩]

def clauseJson : Constraint n → String
  | .leq a b => s!"[\"L\",{a.val},{b.val}]"
  | .upper a l r => s!"[\"U\",{a.val},{l.val},{r.val}]"
  | .lower l r a => s!"[\"D\",{l.val},{r.val},{a.val}]"
  | .denial a => s!"[\"B\",{a.val}]"

def fixtureJson (f : Fixture) : String :=
  let R := naming f.premises f.left f.right
  let cs := String.intercalate "," ((normalized f.premises f.left f.right).map clauseJson)
  s!"{{\"n\":{f.n},\"total\":{R.total},\"left\":{(R.ref f.left).val},\"right\":{(R.ref f.right).val},\"clauses\":[{cs}]}}"

end Subtail.ExpressionNormalization

def main : IO Unit := do
  for f in Subtail.ExpressionNormalization.fixtures do
    IO.println (Subtail.ExpressionNormalization.fixtureJson f)
