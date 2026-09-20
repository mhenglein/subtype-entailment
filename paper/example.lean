import Subtail.EntailmentFast
import Subtail.FiniteTreeDecision

open Subtail.ExpressionNormalization Subtail.EntailmentFast

/-- A small input to the checked Boolean. The reverse query has a root countermodel. -/
def main : IO Unit := do
  let x : Expr 2 := .var 0
  let y : Expr 2 := .var 1
  IO.println s!"With premise x <= y, query x <= y: {entailsCheck [(x, y)] x y}"
  IO.println s!"With premise x <= y, query y <= x: {entailsCheck [(x, y)] y x}"
  let spine : Input 2 := [(.prod x .bot, x)]
  IO.println s!"With premise x * bottom <= x, query x <= bottom (arbitrary): {entailsCheck spine x .bot}"
  IO.println s!"With premise x * bottom <= x, query x <= bottom (finite): {Subtail.FiniteTreeDecision.entailsCheck spine x .bot}"
