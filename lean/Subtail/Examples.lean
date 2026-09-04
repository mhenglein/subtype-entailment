import Subtail.Truncation

namespace Subtail.Examples

def emptyOnly : Instance 1 where
  initial := 0
  transitions := #v[(none, none)]
  bad := #v[false]
  final := #v[true]
  flags := #v[#v[false]]

def badInitial : Instance 1 := { emptyOnly with bad := #v[true] }
def diagonalFlag : Instance 1 := { emptyOnly with flags := #v[#v[true]] }
def loop : Instance 1 := { emptyOnly with transitions := #v[(some 0, none)] }

def rigidFamily : Instance 2 where
  initial := 0
  transitions := #v[(some 1, none), (some 1, none)]
  bad := #v[false, false]
  final := #v[false, true]
  flags := #v[#v[false, false], #v[true, false]]

def visitedStrict : Instance 2 where
  initial := 0
  transitions := #v[(some 0, some 1), (some 1, none)]
  bad := #v[false, false]
  final := #v[true, true]
  flags := #v[#v[false, false], #v[true, false]]

example : Witness emptyOnly [] := (witnessCheck_correct _ _).mp (by decide)
example : witnessCheck emptyOnly [false] = false := by decide
example : witnessCheck badInitial [] = false := by decide
example : witnessCheck diagonalFlag [] = false := by decide
example : lrs [false, false, false] = 2 := by decide

/-- A strict cut is allowed to leave the empty word. -/
example : Witness loop [] := by
  have h := suffix_trace_truncation loop [false] (e := 0) (by decide)
    ((witnessCheck_correct _ _).mp (by decide)) (by decide) (by decide)
  exact h

/-- The shared-suffix rule shortens the memo-rigid family. -/
example : Witness rigidFamily [false] := by
  have h := suffix_trace_truncation rigidFamily [false, false, false] (e := 1)
    (by decide) ((witnessCheck_correct _ _).mp (by decide)) (by decide) (by decide)
  exact h

/-- The visited-state rule cuts 0010 to 00 despite a flag from an unvisited state. -/
example : Witness visitedStrict [false, false] := by
  apply visited_profile_truncation visitedStrict [false, false, true, false]
    (e := 2) (by decide) ((witnessCheck_correct _ _).mp (by decide))
    (by decide) (by decide)
  intro l hl i hi
  have hl' : l = 0 ∨ l = 1 := by change l ≤ 1 at hl; omega
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hl' with rfl | rfl <;> rcases hi' with rfl | rfl | rfl <;> decide

/-- The all-state profile condition fails on the same example. -/
example : ¬ IncomingLe visitedStrict (some 0) (some 1) := by
  intro h
  have hh := h (some 1) (by decide)
  change false = true at hh
  cases hh

end Subtail.Examples
