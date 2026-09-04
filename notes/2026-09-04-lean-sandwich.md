# Lean sandwich predicates

Date: 2026-09-04

`lean/Subtail/SandwichPredicates.lean` formalizes the finite necessary and
sufficient predicates from memo Definition 8.6 for an arbitrary finite
annotated binary instance.

## Interfaces proved

- `Admissible I w` contains the defined-run safety checks and final-state check.
- `Necessary I w L D` checks every agreeing pair whose border length
  `w.length - j` is at most `L` or whose period `j - i` is at most `D`.
- `SuffixBound w L D` says that every occurrence of the final suffix of length
  `L + 1` starts within `D` positions of its last possible start. The case
  `w.length ≤ L` is vacuous.
- `Sufficient I w L D` is `Necessary I w L D ∧ SuffixBound w L D`.

The main semantic theorems are:

```text
witness_implies_necessary
sufficient_implies_witness
witness_implies_sufficient_lrs
```

The last theorem proves the individual coverage fact
`Witness I w → Sufficient I w (lrs w) 0`. It does not bound `lrs` by the
instance size.

## Reversal correspondence

`ReverseSuffixBound` uses the Python formulation directly. It forbids an
occurrence of `reverse w`'s prefix of length `L + 1` at any start `s` with
`D < s` and `s + (L + 1) ≤ w.length`.

The theorem
`suffixBound_iff_reverseSuffixBound` proves equivalence with the forward
formulation. The supporting theorem `reverse_occurrence_iff` maps an original
suffix occurrence at `t` to reverse start
`w.length - (L + 1) - t`.

## Executable checks

The file defines `admissibleCheck`, `necessaryCheck`, `suffixBoundCheck`, and
`sufficientCheck`. Their correctness theorems show Boolean equality with the
corresponding propositions. These are finite computations relative to the
given instance, word, `L`, and `D`; they do not construct the finite-state
O4 automaton.

## Axiom audit

Run the shared audit from `lean/`:

```sh
lake build
lake env lean Subtail/Audit.lean
```

The relevant output is:

```text
'Subtail.sufficient_implies_witness' depends on axioms: [propext, Quot.sound]
'Subtail.witness_implies_sufficient_lrs' depends on axioms: [propext, Quot.sound]
'Subtail.necessaryCheck_correct' depends on axioms: [propext, Quot.sound]
'Subtail.suffixBoundCheck_correct' depends on axioms: [propext, Quot.sound]
'Subtail.sufficientCheck_correct' depends on axioms: [propext, Quot.sound]
```

The reversal lemmas inherit `Classical.choice` through Lean's library theorem
`List.drop_take`; this is used only in erased proof terms. The executable
definitions use finite list operations and the computable natural-number
decider. No `sorryAx`, custom axiom, or classical runtime oracle is used.

## Remaining gaps

O4 still requires the finite-state construction for `S''(L,D)`, a proof that
its graph search is exact, and a complete nonemptiness procedure. The global
computable bound on `L + D` remains open. The file also does not prove the
reduction from subtype constraints to these arbitrary annotated instances.
