# Six states with exact sufficient budget five

Owner: Astra. This is a finite computational counterexample for abstract
binary BorderAvoid, using the audited finite `Sandwich` construction. It
does not give an asymptotic lower bound or a subtype realization.

## The instance

Start at state 0. Undefined transitions are written `-`.

| State | 0 | 1 |
|---|---|---|
| 0 | 3 | - |
| 1 | 0 | 2 |
| 2 | 1 | 4 |
| 3 | 5 | 3 |
| 4 | 1 | 2 |
| 5 | 5 | 4 |

```text
Fin = {2,5}
Bad = empty
G = {(0,5), (3,4), (4,1), (5,4)}
```

The shortest witness is `001011010101`, length 12. It satisfies `S''(5,0)`.
The complete finite searches for all 15 budget pairs with `L+D<5` are empty.
The five pairs `(0,5)` through `(4,1)` are also empty; `(5,0)` succeeds.
Thus the computed exact minimum is `B=5`.

Since there are six states, this refutes the candidate extension

```text
B(I) <= max(0, |K|-2) for all abstract instances.
```

It does not contradict C016, whose bound has a regularity hypothesis. It also
does not refute `B<=|K|`, any larger linear bound, or a computable bound.
The lower-budget searches use the Python automaton; their correctness has
not yet been formalized in Lean.

## Proper borders account for four budget units

Fixing final state 5 excludes the initial state because `G(0,5)`, so that
boundary slice is empty. The slice for final state 2 has shortest word
`0011`, length four, and exact sufficient budget one. Consequently the union
of full boundary slices has `B=1`, while the flagged instance has `B=5`.

All empty/full-border restrictions are retained in this comparison. The
difference is therefore a proper-border effect. It improves on the earlier
E011 examples, whose apparent budget increases disappeared under full
boundary normalization.

## How the example was reduced

Targeted attempt 3 in E014 originally used eight states. Its budget-five
witness visits only old states `{0,2,3,4,5,7}`. Remove the other two states,
make transitions into them undefined, restrict the annotations, and relabel
the remaining states in increasing order.

Every surviving run maps back to the same run in the original instance.
Its endpoint, Bad status, and all flag checks are unchanged. Thus every
witness and every sufficient word of the restricted instance was already
one in the original. Removing states cannot decrease the minimum budget.
The retained word still satisfies `S''(5,0)`, so its budget cannot increase
above five. The independent finite search on the reduced instance confirms
the same value directly.

This also shows why future growth searches should remove irrelevant states
before comparing a budget with a state-count bound. Raw generator size can
hide a counterexample to the candidate bound.

## Reproduce

```sh
python3 experiments/trim_budget_example.py
```

[The result](../results/trimmed-budget.json) contains the full instance,
retained-state mapping, exact budget result, and both final-state slices.
Every one of the 8,191 binary words of length at most 12 is checked using
the forward and reversed predicates. This certifies the displayed shortest
length within a complete search through the returned witness length.

Each finite automaton search has a 200,000-state cap and reports UNKNOWN
if interrupted. This run completes all required searches; the successful
split explores 291 states. The word-length check is separate from the
all-length fixed-budget graph searches.
