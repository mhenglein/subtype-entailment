# A009 budget search

Date: 2026-09-04

Scope: abstract `BorderAvoid` instances only.  The generated automata are not
claimed to arise from the subtype entailment reduction.

## Question

Can flags force the least sufficient budget `B(I)` above the number of DFA
states, or at least make `B(I)` grow beyond the matching no-flag baseline?

Here `B(I)` is the first `L + D` for which the strong `Sandwich` search finds
a word satisfying `S''(L,D)`.  A reported `EXACT` budget has an exhausted `NO`
result for every split at every lower budget and a `YES` result at the
reported split.  A state-cap interruption is `UNKNOWN`; exhausting the tested
range without a witness is `NO_THROUGH`, not a global `NO` result.

## Reproduction

```text
python3 experiments/search_budgets.py \
  --instances 1200 \
  --max-budget 8 \
  --max-word-length 12 \
  --state-cap 50000
```

The run uses seed `2026090409`, random partial binary DFAs with 2–8 states,
sparse final, bad, and flag sets, plus fixed-word calibration instances for
`n in {1,2,3,5,8,12}`.  The result is
[`results/budget-search.json`](../results/budget-search.json).  The script
validates every returned `YES` word with both the forward `witness` predicate
and the independent reversed `border_witness` predicate.

## Result

The run checked 1,200 random instances and 21,043 flagged budget splits.
There were 741 exact flagged rows, 414 `NO_THROUGH` rows, and 45 `UNKNOWN`
rows.  The matching no-flag runs produced 978 exact rows, 194 `NO_THROUGH`
rows, and 28 `UNKNOWN` rows.

No random instance had an exact flagged budget greater than its state count.
No bounded lower-bound row had both a direct witness and an exhausted range
through a budget greater than its state count.  The largest exact flagged
budget among random rows was `B=1`.

Five random rows showed positive exact growth over their matching no-flag
baseline.  The largest observed growth was `+1`.  One complete example is:

```text
states: 7
delta: ((2, 0), (4, 0), (3, 2), (1, -1), (5, 6), (2, -1), (1, 6))
final: {3, 5, 6}
bad: {}
flags: {(4, 6), (5, 5), (6, 3)}
```

For this instance, the flagged search has an exact budget `B=1`, split
`(L,D)=(0,1)`, and witness `00`.  The lower split `(0,0)` is exhausted with
`NO`.  The same DFA with flags removed has exact budget `B=0`, with witness
`00001`.  Both witnesses pass the independent direct predicates.

The fixed-word calibration reproduces the known linear baseline:

| accepted word | states | exact budget |
|---|---:|---:|
| `0` | 2 | 0 |
| `00` | 3 | 1 |
| `000` | 4 | 2 |
| `00000` | 6 | 4 |
| `00000000` | 9 | 7 |
| `000000000000` | 13 | 11 |

The JSON keeps complete input descriptions for the top exact rows, all
positive-growth rows, resistant `NO_THROUGH` examples, and `UNKNOWN`
examples.  The latter are useful stress cases, but their capped searches must
not be interpreted as nonexistence.

## What this establishes

This is bounded evidence that flags can increase the sufficient budget on
small abstract instances.  It does not show superlinear growth, an unbounded
growth family, or a bound for subtype-derived instances.  It does not settle
decidability or undecidability of Problem 1.7.

The search also shows why a finite census needs explicit status handling:
dense flags often remove every short witness, while high-`L` searches can hit
the finite state cap.  A useful next search should bias toward automata whose
accepted words are all bordered, then mutate flags while preserving one known
long witness.  Any proposed `B>|K|` example should exhaust every lower split
and independently validate a witness before being recorded as exact.

## Stored-row replay and trivial-flag diagnostic

The five stored positive-growth rows were replayed without regenerating the
1,200-instance census:

```text
python3 experiments/search_budgets.py --replay-stored \
  --output results/budget-search.json
```

The replay rechecked each stored flagged and no-flag witness with the forward,
reversed, and `sufficient` predicates.  It also re-exhausted every lower split
through each stored exact budget.  All five rows passed, and the JSON records
`all_checks_passed: true` under `replay`.

For a separate diagnostic, `normalize_trivial_flags` adds every state with a
diagonal flag `(q,q)` to `bad`, removes final states `q` with an empty-suffix
flag `(q0,q)`, and drops the remaining flags.  This captures two effects that
every witness must avoid structurally; it is not asserted as a general
equivalence transformation for arbitrary callers.

Of the five `+1` rows, three retain residual growth after this normalization
and two do not.  The three surviving rows have normalized exact budget `0`
against flagged exact budget `1`; the other two have normalized exact budget
`1`.  This separates residual flag interaction from growth explainable by
trivial diagonal or empty-border pruning.  The diagnostic remains abstract
and bounded, so it provides no SEP result.
