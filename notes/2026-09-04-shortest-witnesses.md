# A008 shortest witnesses

Date: 2026-09-04

This note records a bounded search over the abstract `BorderAvoid` model. It
does not establish a bound for subtype entailment or for Problem 1.7.

## Reproduction

Run from the repository root:

```text
python3 experiments/shortest_witnesses.py \
  --output results/shortest-witnesses.json
```

The saved run uses:

| setting | value |
|---|---:|
| transition instances | `3^4` |
| final subsets | `4` |
| bad subsets | `4` |
| flag relations | `16` |
| total two-state instances | `20,736` |
| requested word cap | `12` |
| direct scan cap for two-state rows | `1` |
| `N''(0,0)` state cap | `200,000` |
| targeted seed | `8008` |
| targeted attempts | `120` |
| targeted flag steps | `16` |
| targeted state range | `3`--`8` |
| targeted word cap | `12` |

The direct and reversed predicates were compared on every scanned word. Every
strong-search `YES` was also checked with `sufficient(I,w,L,D)`. The run took
about 25 seconds on the local machine.

## Exact two-state result

The census found:

| result | count |
|---|---:|
| shortest witness found | `2,682` |
| shortest length `0` | `2,592` |
| shortest length `1` | `90` |
| no witness through the requested cap | `18,054` |
| forward/reverse disagreements | `0` |
| applicable C008 cuts | `0` |
| applicable C009 cuts | `0` |
| applicable C013 cuts | `0` |

All `2,682` witnesses have longest repeated suffix `0` and per-word budget
`0`. The other `18,054` rows were decided by an exact `N''(0,0)` graph
search that completed without reaching its cap. Its statuses were `18,054`
`NO`, `0` `UNKNOWN`, and `0`
fallback searches. The graph-state histogram was `0:15,876`, `1:968`,
`3:968`, and `7:242`.

The finite argument behind this shortcut is:

1. Fix a final state and remove states forbidden by diagonal flags `(q,q)`
   and empty-suffix flags `(q,f)`. Drop the remaining flags. This is the
   boundary-only slice represented by `N''(0,0)`.
2. With at most two original states, a nonempty slice has a shortest simple
   accepting DFA path of at most one edge. A path of length zero or one has
   no proper nonempty suffix agreement.
3. Its only possible suffix agreements are the empty and full boundary cases,
   which `N''(0,0)` checks. Therefore a nonempty `N''(0,0)` slice yields a
   witness, and every witness yields a nonempty necessary graph.

The script checks the resulting equivalence across all `20,736` encodings.
The binary two-state statement also has a checked theorem in
[TwoState.lean](../lean/Subtail/TwoState.lean). It is not a theorem about
arbitrary subtype instances.

## Targeted 3--8 state search

The targeted generator first samples a partial binary DFA with `3`--`8`
states. It lists admissible base words through length `12`, then adds a flag
that blocks the current shortest word while preserving a longer base word.
It repeats for at most `16` steps and keeps the best retained input. The
targeted stage had `85` attempts with at least one base candidate and retained
six complete rows.

All six retained rows had an exact strong budget. Their exact budget growth
over the normalized full-boundary slice was:

| selected word | states | exact `B` | normalized minimum `B` | growth | length growth |
|---|---:|---:|---:|---:|---:|
| `001011010101` | 8 | 5 | 1 | `+4` | `+8` |
| `101110011111` | 8 | 4 | 2 | `+2` | `+8` |
| `101001100` | 8 | 3 | 1 | `+2` | `+5` |
| `01100111` | 8 | 2 | 1 | `+1` | `+5` |
| `001000` | 7 | 2 | 1 | `+1` | `+2` |
| `110010` | 7 | 2 | 1 | `+1` | `+1` |

The first row is the strongest retained raw input:

```text
delta = ((4,6), (1,4), (0,3), (2,5), (7,4), (2,3), (6,6), (7,5))
final = {3,6,7}
bad = {}
flags = {(0,6), (0,7), (4,5), (5,2), (7,5)}
word = 001011010101
trace = (0,4,7,5,2,3,5,2,3,2,3,2,3)
visited states = {0,2,3,4,5,7}
```

The raw eight-state row has exact budget `5`; its selected witness visits only
six states. An independent visited-state trim can therefore test the sharper
comparison `B=5` against the six-state boundary benchmark `4`. That trim is a
separate follow-up. It is now completed and independently checked in
[E015](../experiments/README.md#e015): the six-state result still has `B=5`.

The first row's flags block shorter base words through proper borders. One
boundary-safe example is `0011`, blocked by flag pair `(7,5)` on a proper
border without an active empty/full-border flag. The selected word itself has
no active proper flag, which is expected: the construction preserves it while
removing shorter candidates.

The targeted run found no row with exact budget greater than
`max(0, |K|-2)` for the raw declared state count. It did find proper-border
effects that raise the shortest witness length and the exact budget relative
to the normalized boundary-only slice. These are abstract examples only.

## Limits and next experiment

The two-state result depends on the finite two-state path argument. It does
not apply to three or more states. The targeted search is a deterministic,
seeded heuristic, so failure to find a larger excess is not a lower-bound
result. Every bounded `UNKNOWN` remains `UNKNOWN`; the JSON keeps complete
inputs for the retained rows and selected no-witness rows.

After the successful six-state trim, the next step is to search structured
three- to six-state automata and try to generalize the obstruction. Compare
budgets with state counts only after trimming, and seek a family or a larger
bound whose proof handles the proper-border restrictions.
