# Separate boundary flags from proper borders

Owner: Astra. Written proofs below; binary local decomposition also checked in
Lean. The unrestricted subtype entailment problem remains open.

## Exact decomposition

Let `I=(K,delta,q0,Fin,Bad,G)` be a finite annotated partial DFA. For a word
`w` of length `n`, write `c(i)` for its state after `i` letters. A witness
requires a defined safe run, an accepting endpoint, and absence of
`G(c(i),c(j))` whenever `0<=i<=j<=n` and `w[j:]` is a prefix of `w[i:]`.

Two kinds of agreement hold without inspecting letters:

- `i=j`: the full suffix is a prefix of itself. Every visited state must
  avoid a diagonal flag.
- `j=n`: the empty suffix is a prefix of every suffix. Every visited state
  must avoid a flag into the final state.

For each `f in Fin`, define

```text
D_f = Bad union {q : G(q,q)} union {q : G(q,f)}.
L_f = {w : its run avoids D_f and ends at f}.
```

Then `N''(0,0) = union_f L_f`. Indeed, the zero-budget necessary predicate
checks exactly `n-j=0` or `j-i=0`, which are the two cases above. Each `L_f`
is regular and uses the original DFA with forbidden states and one final
state. No occurrence history is needed for these constraints.

The full witness language is precisely the words in this union that also
avoid all flagged agreements with `i<j<n`. Those remaining agreements have
a nonempty suffix and a strict earlier occurrence. We call these the proper
border obligations.

[Boundary.lean](../lean/Subtail/Boundary.lean) proves the binary statements
`witness_iff_boundary_proper`, `boundary_iff_finalSlice`, and
`witness_iff_finalSlice_proper`. It also proves an executable checker correct
and proves that a boundary-safe word of length at most one is a witness.
The general graph arguments below are written proofs, separate from that file.

## Exact decision for at most two states

If a witness exists, some `L_f` is nonempty. Take a shortest path from `q0`
to `f` avoiding `D_f`. It has no repeated state: deleting a loop preserves
the path and boundary safety. Its word has length at most `|K|-1`.

For `|K|<=2`, this length is at most one. Such a word has no indices
`i<j<n`, hence no proper border obligation. It is a witness. Conversely,
every witness belongs to a boundary slice. Thus the following algorithm is
complete for at most two states:

1. Construct the final-state slices.
2. Search their finite graphs for an accepting path.
3. Return a shortest such word, or NO if every graph is empty.

Equivalently, on the binary alphabet, check only the three words `epsilon`,
`0`, and `1`. Every nonempty instance in this class has exact budget `B=0`.
The executable checker and its exact existence theorem are also proved in
[TwoState.lean](../lean/Subtail/TwoState.lean), under the explicit `k<=2`
hypothesis. The one-letter witness need not be a prefix of the original word.
This is a statement about the number of abstract automaton states; two subtype
variables need not generate a two-state summary automaton.

## A decidable regular subclass

For a slice `f`, let `R_f` contain states both reachable from `q0` and able to
reach `f` in the graph avoiding `D_f`. Define

```text
H_f = {(q,r) in G : q,r in R_f and r is reachable from q in that graph}.
```

If every `H_f` is empty, then no accepting boundary-safe run can visit a
flagged pair in forward order. In particular, it cannot violate any proper
border obligation. Its witness language equals `union_f L_f`, so ordinary
finite graph search decides nonemptiness and returns a globally shortest
witness.

Failure of this test is UNKNOWN. A reachable flagged pair may never coincide
with a suffix agreement; nonempty `H_f` is not a certificate of nonexistence.

For a nonempty instance certified by this test, a shortest witness has length
at most `|K|-1`. A nonempty word of length `n` has `lrs<=n-1`; the empty word
has `lrs=0`. Since any witness satisfies `S''(lrs,0)`,

```text
B(I) <= max(0, |K|-2).
```

The singleton language `0^n` with `n+1` states and no flags attains this bound
for every `n>=1`. This upper bound concerns the certified subclass only.
It suggests a sharper experimental target than `B>|K|`: first seek
`B>max(0,|K|-2)` outside this subclass.

## Corrected baselines for the earlier search

The earlier E011 replay removed diagonal flags and flags from `q0` into the
endpoint. That is a valid relaxation, but it leaves empty-suffix flags from
other visited states. Three reported `+1` increases survived that partial
normalization. They were not yet evidence of proper-border budget growth.

For all five original `+1` rows, the complete final-state slices have exact
minimum budget one, equal to the flagged instance's budget. None of the five
increases survives full boundary normalization. The stored flags can still
exclude additional words; equal minimum budgets do not imply equal languages.
This is a correction to the experimental interpretation, not a refutation of
the original numerical results.

## Reproduction and limits

```sh
python3 experiments/check_boundary_slices.py
```

[Results](../results/boundary-slices.json) record:

- All 20,736 binary two-state partial instances, with start state zero:
  81 transition tables, four final sets, four Bad sets, and 16 flag sets.
  Relabeling covers the other start-state choice.
- All words of lengths zero through four in that census, plus 100 seeded
  instances with all words through length seven: 668,316 word comparisons.
- 2,682 nonempty two-state instances: 2,592 have shortest word `epsilon`,
  and 90 have shortest length one. The other 18,054 are exactly empty.
- Across both input sets, the regularity test returns 2,627 YES, 18,105 NO,
  and 104 UNKNOWN. Some two-state instances are decided by the separate
  two-state argument even though this stronger language-equality test fails.
- Exact finite-budget replay of all five previous growth rows, comparing
  with the union of their full boundary slices.

These finite comparisons check the implementations against the direct
necessary and witness predicates. The all-input conclusions above come from
the written arguments and the stated Lean proofs. They provide neither a
global budget bound nor a decision procedure for Problem 1.7. Literature
novelty has not been established.

Python inputs must have well-formed transition tables, valid state indices,
and an alphabet with unique symbols and one transition column per symbol.
