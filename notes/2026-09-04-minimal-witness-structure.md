# Minimal-witness structure after context cuts

Date: 2026-09-04

This note studies a shortest witness `pi` for one fixed BorderAvoid instance.
It uses C008's suffix-trace cut and C013's context-restricted flag cut. The
purpose is to identify what a shortest witness must avoid. It does not claim
that longest repeated suffixes of shortest witnesses are bounded by the number
of states.

## Aligned repeated-context shortening

Let `pi` have length `n`, run through states `c(0), ..., c(n)`, and let
`v = pi[:e]` for `0 <= e < n`. Put `h = lrs(v)`. The C008 proof uses the
shared suffix of length `h`. The following form is sometimes easier to apply.

**Lemma (long aligned context).** Suppose there is an integer `H` such that

```text
h <= H <= e
suffix_H(v) = suffix_H(pi)
c(e-H) = c(n-H).
```

If `pi` is a witness, then `v` is a witness.

The case `H = 0` is allowed. It says that if `h = 0` and `c(e) = c(n)`,
then the prefix is a witness.

### Proof

The shared suffix of length `H` is read from equal states. Determinism therefore
gives

```text
c(e-lambda) = c(n-lambda)    for every 0 <= lambda <= H.
```

In particular, equality holds for every `lambda <= h`. The length-`h` suffixes
also agree. Thus the hypotheses of C008 hold, and `v` is a witness. Acceptance
of `v` follows directly from the equality at `H` and the fact that `pi` ends
in a final state. Definedness and avoidance of `Bad` are inherited because
`v` is a prefix of `pi`.

This proves a useful exclusion for shortest witnesses. If `pi` is a shortest
witness, then for every `e < n` and every `H` with `lrs(pi[:e]) <= H <= e`,

```text
suffix_H(pi[:e]) = suffix_H(pi)
    implies c(e-H) != c(n-H).
```

The repeated states must be aligned at the starts of matching suffix contexts.
A repeated state at arbitrary positions does not satisfy this implication.

## Exact obstruction for a shortest witness

The context-cut proof gives a more detailed necessary condition. For a prefix
`v = pi[:e]`, let `h = lrs(v)`. For `0 <= lambda <= h`, define

```text
U_lambda = v[e-lambda:e]
E_lambda = { i | 0 <= i < e-lambda and
                 v[i:i+lambda] = U_lambda }.
```

The empty-factor convention makes `E_0 = {0, ..., e-1}`. Assume `pi` is a
shortest witness. Then, for every `e < n`, at least one of the following holds:

1. `c(e)` is not final;
2. `suffix_h(v) != suffix_h(pi)`; or
3. there are `lambda <= h` and `i in E_lambda` such that

   ```text
   (c(i), c(e-lambda)) in G.
   ```

In the third case, the same source and suffix are safe at the original end:

```text
(c(i), c(n-lambda)) not in G.
```

Therefore every proper prefix with the shared-suffix and final-state
conditions has a **critical strict earlier occurrence**, possibly an
occurrence of the empty suffix, whose flag becomes dangerous only after
shortening.

### Proof

Assume that conditions 1 and 2 fail, but condition 3 also fails. Then
`c(e)` is final, the relevant suffixes agree, and for every `lambda <= h`,
incoming flags into `c(e-lambda)` from all exact earlier occurrences belong to
the incoming flags into `c(n-lambda)`. The exact-occurrence version of C013
then proves that `v` is a witness. This contradicts shortestness because
`e < n`. Hence condition 3 must hold.

For the final display, an index `i in E_lambda` means that the length-`lambda`
factor at `i` equals the suffix of `v`. The shared-suffix condition makes that
factor equal to the suffix of `pi` at `n-lambda`. The pair would therefore be a
forbidden pair in `pi` if `(c(i), c(n-lambda))` were in `G`, contradicting that
`pi` is a witness.

The boundary cases are explicit. If `e = 0`, then `E_0` is empty. Thus a
shortest nonempty witness cannot have an empty prefix with a final initial
state and a matching length-zero context; otherwise the empty word would be a
shorter witness. If `h = 0` and `e > 0`, the only possible critical length is
`lambda = 0`, which checks every earlier source position because the empty
suffix prefixes every suffix.

This obstruction is stronger than saying that a shortest word resists C009:
it identifies a source position carrying a strict earlier occurrence, possibly
of the empty suffix. It still does not bound the number or lengths of the
contexts `U_lambda`; those positions and contexts remain unbounded.

## Why arbitrary repeated states do not suffice

Consider the following three-state instance, with start state `0`:

```text
delta(0,0) = 1       delta(0,1) = 0
delta(1,0) = 2       delta(1,1) undefined
delta(2,0) undefined delta(2,1) = 2
Fin = {2}            Bad = empty
G = {(0,1)}.
```

The word `pi = 001` has run `(0,1,2,2)` and is a witness. It is shortest:

- the empty word is not final;
- words of length one do not end in state `2`;
- `00` reaches state `2` but has the flagged proper border pair
  `(i,j)=(0,1)`, since its suffix `0` is a prefix of `00` and
  `(c(0),c(1))=(0,1)`.

The run repeats state `2` at positions `2` and `3`. Deleting that repeated
loop gives `00`, which is accepted but is not a witness because the deletion
creates the flagged border above. For the potentially relevant prefix
`v = 00` at `e = 2`, `h = 1`, but

```text
suffix_1(v) = 0 != 1 = suffix_1(pi).
```

The aligned-context lemma therefore does not apply. This is the precise gap
in a pigeonhole argument based only on repeated DFA states: it does not control
the suffix word at the cut, nor the new borders created by deleting a loop.

## A precise missing condition for interior loop deletion

The same issue can be isolated for an interior deletion. Let `0 <= a < b <= n`,
let `d = b-a`, and set

```text
v = pi[:a] + pi[b:].
```

Assume `c(a) = c(b)`. The run of `v` is then defined, avoids `Bad`, and ends
in the same final state as `pi`. Map positions of `v` back to `pi` by

```text
f(i) = i       when i < a,
       i + d   when i >= a.
```

The state at position `i` in `v` equals `c(f(i))`. A sufficient border-lifting
hypothesis is:

```text
for every i < a and i <= j <= |v|,
if v[j:] is a prefix of v[i:],
then pi[f(j):] is a prefix of pi[f(i):].
```

Under this hypothesis, `v` is a witness. Pairs with `i >= a` lift directly;
pairs with `i < a` lift by the displayed hypothesis, and every flagged pair
would then contradict that `pi` is a witness. The hypothesis pinpoints the
remaining work: every border whose source suffix crosses the deletion join
must lift to a border before deletion. State equality alone proves only the
run and final-state parts.

For `pi = 001`, deleting positions `a = 2` and `b = 3` produces `v = 00`.
The new pair `(i,j)=(0,1)` does not lift: in `v`, `0` is a prefix of `00`,
whereas in `pi`, the suffix `01` at position `1` is not a prefix of `001` at
position `0`. The flag `G(0,1)` then makes the deletion fail.

This condition is deliberately stated as a border-transfer obligation rather
than a claimed theorem about all loops. It can guide future experiments: a
proposed finite summary must record enough join context to prove this lifting
property. Pigeonhole repetition of states does not provide that summary.

## Consequence for A008

For a shortest witness, inspect each proper prefix in this order:

1. Search for an aligned matching context and equal start states. The aligned
   lemma rules this out for a shortest witness.
2. If the suffix and final-state conditions hold, record a critical exact
   occurrence from the obstruction theorem.
3. Treat repeated states away from those aligned contexts as harmless until a
   border-lifting argument handles the deletion join.

This gives a precise obstruction when the acceptance and suffix hypotheses
hold, but no bound on how long critical contexts can persist. The note supports the
minimal-witness search without claiming a solution or a global computable
budget bound.
