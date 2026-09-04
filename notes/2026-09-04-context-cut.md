# Occurrence-context truncation cuts

Date: 2026-09-04

This note records an A015 attempt to weaken C009's incoming-flag inclusion.
The goal is to transfer a witness `pi` to a proper prefix `v`, while comparing
only flag sources that can occur in the retained prefix or can actually be an
earlier occurrence of the suffix under consideration.

The result is a proved family of sufficient cuts. It does not give a bound on
the minimum witness budget and does not solve Problem 1.7.

## Setup

Let `pi` be a witness of length `n`, with defined DFA run

```text
c(0), c(1), ..., c(n).
```

Choose `0 <= e < n`, let `v = pi[:e]`, and let `h = lrs(v)`. Here `lrs(v)` is
the largest positive `lambda < |v|` for which the suffix of `v` of length
`lambda` occurs at a position ending before the end of `v`; use `h = 0` when
there is no such positive length. For `0 <= lambda <= h`, write

```text
U_lambda = v[e-lambda:e]
R_lambda = c(e-lambda)
T_lambda = c(n-lambda).
```

The hypothesis

```text
suffix_h(v) = suffix_h(pi)
```

is automatic when `h = 0`. It implies the corresponding equality of suffixes
for every `lambda <= h`.

For each such `lambda`, define the positions of strict earlier occurrences:

```text
E_lambda = { i | 0 <= i < e-lambda and
                 v[i:i+lambda] = U_lambda }.
```

For `lambda = 0`, the factor equality is vacuous, so `E_0` contains all
positions `0 <= i < e`. Define the associated state sets

```text
O_lambda = { c(i) | i in E_lambda }                 exact occurrences
Q_lambda = { c(i) | 0 <= i < e-lambda }             earlier context
V_e      = { c(i) | 0 <= i <= e }                   all retained states.
```

They satisfy `O_lambda subseteq Q_lambda subseteq V_e`. For an endpoint state
`q`, let `Pred_G(q) = { r | (r,q) in G }`.

## The localized lemma

Assume:

1. `pi` is a witness.
2. `0 <= e < n`, `v = pi[:e]`, and `h = lrs(v)`.
3. `suffix_h(v) = suffix_h(pi)`.
4. `c(e)` is in `Fin`.
5. For every `0 <= lambda <= h`,

   ```text
   Pred_G(R_lambda) intersect O_lambda
       subseteq Pred_G(T_lambda).
   ```

Then `v` is a witness.

The same conclusion holds if `O_lambda` in condition 5 is replaced by
`Q_lambda`, or by `V_e`. The `V_e` version is a strict relaxation of C009:
C009 compares `Pred_G(R_lambda)` and `Pred_G(T_lambda)` over every state in
`K`, while this version compares them only over states visited by `v`.
The `Q_lambda` version removes retained states after the start of the relevant
suffix. The `O_lambda` version keeps only states at exact earlier occurrences
of that suffix.

### Proof

Because `v` is a prefix of `pi`, its run is defined and avoids `Bad`. Condition
4 gives the required final-state check.

Consider a possible flagged pair in `v`, with positions `i <= j`. If `i = j`,
the pair is diagonal. The original witness has no diagonal flag at any state
visited by `pi`, so this case is impossible.

Suppose `i < j` and set `lambda = e-j`. The suffix of `v` beginning at `j` has
length `lambda`. Since it is a prefix of the suffix beginning at `i`,

```text
v[i:i+lambda] = v[j:e] = U_lambda.
```

If `lambda > h`, this is a positive repeated suffix longer than `lrs(v)`,
which is impossible. The case `lambda = 0` is allowed and is covered by
`E_0`.

For `lambda <= h`, condition 3 gives
`U_lambda = pi[n-lambda:n]`. Thus the suffix of `pi` at `n-lambda` is a
prefix of the suffix at `i`. Since `pi` is a witness,

```text
(c(i), T_lambda) is not in G.
```

The position `i` belongs to `E_lambda`, so `c(i)` belongs to `O_lambda` and
also to each larger source context used above. Condition 5 says that a flag
from `c(i)` to `R_lambda` would transfer to a flag from `c(i)` to
`T_lambda`, contradicting the preceding display. Therefore no flagged pair
exists in `v`, and `v` is a witness.

This proof also handles the boundary cases.

- If `h = 0` and `e > 0`, only `lambda = 0` is checked. Every nonempty suffix
  of `v` has no earlier occurrence, and condition 5 transfers the empty-suffix
  obligations from `c(n)` to `c(e)`.
- If `e = 0`, then `v` is empty, `h = 0`, and `O_0` and `Q_0` are empty.
  The localized flag condition is vacuous. Condition 4 makes the initial state
  final, and the original diagonal check rules out the only possible flag, so
  the empty word is a witness.
- If `e > 0` and `lambda = 0`, `E_0` includes every earlier position. This is
  necessary because the empty suffix is a prefix of every suffix.

## Why the exact-occurrence version is useful, and its limit

The exact set `O_lambda` is the narrowest of the four contexts considered
here. We do not claim it is minimal: some obligations can also be discharged
from diagonal checks or other properties of the instance. The condition is
close to a direct check of `v`: under the assumptions that `pi` is a
witness and the suffixes agree, every state in `O_lambda` is already known to
have no flag to `T_lambda`. Consequently,

```text
Pred_G(R_lambda) intersect O_lambda
    subseteq Pred_G(T_lambda)
```

reduces to checking that no exact earlier occurrence has a flag to the new
endpoint. This is a localized decomposition of the witness condition, not a
pumping theorem. The visited-state and `Q_lambda` versions retain more useful
finite summaries while remaining strictly sufficient by the same proof.

The implication chain, with the common suffix and final-state conditions
understood, is

```text
C009 all states  =>  V_e  =>  Q_lambda  =>  O_lambda.
```

The last criterion is the weakest of these four sufficient conditions. The
visited-state criterion is a simpler candidate for a finite state summary.

## Small strict examples

The executable search in [check_context_cuts.py](../experiments/check_context_cuts.py)
enumerates every two-state binary partial DFA, every `Bad` and `Fin` set, and
every flag relation. It finds the first strict examples with a nonempty
retained prefix and `h >= 1` at word length four.

### States visited by the retained prefix

```text
delta(0,0) = 0       delta(0,1) = 1
delta(1,0) = 1       delta(1,1) undefined
Fin = {0,1}          Bad = empty
G = {(1,0)}          start = 0
```

Take `pi = 0010`, whose run is `(0,0,0,1,1)`. With `e = 2`,
`v = 00` and `h = 1`. The shortened word is a witness. C009 fails because
state `1` is in `Pred_G(0)` but not in `Pred_G(1)`, even though state `1` is
not visited by `v`; the visited-state, `Q_lambda`, and exact-occurrence rules
all succeed.

### Exact earlier occurrences

```text
delta(0,0) undefined  delta(0,1) = 1
delta(1,0) = 0        delta(1,1) = 1
Fin = {1}             Bad = empty
G = {(1,0)}           start = 0
```

Take `pi = 1011`, whose run is `(0,1,0,1,1)`. With `e = 3`,
`v = 101` and `h = 1`. For `lambda = 1`, the new target is state `0` and
the old target is state `1`. C009, the visited-state rule, and the `Q_lambda`
rule all see the offending state `1` in `Pred_G(0)`. The exact earlier
occurrences of the suffix `1` have only position `0`, whose state is `0`, so
the exact-occurrence rule succeeds. The shortened word is a witness.

The search also records an empty-prefix strict example: a one-letter word can
have a final empty prefix while an unvisited state makes C009 fail. This is
why `e = 0` should be handled explicitly rather than silently excluded.

## Bounded independent regression

Run:

```text
python3 experiments/check_context_cuts.py
```

The script uses an independent run and witness predicate, then compares that
predicate with the reversed-border checker `border_lab.border_witness` as a
second oracle. It checks:

| Scope | Result |
|---|---:|
| Two-state instances | 20,736 |
| Words per instance, lengths 0 through 6 | 127 |
| Independent/reference witness comparisons | 2,633,472 |
| Applicable C009 cuts | 179,760 |
| Applicable visited-state cuts | 181,230 |
| Applicable `Q_lambda` cuts | 181,230 |
| Applicable exact-occurrence cuts | 181,306 |
| Larger random instances | 120, state counts 2 through 5 |
| Random words per instance, lengths 0 through 8 | 511 |
| Failed implication checks | 0 |

The random run had 61,320 words and no failed implication checks. The complete
JSON output is [context-cuts.json](../results/context-cuts.json). The search
is bounded evidence only. It does not establish a global witness bound, a
decision procedure, or any result for arbitrary BorderAvoid instances beyond
the stated lemma.

## Next mathematical use

Use the visited-state rule as a non-tautological cut in minimal-witness
searches. Use the exact-occurrence rule as a diagnostic: when it succeeds but
the visited-state rule fails, record which unrelated retained state caused the
failure. A future pumping lemma would need to control those context states or
prove that their flags can be ignored. The present result supplies that
failure classification but no bound on how long such contexts can remain
relevant.
