# Five-state all-length NO certificate

Date: 2026-09-08. Workstream: A012, prompted by issue #15. Base main: `99133037a60f65c8e0fab5ed9299524fbd95043e`.

**Status:** written all-length proof plus an independent direct-predicate regression. Not Lean-checked and not independently mathematically reviewed. This solves the first concrete certificate target from issue #15, not A012's general completeness problem and not unrestricted Problem 1.7.

## Target instance

Use start state 0, sole final state 4, no Bad states, and

```text
G = {(0,2), (0,3), (1,2)}.
```

The partial binary transition table is

| state | 0 | 1 |
|---|---:|---:|
| 0 | 2 | 1 |
| 1 | 2 | 1 |
| 2 | undefined | 3 |
| 3 | 4 | 3 |
| 4 | undefined | undefined |

This is the five-state obstruction first recorded on PR #9. Every accepted word has the unique form

```text
w(n,m) = 1^n 0 1^m 0,   n >= 0, m >= 1.
```

The point of this note is to turn the earlier informal three-case exclusion into an explicit certificate schema: from the two parameters `n,m`, compute one concrete flagged pair of cuts whose suffixes agree.

## Certificate schema

For a word `w(n,m)`, let `c(t)` be the DFA state after `t` input letters. The certificate is one of the following three records.

### Case 1: n < m

Take

```text
i = 0,
j = m + 1.
```

The cut `j` lies in the second 1-block exactly `n` ones before the final zero. Hence

```text
w[j:] = 1^n 0,
w[i:] = 1^n 0 1^m 0,
```

so `w[j:]` is a prefix of `w[i:]`. The run at `i` is state 0. Because `m-n >= 1`, the cut `j` occurs after at least one `1` transition from state 2 and therefore is in state 3. Thus

```text
(c(i), c(j)) = (0,3) in G.
```

This is a forbidden suffix agreement. The boundary case `n=0` is included: `j=m+1` is the final-zero cut in state 3, whose suffix is `0`, and the whole word also begins in `0` exactly when `n=0`.

### Case 2: n = m

Take

```text
i = 0,
j = n + 1.
```

The second cut is the entry to the second 1-block, in state 2. Both compared tails begin with the same word `1^n 0`:

```text
w[j:] = 1^n 0
```

and this is a prefix of `w[i:] = 1^n 0 1^n 0`. Therefore

```text
(c(i), c(j)) = (0,2) in G.
```

### Case 3: n > m

Take

```text
i = n - m,
j = n + 1.
```

The first cut is inside the initial 1-block exactly `m` ones before its zero, so `c(i)=1`. The second cut is the entry to the second block, so `c(j)=2`. Moreover

```text
w[i:] = 1^m 0 1^m 0,
w[j:] = 1^m 0,
```

hence the target tail is a prefix of the source tail and

```text
(c(i), c(j)) = (1,2) in G.
```

## Theorem

Every accepted word of this five-state instance is rejected by at least one explicit certificate from the schema above. Therefore the witness language is empty.

**Proof.** Every accepted word is `w(n,m)` for exactly one `n>=0,m>=1`. Exactly one of `n<m`, `n=m`, or `n>m` holds. The corresponding construction above returns cuts `i<=j` whose run-state pair belongs to `G` and whose target suffix is a prefix of the source suffix. That is exactly a forbidden agreement in the BorderAvoid witness predicate. Hence no accepted word is a witness. QED.

This certificate is finite as a schema: it consists of three arithmetic guards and three formulas for the two cuts. The instance parameters `n,m` may be unbounded, but the proof rule itself does not grow with them.

## Why this matters for A012

The same instance defeats the old strategy of waiting for some finite `Necessary(L,D)` language to become empty. For

```text
w_n = 1^n 0 1^(n+1) 0,
```

there is exactly one violating pair, `(i,j)=(0,n+2)`, with suffix length `n+1` and gap `n+2`. Thus

```text
Necessary(I,w_n,L,D)
    iff
n+1 > L and n+2 > D.
```

For every fixed finite `L,D`, choose sufficiently large `n`; a candidate survives the necessary test even though the instance has no witness. The three-case certificate succeeds because it allows the witnessing bad cut to depend symbolically on the candidate parameters rather than insisting that one finite comparison budget catches all candidates.

That distinction suggests a more general A012 direction: a complete NO calculus may need symbolic partitions of the candidate language together with a locally checkable violating-cut function on each part.

## Independent regression

Run

```sh
python3 experiments/check_five_state_no_certificate.py
```

The checker independently reimplements the partial DFA, direct forward suffix-agreement predicate, certificate construction, and the special `Necessary` identity. It does not import the PR #9 implementation.

The recorded result checks:

- all 1,056 parameter pairs `0<=n<=32`, `1<=m<=32` against their generated certificates;
- all 8,191 binary words through length 12, with all 55 accepted words parsed into the stated normal form and certified; zero witnesses;
- 25 special-family words `w_n`, each with exactly one direct violation;
- 4,225 `(n,L,D)` checks of the exact necessary-predicate identity.

These bounded checks support the implementation. The all-length result rests on the three-case proof above.

[Checker](../experiments/check_five_state_no_certificate.py) · [result](../results/five-state-no-certificate.json).

## Limitations and next target

This does **not** provide a complete certificate calculus for arbitrary terminal instances. The proof relies on a particularly simple two-parameter candidate language and a trichotomy that exposes one violating cut in each region.

The next discriminating target from issue #15 should be the seven-state different-gap NO example from the realizable last-flag spectrum work. A useful generalization would define a certificate object consisting of:

1. a regular or arithmetic partition of candidates;
2. a symbolic function selecting source/target cuts on each part;
3. a mechanically checkable proof that the selected states form a flag and the selected tails agree;
4. a finite coverage proof for the partition.

A finite set of sound rules is only progress. A012 is complete only after proving that every NO instance admits such a finite certificate and that certificate checking terminates effectively.
