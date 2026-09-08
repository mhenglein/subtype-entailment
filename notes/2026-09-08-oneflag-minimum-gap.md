# One flag already separates last-aligned length from the global minimum

Date: 2026-09-08. Workstream: A017. Base main: `99133037a60f65c8e0fab5ed9299524fbd95043e`.

**Status: explicit all-length counterexample + deterministic reproduction. Independent review pending; not Lean-checked. This does not settle Problem 1.7.**

## 1. Question

The September 7 last-flag continuation exhibited a seven-state, two-flag family in which a last-aligned violation can grow without bound while a different flag supplies a one-letter violation in the same word. A tempting repair is to restrict to a single forbidden ordered pair: perhaps then long last-aligned comparisons force the global minimum violation length to grow.

That repair is false. Four states and one flag suffice.

## 2. Instance

Take start state `0`, sole terminal final state `3`, no Bad states, and

    G = {(0,1)}.

The binary transition table is

| state | 0 | 1 |
|---|---:|---:|
| 0 | 0 | 2 |
| 1 | 3 | 0 |
| 2 | 1 | 1 |
| 3 | undefined | undefined |

For every integer `r>=0`, put

    z_r = 10 1^(3r+2) 0,
    w_r = z_r z_r.

Then `|z_r|=3r+5` and `|w_r|=6r+10`.

## 3. The square is always accepted

On letter `1`, the nonfinal states cycle

    0 -> 2 -> 1 -> 0.

Starting from state `0`, the prefix `10` reaches state `1`. Reading `1^(3r+2)` from `1` reaches `2`, and the final `0` returns to `1`. Hence

    delta(0,z_r)=1.

Starting from state `1`, the prefix `10` reaches state `0`. Reading `1^(3r+2)` from `0` reaches `1`, and the final `0` reaches terminal state `3`. Hence

    delta(1,z_r)=3.

Therefore `w_r=z_r z_r` is an accepted word whose midpoint state is exactly the flag target `1`.

## 4. An unbounded last-aligned violation

At positions

    i=0,
    j=|z_r|,

we have states `(0,1)` and

    w_r[i:] = z_r z_r,
    w_r[j:] = z_r.

Thus the target suffix is a prefix of the source suffix and gives a forbidden agreement of length `|z_r|=3r+5`.

It is last-aligned. Follow the two copies synchronously from the flagged root `(0,1)`. After the first `1` the pair is `(2,0)`; after the following `0` it is `(1,0)`. Under subsequent `1`s the pair cycles

    (1,0) -> (0,2) -> (2,1) -> (1,0).

None of these pairs is `(0,1)`. The final `0` reaches `(1,3)`. Hence no positive aligned offset enters the sole flag again. The midpoint comparison is therefore last-aligned for every `r`.

Consequently this ONE-FLAG instance has an unbounded realizable last-aligned length spectrum.

## 5. The same flag supplies a one-letter violation

Now look inside the second copy. It begins in state `1`. After its first symbol `1`, the run is in source state `0`; the remaining suffix begins with the next symbol `0`.

Immediately before the final symbol of the whole word, the run is in target state `1`, because the last transition of `z_r` is `1 --0--> 3`. The target suffix there is exactly the one-letter word `0`.

Thus positions

    i=|z_r|+1,
    j=2|z_r|-1

form another `(0,1)` forbidden agreement, now of target length one. Since proper target lengths are positive,

    mu(w_r)=1

for every `r>=0`, where `mu` is the global minimum proper violation length.

The short comparison is also last-aligned, so the same one-flag spectrum contains `1` as well as the unbounded sequence `3r+5`.

## 6. Consequence

The implication

    one flag + unbounded last-aligned spectrum
        => unbounded global minimum violation lengths

is false.

More strongly, the obstruction does not require two unrelated flag colours: two different gaps of the SAME ordered state pair can coexist in one word, one growing and one constant. Therefore any exact abstraction of global minima must coordinate multiple occurrences/gaps even in the one-flag class.

This invalidates the proposed shortcut of proving a one-flag decision merely by identifying the last-aligned spectrum with global-minimum behavior. It does **not** refute the possibility of a separate linear small-witness theorem for one-flag instances; this automaton itself has short witnesses (`100` and `110`).

## 7. Reproduction

Run

    python3 experiments/check_oneflag_minimum_gap.py

The deterministic checker verifies the formulas above for `r=0..200`, using both forward and reversed witness predicates. It also enumerates all binary words through length 14 for this instance, checks the explicit violation extractor against the witness predicates, and confirms the short witnesses.

Finite reproduction supports the implementation only; the unbounded conclusion rests on the all-`r` argument above.

## 8. Handoff

The useful surviving one-flag question is not whether different flags are needed—they are not. The next discriminating target is instead:

> If a terminal one-flag instance has any witness, must it have a witness of length bounded by a computable (perhaps linear) function of the state count?

C021 gives a one-flag lower family with unique shortest length `3k-3`, so any universal bound must be at least that large infinitely often. The present counterexample neither proves nor refutes a `3k-3`, `6k+O(1)`, or other computable upper bound.
