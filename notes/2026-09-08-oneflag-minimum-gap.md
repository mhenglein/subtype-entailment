# One flag already separates last-aligned length from the global minimum

Date: 2026-09-08. Workstream: A017. Consolidated claim: C064.

**Status: written all-length argument plus deterministic reproduction; independent review pending; not Lean-checked. This does not settle Problem 1.7.**

## 1. Instance

Take start state `0`, sole terminal final state `3`, no Bad states, and

    G = {(0,1)}.

The binary transition table is

| state | 0 | 1 |
|---|---:|---:|
| 0 | 0 | 2 |
| 1 | 3 | 0 |
| 2 | 1 | 1 |
| 3 | undefined | undefined |

For every `r>=0`, let

    z_r = 10 1^(3r+2) 0,
    w_r = z_r z_r.

Then `|z_r|=3r+5`.

## 2. Unbounded last-aligned spectrum

On letter `1`, the nonfinal states cycle `0 -> 2 -> 1 -> 0`. A direct transition calculation gives

    delta(0,z_r)=1,
    delta(1,z_r)=3.

Hence `w_r` is accepted and its midpoint is state `1`. Positions `0` and `|z_r|` therefore form the forbidden pair `(0,1)`, and the target suffix is exactly `z_r`, of length `3r+5`.

This comparison is last-aligned. After the first aligned `1` the state pair is `(2,0)`, after the following `0` it is `(1,0)`, and under the subsequent ones it cycles

    (1,0) -> (0,2) -> (2,1) -> (1,0).

The sole flag `(0,1)` is never re-entered at a positive aligned offset; the final zero reaches `(1,3)`. Thus the realizable last-aligned violation lengths are unbounded.

## 3. Every bad accepted word has a one-letter violation

The first draft established `mu(w_r)=1` only on the displayed square family. That is not enough to characterize the whole bad language. The following argument supplies the missing all-word statement.

Every nonempty accepted word ends with a `0` read from state `1`, because `1 --0--> 3` is the only transition into the terminal final state.

Suppose an accepted word has an earlier occurrence of `0` read from state `0`. Since `0 --0--> 0`, that position is a source state `0`, while immediately before the final zero the state is `1`. The one-letter target suffix `0` therefore agrees at the earlier source position and gives the forbidden pair `(0,1)`. Hence every such bad word has minimum proper violation length one.

Conversely, suppose an accepted word has **no** earlier zero read from state `0`. We show that it cannot contain any forbidden proper agreement at all. Any matching comparison rooted at `(0,1)` evolves synchronously. On symbol `1` its pair orbit is

    (0,1) -> (2,0) -> (1,2) -> (0,1).

A zero cannot be read while the pair is `(0,1)` or `(2,0)` without using the excluded state-0 zero transition in one of the two occurrences. At pair `(1,2)`, reading zero would send the earlier/source occurrence to terminal state `3` while the later occurrence continues, so it cannot realize a proper target suffix of an accepted word. Therefore a forbidden comparison rooted at `(0,1)` cannot reach the later occurrence's final zero. No proper forbidden agreement exists.

Thus an accepted word is bad **iff** it contains an earlier state-0 zero, and every bad accepted word has

    mu(w)=1.

The global set of proper minimum violation lengths for this one-flag instance is therefore exactly `{1}`, while its last-aligned violation spectrum is unbounded.

For the specific square `w_r`, the short violation occurs after the first symbol of the second copy and immediately before the final zero, exactly as in the original construction.

## 4. Consequence

The implication

    one flag + unbounded realizable last-aligned spectrum
        => unbounded global minimum violation lengths

is false even for a four-state terminal instance. The obstruction does not require multiple flag colours: distinct occurrences of the same ordered pair can generate a growing comparison and a constant-short comparison in the same language.

This does not rule out a separate computable small-witness theorem for terminal one-flag instances. The present automaton itself has short witnesses `100` and `110`.

No lower bound from C021 is transferred here. C021's extremal family has nonterminal accepting behavior, so it cannot be used as a terminal one-flag lower bound without an additional reduction that preserves the relevant parameters.

## 5. Reproduction

`experiments/check_oneflag_minimum_gap.py` checks the explicit family for `r=0..200`, compares the forward and reversed witness predicates, and exhausts bounded words. The consolidated regression additionally checks the strengthened all-bad-word characterization on a larger finite prefix of the language. Finite tests support the implementation; the unbounded and all-word conclusions above rest on the written argument.
