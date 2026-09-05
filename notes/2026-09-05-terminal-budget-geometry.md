# Terminal budget geometry and a failed residual-cycle shortcut

Date: 2026-09-05. Base: `a6e21938bce5ca4a88f81fb77a539eb460c22eb0`.

**Status: EXACT WORD-LEVEL IDENTITY + CERTIFIED COUNTEREXAMPLE + BOUNDED FALSIFICATION EVIDENCE.**
This does not settle unrestricted Problem 1.7 and does not prove the terminal
budget conjecture `B <= k-2`.

## C041: exact geometric form of a word's sufficient budget

Let `w` have length `n`. For each nonempty suffix length `m`, let

    a_m = the start position of the earliest occurrence of w[n-m:]
    j_m = n-m
    g_m = j_m-a_m.

Thus `g_m=0` exactly when the length-`m` suffix is unique. For every witness
word `w`, the repository's exact per-word budget satisfies

    word_budget(w) = min_{1 <= m <= n+1} (m-1 + g_m),

with the final `m=n+1` convention representing `L=n` and value `n`.
Equivalently, for the ordinary range `1<=m<=n`,

    word_budget(w) = min_m ((m-1) + distance from the earliest copy of
                             suffix_m(w) to the terminal copy).

**Proof.** In `border_lab.word_budget`, put `m=L+1`. `first_end(w,m)` is
`a_m+m`, so

    n-first_end(w,m) = n-(a_m+m) = (n-m)-a_m = g_m.

The minimized summand `L + n-first_end(w,L+1)` is therefore exactly
`m-1+g_m`. The witness hypothesis is needed only because `word_budget` is
undefined on non-witnesses; the string identity itself is unconditional.

This reframes the terminal candidate `B<=k-2`: it is enough to prove that every
positive k-state terminal instance has some witness with a suffix occurrence
geometry satisfying

    m + g_m <= k-1

for some suffix length `m`. A unique suffix of length at most `k-1` is the
special case `g_m=0`; uniqueness is not required in general.

C038 constrains a repeated terminal suffix in a complementary way. If its gap
is `d=g_m>0`, then terminal nonmerging bounds the number of aligned copies, but
does not directly bound `m+d`. Thus C038 alone does not prove the candidate.

## C042: local source viability plus a residual pair cycle does not imply YES

The following five-state terminal instance refutes a tempting strengthening of
C039/C040 and C037. Start state is 0, sole final is terminal state 4, Bad is
empty, and

    delta(0) = (1, -1)
    delta(1) = (3,  2)
    delta(2) = (1,  0)
    delta(3) = (4,  1)
    delta(4) = (-1,-1)

with

    G = {(0,1), (2,0), (2,3), (3,0)}.

The C037 last-flag overlap certificate is `CYCLIC`, so its finite detection
bound is unavailable.

Nevertheless every live nonfinal state has a suffix to the final satisfying
**that source state's own outgoing flags**:

    source 0: 01000
    source 1: 00
    source 2: 1000
    source 3: 0

Each displayed word is checked by the ordinary witness predicate after keeping
only flags whose source is the displayed state. Hence no sound source-only
impossibility theorem can remove any of these states merely because its own
constraints are unsatisfiable.

But the full instance is exactly NO: the finite `Necessary(2,0)` automaton is
empty (six reachable memory states in the reference implementation). Since
every genuine witness satisfies every Necessary predicate, this is a complete
nonexistence certificate, not a bounded word search.

So the attractive dichotomy

    source-prune to a fixpoint; if C037 is still cyclic, answer YES

is false in general. Multi-source interactions remain essential even when all
individual source obligations are realizable.

## E028: exact falsification search for the terminal B<=k-2 candidate

A separate standard-library search used the repository's exact finite Strong
Sandwich automata. For each generated k-state terminal instance it exhausted
**every** split `L+D<=k-2`. If all were empty, it additionally searched the next
four total budgets for a counterexample witness. Any returned positive word was
checked by the direct witness predicate.

Deterministic runs:

- k=5, seed 2026090525, 20,000 instances: 6,582 had a Strong witness with
  budget <=3; 13,418 had none; zero caps; no instance with empty budgets <=3
  and a witness at budgets 4..7.
- k=6, seed 2026090526, 15,000 instances: 4,762 had a Strong witness with
  budget <=4; 10,238 had none; zero caps; no instance with empty budgets <=4
  and a witness at budgets 5..8.
- k=7, seed 2026090527, 4,000 instances: 1,192 had a Strong witness with
  budget <=5; 2,808 had none; zero caps in the <=5 searches; no counterexample
  was found in the completed run.

This is falsification evidence only. An instance with no Strong witness in the
searched budget range may still have a witness at a larger budget, so these
counts must not be read as NO classifications. The exhaustive four-state
terminal result C034 remains the only all-instance result behind the `k-2`
candidate.

## Next proof target

The budget identity suggests attacking a **shortest witness** by its terminal
suffix geometry rather than by arbitrary loop deletion. If `word_budget>k-2`,
then for every `1<=m<=k-1` the terminal length-m suffix has an earlier occurrence
whose start gap satisfies

    g_m >= k-m.

Equivalently, every one of those earliest occurrences starts at or before
position `n-k`. This creates a nested staircase of repeated terminal suffixes.
A successful proof would show that such a staircase forces a sound shortening
or an already-forbidden flagged comparison in a shortest terminal witness.
The current loop-deletion counterexamples show that state repetition alone is
insufficient; the proof must use the simultaneous family of nested suffix
occurrences.
