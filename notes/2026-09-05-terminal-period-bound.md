# Bounded overlap exponent for terminal violations

Date: 2026-09-05. Continues A017 after commit `af6cde5`.

**Status: WRITTEN PROOF + REPRO. Not Lean-checked.** This is a structural
restriction on every terminal violation. It does not by itself decide terminal
BorderAvoid or unrestricted Problem 1.7.

## C038: every terminal suffix violation has bounded exponent

Let I be a k-state partial deterministic automaton whose accepting states are
terminal. Let w be a defined accepted word of length n, with run states c(t).
Suppose i<j and the suffix at j is a prefix of the suffix at i:

    w[j:] is a prefix of w[i:].

Put d=j-i and N=n-i. Then the whole source suffix w[i:] has period d: for each
x with i <= x < n-d,

    w[x] = w[x+d].

Consequently the suffixes beginning at

    i, i+d, i+2d, ..., i+floor(N/d)d

form a chain under the prefix relation. C036 applies to every adjacent pair in
this chain, so their starting run states are pairwise distinct. There are only
k states. Therefore

    floor(N/d) + 1 <= k,

or equivalently

    floor((n-i)/(j-i)) <= k-1.

This is sharp. A k-state unary path of length k-1 ending at a terminal final,
with a flag from the start to the next state, has i=0, j=1, N=k-1, d=1.

Writing N=t d+r with 0<=r<d, and y=w[i:j], the same periodicity gives the
normal form

    w[i:] = y^t prefix_r(y),       1 <= t <= k-1.

Thus an overlapping forbidden comparison can never require an unbounded
number of copies of its gap word. The gap word itself can still be arbitrarily
long, and a non-overlapping comparison is simply the t=1 case with an arbitrary
regular middle region before the terminal copy. This is why C038 is not a
finite word-length bound.

If (c(i),c(j)) is flagged, this factorization is an exact structural form of a
proper violation. Conversely any accepted word with such positions and the
stated equality is a violation. The theorem does not require that the flagged
pair be the last flag of C037; it applies to every proper suffix agreement on a
terminal accepted run.

## Relation to the remaining cyclic pair graph

A productive cycle in the unflagged synchronized-pair graph can make one
particular comparison arbitrarily long only by increasing its gap d as well.
For fixed d, terminality caps the number of aligned d-shifts at k. This removes
one source of unboundedness from C037's cyclic residuals, but does not yet bound
d itself or the number of different gap words a witness may traverse.

This suggests splitting the remaining problem into:

1. bounded-use equality patterns, now guaranteed by C038; and
2. regular control of where the captured gap and its terminal copy occur.

The non-overlap case has the canonical one-backreference shape A(B)_x C x at
the language level, while overlap gives at most k-1 consecutive uses of a gap
word plus one prefix remainder. This resemblance to restricted backreference
languages is only a research direction. No undecidability transfer is claimed.

## Literature caution

Freydenberger's extended-regex universality result shows that one-variable
backreference formalisms can remain undecidable even when the number of variable
occurrences is bounded in the construction. That result cannot be applied
verbatim here: terminal BorderAvoid violations repeat a suffix reaching the end
of the word and impose the periodic-overlap form above, which is substantially
more constrained than an arbitrary one-variable extended regular expression.
An exact reduction would still be required.

The 2026 1-use REWB canonical form A(B)_x C x D is a closer match to the
non-overlap part, but its published result concerns matching complexity, not the
universality question needed here. We therefore record the connection without
promoting it to a decidability or undecidability claim.

## E026: finite validation

Run

    python3 experiments/check_terminal_period_bound.py

The seeded run checks 2,000 random terminal automata, all accepted binary words
through length 9, and every flagged suffix agreement found. It verifies both
the period identity and the state-chain proof obligations, and separately checks
the sharp unary family for k=2..8.

Recorded result: 11,631 accepted words and 11,918 flagged agreements, with no
failure. The maximum observed full-period count is six. These finite checks
support the implementation only; the quantified claim rests on the proof above.
