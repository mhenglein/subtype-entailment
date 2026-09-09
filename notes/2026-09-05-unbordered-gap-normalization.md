# Unbordered gap normalization and profile descent

Date: 2026-09-05. Continues Q002/A017 after `dc90b7c`.

**Status: C045 retains its written proof plus bounded independent reproduction
under its exact hypotheses. Unrestricted Problem 1.7 remains open.**

**Status correction (2026-09-09).** Q003 is REFUTED; see
[Q003](../research/conjectures/Q003.md) and the
[modular counterexample](2026-09-05-modular-synchronization.md).
The unconditional descent conjecture and the conditional C045 lemma are
separate statements. The refutation does not refute C045, and C045 does not
supply its hypotheses for arbitrary witnesses. Original conjectural discussion
below is retained as history, not a live target. No new proof review is claimed.

## C045: unbordered gap deletion is profile-safe under terminal uniqueness

Let `M` be a partial deterministic automaton and let

    w = X s y s

be an accepted word ending in a terminal final state. Put `m=|s|>0`. Assume:

1. `s` is unbordered;
2. the run state immediately after the first `s` equals the run state
   immediately before the terminal `s`, so `y` is a state loop; and
3. in the shortened word

       v = X s s

   the terminal suffix of length `m+1` is unique.

Write `A(z)` for the full state-pair suffix-agreement profile of an accepted
word, including diagonal and empty-suffix agreements.

**Theorem.** `v` is accepted,

    A(v) subseteq A(w),

and `word_budget(v) <= m`.

Therefore, for every flag relation `G`, if `w` is a witness then `v` is also a
witness. If `m<=k-2` in a `k`-state terminal instance, this is directly a
`k-2`-budget normalization.

### Proof

Acceptance is immediate: deleting `y` splices equal run states, and the final
copy of `s` is read from the same state as in `w`.

Consider an agreement in `v` at positions `i<=j`, and let `ell=|v|-j` be the
target-suffix length. Empty-suffix agreements and diagonal agreements lift
because every state visited by `v` is also visited by `w`.

Suppose `i<j`. If `ell>=m+1`, then the occurrence at `i` contains an earlier
copy of the terminal length-`m+1` suffix: take the last `m+1` letters of the
matched factor. This contradicts hypothesis 3. Hence every proper agreement
has `ell<=m`, so its target lies wholly inside the second copy of `s`.

If the source occurrence lies wholly in `X` or in one of the two copies of
`s`, its letters and endpoint states occur unchanged in `w`, and the state
pair lifts directly. The only remaining possibility is that the source starts
inside the first `s` and its length-`ell` factor crosses the join between the
two copies in `v`. Write the crossing factor as

    suffix_r(s) prefix_t(s),    r,t>0, r+t=ell<=m.

It equals the terminal `ell`-suffix of `s`. Comparing the last `t` letters
forces

    prefix_t(s) = suffix_t(s),

where `0<t<m`, contradicting that `s` is unbordered. Thus no such crossing
agreement exists, and every agreement pair of `v` belongs to `A(w)`.

Finally, hypothesis 3 gives a unique terminal suffix of length `m+1`. By C041,
choosing that suffix in the exact budget formula gives `word_budget(v)<=m`.

### Double-copy corollary

For `X=epsilon`, hypothesis 3 follows automatically from unborderedness of
`s`: if the terminal length-`m+1` suffix of `ss` had an earlier occurrence,
dropping its first letter would give an occurrence of `s` in `ss` at a
nontrivial shift, hence a nonempty border of `s`. Therefore

    A(ss) subseteq A(sys)

whenever `s y s` is accepted with `y` a loop at the join, and
`word_budget(ss)<=|s|`.

## Why the uniqueness hypothesis is real

The tempting extension “use the earliest earlier copy of an unbordered `s`”
is false. Consider

    delta(0) = (1,2)
    delta(1) = (2,1)
    delta(2) = (3,2)
    delta(3) = (-1,-1)

with start 0 and terminal final 3. The accepted word

    w = 0101110

has terminal `s=10`. Its earliest occurrence starts at 1, and the state after
that copy equals the state before the terminal copy. Deleting the intervening
gap gives

    v = 01010.

But `v` has a new agreement pair `(0,1)`: its terminal suffix `010` now occurs
at the start. Exactly correspondingly, the terminal length-3 suffix is not
unique. This counterexample prevents promoting the broader earliest-copy rule.

## Q003: strict agreement-profile descent

The strongest current proof target is the following strengthening of Q002.
For every `k`-state terminal DFA and every accepted word `w` with

    word_budget(w) > k-2,

there exists a **strictly shorter** accepted word `v` such that

    A(v) subseteq A(w).

If true, repeated descent terminates and eventually reaches budget at most
`k-2`, proving Q002 and therefore the sharp terminal budget bound.

This is stronger than Q002: Q002 does not require its low-budget replacement
to be shorter than the supplied target.

A bounded adversarial search enumerated every accepted binary word through
length 12 for 1,200 random 5-state terminal tables, 900 random 6-state tables,
and 500 random 7-state tables. It tested 4,701, 1,048, and 271 high-budget
targets respectively, with target budgets up to eight. Every target had a
strictly shorter profile-dominated accepted word in the enumerated language.
This is falsification evidence, not an all-length theorem.

### Single-loop descent is false

Q003 cannot be proved by saying that one equal-state loop can always be
deleted. A six-state example has

    delta = ((1,2),(-1,4),(-1,3),(1,2),(5,4),(-1,-1))
    w = 1111011110

with `word_budget(w)=5`. Every single equal-state loop deletion creates a new
agreement pair. Nevertheless

    1111011110  ->  110110

is profile-safe by deleting two disjoint loops simultaneously, and the result
has budget three. A separate five-state example `11101110 -> 110110` exhibits
the same phenomenon.

A seeded falsification run over 1,643 high-budget random targets through eight
states found no case requiring more than two simultaneous loop deletions; two
cases required exactly two. This observation is not promoted to a theorem.
It suggests that a successful proof may need an Anderson-style interaction of
multiple pump-downs rather than a single-loop lemma.

## Relation to Anderson et al.

Anderson et al. prove a `6n+1` bound for ordinary unbordered words by combining
multiple pump-downs on opposite sides of a long word. Their Claims 59-61 are
precisely relevant to the two-loop phenomenon above. C039 adapts that proof
when a source's flagged target set is forward closed. For arbitrary colours,
the proof still loses the target colour when the final border start moves
inside the right periodic region; no valid generalization is claimed here.

The next useful route is to understand whether two or finitely many loop
pump-downs can always be chosen so that the *state-pair agreement profile*
only decreases. Q003 captures exactly the descent statement needed; C045 is a
proved local case where the cancellation can be certified syntactically by an
unbordered terminal block and one unique longer suffix.
