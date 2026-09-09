# Paired-state pumping for mismatched overlap borders

Date: 2026-09-09. Continues the single-source synchronized-deletion line.

**Status: proved finite-word pumping lemmas and a large-shift/small-shift dichotomy. The lift through every periodic-root copy is still pending; no decision theorem is claimed.**

## 1. Setting

Suppose two equal factors of an accepted word occur at positions `a<b`:

    w[a:a+r] = w[b:b+r].

Write `p=b-a`. The difficult junction-mismatch case from the previous note is
most useful when the occurrences overlap, `p<r`. Then their union has local
period `p`.

The run states are `c(0..|w|)` in an `n`-state deterministic automaton.

## 2. Two disjoint aligned loop deletions preserve the equality

**Lemma 1 (paired deletion).** Pick aligned offsets `0<=t<t'<=r`. Assume

    c(a+t)  = c(a+t'),
    c(b+t)  = c(b+t'),

and the two deletion intervals

    I=[a+t,a+t'),   J=[b+t,b+t')

are disjoint. Delete both intervals. The resulting word is accepted. Moreover,
if both deletions lie strictly inside the two displayed equal occurrences, the
surviving versions of those occurrences are still equal after deleting the
same relative subfactor `[t,t')` from each.

*Proof.* Equality of the factors gives

    w[a+t:a+t'] = w[b+t:b+t'].

The first state equality makes deletion of `I` a valid deterministic loop
splice. Because `I` and `J` are disjoint, the positions corresponding to the
endpoints of `J` survive with run states `c(b+t),c(b+t')` (shifted in index if
`I` is earlier). Their equality therefore makes the second splice valid. Both
occurrences have had the same aligned word removed, so their remaining letters
are equal. QED.

The same argument works for any finite list of pairwise disjoint aligned
intervals whose endpoint-state equalities hold before the earlier deletions;
process them left to right.

## 3. Large shift: `p>n^2` gives a short disjoint paired pump

Consider the `n^2+1` aligned offsets

    t = q, q+1, ..., q+n^2

inside a region where both occurrences have at least `n^2` letters of margin.
Associate to `t` the state pair

    P_t = (c(a+t), c(b+t)).

Two offsets `t<t'` have the same pair. Hence both endpoint-state equalities of
Lemma 1 hold, and

    1 <= t'-t <= n^2 < p.

Because the starts of the two occurrences differ by `p`, intervals of common
length `<p` at the same relative offset are disjoint. Lemma 1 therefore gives
a strictly shorter accepted word while preserving the aligned factor equality.

So in the overlap-mismatch case, **a shift `p>n^2` is pumpable whenever the
equal factors contain an interior aligned window of `n^2+1` offsets away from
protected endpoints**.

## 4. Small shift: `p<=n^2` gives a bounded local period

When `p<=n^2`, the union of the overlapping equal factors has period at most
`n^2`. Along any sufficiently long interior portion of this local-period zone,
look at run states at one fixed phase modulo `p`:

    c(q), c(q+p), c(q+2p), ... .

Among `n+1` such positions two states coincide. Deleting between them removes
a positive multiple of `p`; by the aligned local-period lemma from the previous
note, acceptance and the local `p`-periodic letter pattern survive the splice.
The deleted length is at most `n p <= n^3` if consecutive `n+1` phase samples
are used.

This is not yet as strong as Lemma 1 because one deletion inside an overlap can
occur at different relative offsets in the two compared occurrences. The
important reduction is quantitative: the only residual overlap case has a
local period bounded by `n^2`, independent of the large root length.

## 5. Dichotomy for the remaining single-source proof

After protecting the short defect/tail and handling matched-junction borders,
a long mismatched-junction overlap can be split as follows:

* `p>n^2`: use paired run-state pumping to delete the same aligned word from
  both occurrences, preserving their equality exactly;
* `p<=n^2`: the mismatch lives in a locally periodic zone of bounded period,
  so only a bounded-phase pumping argument remains.

The large-shift branch is particularly promising because it preserves the
problematic equality by construction rather than requiring a new border
correspondence theorem.

## 6. Remaining lift through the root copies

The shape theorem's periodic prefix contains at most `n+2` copies of the large
root. A surgery on the root phase must be repeated in every copy that survives
before the defect. To turn Lemma 1 into a shortest-witness contradiction, the
endpoint signature should therefore store, for each relevant root copy, the
**pair** of automaton states at the two aligned factor occurrences. There are
only finitely many such tuples because the number of copies is bounded by the
shape theorem.

A pigeonhole argument over a sufficiently large root can then seek two relative
offsets with the same full paired-state tuple. What remains to check carefully
is placement: all repeated deletions must be pairwise disjoint, avoid the
`<2n` defect/tail neighborhood, and leave the T-border target state unchanged.
No claim is made here that these inequalities have already been closed.

The proof search is therefore reduced to an explicit finite placement problem,
not a new word-combinatorics mystery: the equality-preserving pump for the
large-shift branch is Lemma 1, while the small-shift branch has period at most
`n^2`.
