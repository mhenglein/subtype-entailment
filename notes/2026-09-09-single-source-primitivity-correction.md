# Single-source synchronized deletion: primitivity correction and sharper remaining gap

> **Continuation, 2026-09-09:** C065 supplies a different written decision
> proof for single-source terminal instances, via prefix-free source capture
> and existential word equations. Independent mathematical review is pending.
> See [the new construction and exact scope](2026-09-09-source-capture-word-equations.md).
> The pumping obligations and strategy recommendations below are historical;
> the new result does not assert that those pumps have been proved. The
> unrestricted problem remains unresolved in this repository.

Date: 2026-09-09. Continues `notes/2026-09-08-single-source-shape-lemmas.md`.

**Status: written correction + exhaustive diagnostic. Not Lean-checked. This does not decide the single-source problem or unrestricted Problem 1.7.**

## 1. The primitivity sub-obligation in Section 6 is unnecessary

The existing synchronized-window proposal starts from a primitive root `z0` of
length `d0`, deletes the same nonempty phase interval `[phi,phi')` from every
copy, and obtains a shorter block `z~` and a shorter accepted word `w~` whose
long periodic prefix is a prefix of `z~^omega`. The construction also arranges
that

    w~ is |z~|-periodic  iff  w is d0-periodic.

Since the original shortest witness `w` is not `d0`-periodic, `w~` is not
`|z~|`-periodic.

Section 6 listed as a missing step the possibility that `z~` is imprimitive,
`z~ = r^k` with `k>1`, because the shortened word might then be `|r|`-periodic.
That possibility is impossible:

**Lemma (root normalization after synchronized deletion).** Let `u` be a
nonempty word, let `r` be its primitive root, and let `W` have a prefix of
`u^omega` of length at least `|u|`. If `W` is not `|u|`-periodic, then `W` is
not `|r|`-periodic. Consequently Lemma 3 of the shape note applies to `W` with
primitive root `r`.

*Proof.* Write `u=r^k`. If `W` had period `|r|`, then it would also have every
multiple of `|r|` below `|W|` as a period, in particular `|u|=k|r|`. This
contradicts the hypothesis. The prefix of `u^omega` is also a prefix of
`r^omega`, so Lemma 3 applies. QED.

The resulting border bound is at least as strong as the one desired with the
possibly imprimitive block:

    every border of W has length < |W|-X+|r|
                              <= |W|-X+|u|.

Therefore synchronized deletion does **not** need to preserve primitivity of
the shortened block. The first missing step listed in Section 6 can be deleted.
Only the border-correspondence/new-border problem remains.

## 2. Why counting all primitivity-destroying windows would have been the wrong route anyway

A separate exhaustive diagnostic enumerated every primitive binary word through
length 15 and every nonempty proper deletion interval. It counted intervals
whose deletion leaves an imprimitive word. The maximum observed values are
recorded in `results/primitive-deletion-windows.json`.

There is an elementary quadratic lower-bound family. Take a primitive word of
length `n` with exactly one `1`, at an interior position `a`. Every deletion
interval containing that `1` and leaving at least two symbols produces `0^k`,
hence an imprimitive remainder. There are

    (a+1)(n-a) - 3

such intervals: all intervals containing the `1`, minus the full-word deletion
and the two deletions leaving one endpoint symbol. Centering the `1` gives

    floor((n+1)^2 / 4) - 3

bad intervals. The exhaustive maximum equals this value for every `n=3..15`.
The equality is only an observation; the displayed lower bound is proved.

Thus the hoped-for argument "only few deletion windows destroy primitivity"
would have failed even if primitivity mattered. The correction in Section 1
removes that dead end completely.

## 3. Sharpened remaining obligation: junction-created borders

After root normalization, the sole missing step in the synchronized deletion
programme is:

> choose synchronized endpoints so that every T-border of the shortened word
> lifts to a T-border of the original word, or otherwise derive a contradiction.

The defect-tail word `mt` has length `<2n`. In the border characterization from
the shape note, any new border requires an occurrence of `mt` at a phase of the
shortened cyclic root. Hence a first local obstruction is a **new occurrence of
`mt` created across the deletion junction**.

This part can be eliminated by enriching the endpoint signature with a bounded
left context.

**Local junction-factor lemma.** Let a cyclic word `z` have cut positions
`phi<phi'` with identical `L` letters immediately before the cuts (cyclically).
Delete `[phi,phi')` and join the prefix before `phi` to the suffix after `phi'`.
Every factor of length at most `L` that crosses the new junction already occurs
in the original cyclic word crossing `phi'`.

*Proof.* A crossing factor consists of `s` letters immediately before `phi`
and `ell-s` letters immediately after `phi'`, with `ell<=L`. Equality of the
`L`-letter left contexts replaces the first piece by the `s` letters
immediately before `phi'`; the concatenation is exactly the original factor
crossing `phi'`. QED.

Taking `L=|mt|<2n` means the deletion cannot create a genuinely new `mt`
occurrence at its junction. Since the state-synchronization pigeonhole already
uses a finite signature, adjoining the preceding `2n` input letters only
multiplies the number of signature classes by at most `2^(2n)`; it preserves a
computable large-root pigeonhole argument.

This does **not yet finish border correspondence**. A border also requires a
possibly long equality between the root prefix and the factor preceding the
actual defect phase. Even when the short `mt` occurrence is old, deleting one
phase interval can make those two longer factors equal because the deleted
block may occur at different relative offsets in the two compared factors.
That is now the exact residual combinatorial problem.

## 4. Next target

The remaining proof should split candidate borders according to whether the two
long compared factors cross the deleted phase interval at the same relative
offset.

* If they do, reinserting the deleted block on both sides should lift the border
  to the original word, with state equality supplied by the synchronized
  endpoint tuple.
* If they do not, the equality in the shortened root gives two occurrences of
  the deletion junction at different relative offsets inside equal factors.
  The expected consequence is a nontrivial local period of the shortened root;
  Fine-Wilf may then force either a smaller root period or a bound on the border
  length. This is the remaining theorem to prove.

The important narrowing is that **primitivity is no longer part of the problem,
and short defect occurrences can be protected by finite local context**. The
only unresolved phenomenon is long prefix/factor equality with mismatched
junction offsets.

## 5. Reproduction

`experiments/primitive_deletion_windows.py` enumerates the finite diagnostic;
`results/primitive-deletion-windows.json` records the exhaustive maxima through
length 15. Those counts are evidence only. The root-normalization and local
junction-factor lemmas above are all-length arguments.
