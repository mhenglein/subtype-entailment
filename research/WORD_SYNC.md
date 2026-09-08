# Whole-word synchronization: proposed C048-C050 / E032

Base checkpoint: PR #6 (`256b287`). This continuation does not settle
unrestricted Problem 1.7. The following proposed claim records have written
proofs and finite reproduction, not Lean verification or independent review.

## Proposed claim records

<a id="c048"></a>
### C048 - Whole-word synchronization and a nonflat product decision

Given r>=2 binary DFAs with n_i states, a binary terminal BorderAvoid instance
with 3*sum(n_i)+2r+1 states has exactly the witnesses `(E(u)00)^r` where u
belongs to every input language, E(0)=10, E(1)=11. Flags compare unequal
predecessor tags at code boundaries. A longest-common-suffix argument proves
both directions. The constructed subclass, supplied with its DFA decomposition,
is decided exactly by a product of at most product(n_i) states. Every positive
instance has a witness of length at most 2r*product(n_i). No budget-preserving
encoding or unrestricted decomposition algorithm is asserted.

<a id="c049"></a>
### C049 - PSPACE hardness for the exact normalized signature

C048 reduces binary DFA intersection nonemptiness to terminal BorderAvoid.
Combining it with C030 gives PSPACE-hardness of non-entailment and entailment
for bottom and one binary covariant product, even on always-satisfiable
normalized systems, at the recorded proof status of the bridge. The source
problem's classical PSPACE-completeness is attributed in the full note.
No unrestricted PSPACE upper bound or decidability result follows.

<a id="c050"></a>
### C050 - Superpolynomial fixed-skeleton and straight-line descriptions

An explicit list of d+1 DFAs, with at most 6d^2+3d total states, has singleton
intersection C_d: the concatenation of all d-bit binary numbers, least-significant
bit first. Its compiled instance has k<=18d^2+11d+3 states and unique witness
W_d=(E(C_d)00)^(d+1). This word contains 2^d distinct factors of length 2d.
Every fixed-word power skeleton containing W_d needs body size at least
2^d/(2d), regardless of exponent magnitudes. Every ordinary binary straight-line
grammar for W_d needs at least 2^d/(2d-1) concatenation productions. Since the
witness is unique, no polynomial-size existence-preserving skeleton cover is
possible in general. Effective superpolynomial covers and richer representations
remain possible; a counting program itself describes this family compactly.

**Status of all three:** written proof, independent review requested. The
quantified statements rest on the proof, not on the finite sample below.

[Complete definitions, proofs, complexity citation, and limits](../notes/2026-09-05-word-synchronization.md).

<a id="e032"></a>
## E032 - Reproduction

```sh
python3 experiments/check_word_sync.py
```

[Implementation](../experiments/word_sync.py),
[counter generator](../experiments/counter_intersection.py),
[checker](../experiments/check_word_sync.py),
[result](../results/word-synchronization.json).

The standard-library run records 32,767 raw binary words; 3,785 block tuples;
all 4,096 pairs of total two-state input DFAs (1,858 YES, 2,238 NO);
120 additional random lists (19 YES, 101 NO); 196 full/reduced summary checks;
20 exact canonical-model checks; counting widths 1..6 and 642 single-bit
corruptions; 3,055 skeleton-factor tests. A deliberate cap returns UNKNOWN.
The two-state oracle is complete because its product has only four states,
not because a guessed word-length cutoff was assumed. The counter family
has a separate all-length uniqueness proof.

## Consequence

The new target is a complete shared-word/regular-constraint representation,
not an assumption that every long witness compresses into a polynomial-size
fixed repetition skeleton. This construction covers a genuinely nonflat
subclass but does not establish such a representation for arbitrary inputs.
