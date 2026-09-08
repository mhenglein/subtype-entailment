# A017/A012 continuation: synchronized tails and regular-marking barrier

Date: 2026-09-08. Base main: `c4875e599958dd624dd7220dd7cbe5bb96822b11`.

**Written proofs and reproducible experiments; independent mathematical review
pending; not Lean-checked. No unrestricted Problem 1.7 resolution.**
No new global claim/experiment numbers are assigned in this scoped continuation.

## Results

The combined synchronous-separator/semantic-tail construction supports arbitrary
nonflat data languages and original target recurrence. A weaker G-specific
compiler synchronizes only productive last-aligned pair paths; it preserves
witnesshood without preserving every irrelevant comparison. The locally tested
weighted spectrum and supplied-H search resolve the latest three-state
structural obstruction and earlier semantic/encoding fixtures.

A new six-state nonflat NO language defeats the closing strengthening.
Its words `0^(2m)1 0^m10` have exactly one violation. For every regular,
candidate-covering choice of optional separator marks, some annotation of a
sufficiently large such word survives every supplied finite marker-tail bound.
The proof covers deterministic history, finite lookahead and nondeterministic
regular decoration relations, plus finite families of such choices.

The barrier requires original candidates to remain covered and flags to remain
unchanged at original cut boundaries. It does not exclude genuine
existence-preserving word normalization, a symbolic arithmetic/shared-word
cover, a different complete NO calculus, or a subtype decision algorithm.

## Repository evidence and reproduction

[Full proof, precise quantifiers, and limitations](../notes/2026-09-08-synchronized-tail-and-regular-marking-barrier.md).
[Standalone independent barrier checker](../experiments/check_regular_marking_barrier.py).
[Standalone deterministic output](../results/regular-marking-barrier.json).
[Comprehensive local-run output](../results/synchronized-tail.json).

    python3 experiments/check_regular_marking_barrier.py

This repository-contained checker has no imports outside the standard library.
Seed 2026090863; 32,767 words through length 14, all 262 accepted words
certified, 300 longer nonflat candidates, 64 unique-violation words, 1,024
memoryless-decoration/bound checks, and 100 regular-relation viability checks.
Finite checks support, but do not prove, the quantified barrier theorem.

## Companion implementation: publication boundary

The full combined solver and its larger checker were executed locally and are
included in the session's standalone reproduction package. Their larger GitHub
source upload was blocked; they are NOT installed in this repository by this
contribution. The proof's implementation discussion describes that tested local
work. Do not infer repository availability from those inventory names.

Exact companion Git blobs:

- `experiments/synchronized_tail.py`: `28503784a4ff359c491940e00296dc94de33f1d4`;
- `experiments/check_synchronized_tail.py`: `91711fc7958bdb7f71b8893962eb0bdac402192b`;
- `results/synchronized-tail.json`: `c115c9768f360fe125cb40dd40c73ce9ab188ded`.

The companion checker includes 1,034 small instances, 240 acyclic oracles,
400 random terminal instances, nonflat data schemas and finite-memory/
lookaround tests. Its exact counts, parameters and limitations are in the full
proof and saved result. Two hash-seed runs were byte-identical. The previous
standalone lastflag result also reproduced byte-for-byte. No full local
repository CI, global index/link validation, or Lean build is claimed.

## Handoff

Do not restart the claim that larger finite-memory separator decorations plus
finite semantic tails must eventually refute every NO instance. The barrier
refutes it under the stated candidate-coverage/annotation model. Instead target
an effective G-specific normalization that may change or discard candidates
with proof, or a complete symbolic case cover. The new nonflat NO language has
an all-length three-case arithmetic certificate with an arbitrary regular
middle; its exact proof is the benchmark, not another budget search. A017
remains inconclusive on its unrestricted normalization target.
