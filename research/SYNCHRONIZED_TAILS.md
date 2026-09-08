# A017/A012 continuation: synchronized tails and regular-marking barrier

Date: 2026-09-08. Base main: `c4875e599958dd624dd7220dd7cbe5bb96822b11`.

**Written proofs and reproducible experiments; independent mathematical review
pending; not Lean-checked. No unrestricted Problem 1.7 resolution.**
No new global claim/experiment numbers are assigned in this scoped continuation.

## Results

The combined synchronous-separator/semantic-tail construction supports arbitrary
nonflat data languages and original target recurrence. A weaker G-specific
compiler synchronizes only productive last-aligned pair paths; it preserves
witnesshood without preserving every irrelevant comparison. The installed
weighted macro spectrum and supplied-H search resolve the latest three-state
structural obstruction and earlier semantic/encoding fixtures.

A six-state nonflat NO language defeats the closing finite-decoration
strengthening. Its words `0^(2m)1 0^m10` have exactly one violation. For every
regular, candidate-covering choice of optional separator marks, some annotation
of a sufficiently large such word survives every supplied finite marker-tail
bound. The proof covers deterministic history, finite lookahead and
nondeterministic regular decoration relations, plus finite families.

The barrier requires original candidates to remain covered and flags to remain
unchanged at original cut boundaries. It does not exclude genuine
existence-preserving word normalization, a symbolic arithmetic/shared-word
cover, a different complete NO calculus, or a subtype decision algorithm.

A first symbolic-NO rule has now also been extracted from the barrier. The
three-way certificate decides the entire family `a* b M a+ b a` whenever a
supplied regular middle M satisfies two finite control conditions and the three
arithmetic cases `n<m`, `n=m`, `n>m` map to fixed flags. Its verifier proves
candidate-language equality by finite symmetric difference rather than bounded
enumeration. This is a reusable all-length certificate rule, not merely a
restatement of the six-state example.

## Repository evidence and reproduction

[Full barrier proof, precise quantifiers, and limitations](../notes/2026-09-08-synchronized-tail-and-regular-marking-barrier.md).
[Arbitrary-data macro-tail proof](../notes/2026-09-08-macro-marker-tails.md).
[Three-way NO-certificate proof](../notes/2026-09-08-three-way-cut-certificates.md).

Installed executable layers:

- [macro-tail solver](../experiments/macro_marker_tail.py);
- [macro separator spectrum](../experiments/macro_marker_spectrum.py);
- [productive last-aligned separator compiler](../experiments/last_aligned_separators.py);
- [three-way symbolic NO verifier](../experiments/three_way_cut_certificate.py);
- [combined-tail regression](../experiments/check_macro_marker_tails.py);
- [last-aligned compiler regression](../experiments/check_last_aligned_separators.py);
- [three-way verifier regression](../experiments/check_three_way_cut_certificate.py);
- [standalone independent barrier checker](../experiments/check_regular_marking_barrier.py).

Recorded outputs include
[macro tails](../results/macro-marker-tails.json),
[last-aligned separators](../results/last-aligned-separators.json), and the
[regular-decoration barrier](../results/regular-marking-barrier.json).

The configured research workflow runs the installed tail/compiler/verifier
layers. The independent barrier workflow separately replays the standalone
barrier checker. Finite regressions support implementation correctness; the
all-length claims come from the linked written arguments.

## Companion implementation: publication boundary

The original continuation also produced a larger monolithic combined solver and
checker in the session's standalone reproduction package. Those exact companion
files are still not installed under their original names. Their results are not
needed to use the repository-contained modular replacements listed above.

Exact companion Git blobs retained for provenance:

- `experiments/synchronized_tail.py`: `28503784a4ff359c491940e00296dc94de33f1d4`;
- `experiments/check_synchronized_tail.py`: `91711fc7958bdb7f71b8893962eb0bdac402192b`;
- `results/synchronized-tail.json`: `c115c9768f360fe125cb40dd40c73ce9ab188ded`.

The companion checker included 1,034 small instances, 240 acyclic oracles,
400 random terminal instances, nonflat data schemas and finite-memory/
lookaround tests. The modular installed implementation now supplies the key
scientific layers directly on main with its own discriminating regressions.

## Handoff

Do not restart the claim that larger finite-memory separator decorations plus
finite semantic tails must eventually refute every NO instance. The barrier
refutes it under the stated candidate-coverage/annotation model.

The constructive A012 direction is now **finite symbolic cut-selector covers**.
The installed three-way rule demonstrates that a regular recurrent middle can
be discharged while only arithmetic relations between anchor-block lengths are
case-split. The next generalization should allow finitely many parameterized
unary/periodic blocks, a finite Presburger partition, and affine source/target
cut selectors whose flag/equality obligations are checked by finite automata.
A completeness theorem for such covers would yield a genuine terminating NO
semiprocedure; failure of one proposed cover remains UNKNOWN.

In parallel, A017 may seek an existence-preserving normalization that can change
or discard candidates with proof. Unrestricted Problem 1.7 remains open.