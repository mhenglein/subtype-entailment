# A012/A017: collective and cross-gap flag inference

Date: 2026-09-08. Reviewed main: `5f65593175b6639e35cef3e9f20016d9600069ad`.

**Written all-length proofs plus reproduced tests. Independent mathematical
review pending. Not Lean-checked. Unrestricted Problem 1.7 is not resolved.**
No new global claim/experiment IDs are allocated by this scoped contribution.

## Exact results

Guarded predecessor closure permits cyclic collective flag proofs, ranked by
the strictly decreasing source-cut position. It repairs the latest six-state
regular-decoration barrier: the equivalent annotation has exact last-aligned
length bound two and an exhausted 14-state Necessary(2,0) NO certificate.

A maximal-periodic-suffix construction decides implication of bad-gap sets
for EVERY admissible word and EVERY gap. Two exact finite backends preserve
one common assignment to all repeated factors and handle diagonal/empty-tail
cases. They compute the greatest gap-equivalent annotation on a fixed table.
This annotation is optimal for latest-hit suffix length, not for a cost whose
marking changes with the flags.

A seven-state three-block NO instance defeats every such gap-equivalent
length/budget normalization. A separate periodic-grid inference escapes that
limit by discharging a comparison at a multiple of its gap. It adds (0,2),
then collective backward inference derives the final-column flag (4,6) and
proves NO. The combined finite calculus terminates but is not a complete
witness-existence procedure.

## Reproduction

    python3 experiments/check_collective_research.py
    python3 experiments/run_experiments.py
    python3 experiments/check_lastflag_spectrum.py

[Proof, exact boundaries, and counterexamples](../notes/2026-09-08-collective-and-cross-gap-transport.md).
[Checker](../experiments/check_collective_research.py).
[Deterministic result](../results/collective-gap-research.json).

The complete finite three-block annotation census has 709 YES and 3,387 NO
among all 4,096 effective flag relations; the calculus closes every NO.
This is one table, not all seven-state inputs. Independent finite-language
oracles, two all-input implication backends and literal predicates check the
interfaces. See the result for exact seeds, counts, caps and coverage.

## Preserved limit and handoff

A second seven-state NO example remains at a saturated flag fixed point with
unbounded last-aligned lengths, while Necessary(1,0) independently proves NO.
Therefore saturation followed ONLY by the bounded-spectrum criterion is
incomplete. Retain existing regular/necessary/arithmetic certificates.

The next closing obligation is completeness of a proof-producing combination
with candidate-context splitting or a different existence-preserving finite
cover. Finite flag saturation alone does not supply it. No underlying subtype
semantic theorem is promoted by these results.
