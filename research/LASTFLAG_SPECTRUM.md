# A017 continuation: realizable last-flag length spectra

Date: 2026-09-07. Base: `8e6c2e6c13754436871ff440cd52cd3e60294a74`.

**Evidence: written proofs plus reproduced checks. Independent mathematical
review pending. Not Lean-checked. No unrestricted Problem 1.7 decision.**
No new global C/E identifiers are allocated in this scoped continuation, to
avoid conflicting with still-separate scientific branch records.

## Exact result

For a terminal input, the lengths of actual last-aligned-flag comparisons in
boundary-safe accepted words have an effectively unary-regular presentation.
The construction uses bounded periodic exponents and JOINT word actions on
single states and synchronized pairs; it retains one common word assignment.
The uncapped algorithm decides boundedness and computes the exact maximum H
when finite, or supplies a pumping certificate when unbounded.

Finite H makes Witness exactly Necessary(H,0), yielding a sound partial
existence decider strictly stronger than the acyclic last-flag graph test.
A five-state example has H=1 although that graph has a productive cycle.
Unbounded spectra remain UNKNOWN for witness existence. A seven-state NO
example has an unbounded spectrum but an exact one-letter detection bound,
so boundedness of globally minimum violations is a different property.

## Evidence and reproduction

[Full proof, strict example, counterexample, and limits](../notes/2026-09-07-realizable-lastflag-spectrum.md).
[Implementation](../experiments/lastflag_spectrum.py).
[Independent-predicate checker](../experiments/check_lastflag_spectrum.py).
[Saved output](../results/lastflag-spectrum.json).

    python3 experiments/check_lastflag_spectrum.py
    python3 experiments/run_experiments.py

Seed 2026090719; 1,034 exhaustive small instances, 240 complete acyclic
oracles, 600 random terminal instances, 746 transformation-generator pairs,
and six analytic fixtures. See the proof note/result for exact counts and
cutoffs. Random monoid/combination caps are 5,000/2,000,000; all caps retain
UNKNOWN. The original core result remains byte-identical. No full repository
CI, global link scan, or Lean build was run from the partial snapshot.

## Handoff

A017 remains inconclusive on its unrestricted target. Distinguish boundedness
of all LAST-ALIGNED comparison lengths from boundedness of the GLOBAL minimum
violation per bad word. Any next invariant must coordinate different gaps in
one word and must pass both the seven-state short-detectable regression and
the prior five-state necessary-budget counterexample. Even the latter property
alone is not a complete NO method for every terminal instance.
