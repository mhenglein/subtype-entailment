# Semantic marker-tail continuation (A012/A017)

Date: 2026-09-08. Base main: `99133037a60f65c8e0fab5ed9299524fbd95043e`.
**Written proofs and executed checks; independent mathematical review pending;
not Lean-checked. Unrestricted Problem 1.7 remains unresolved.** This is the
scoped claim/experiment record; no colliding global IDs are allocated.

## Results

For every supplied H, existence in the H-marker-tail relaxation is decided by
an exact finite shared-reference/powerset construction. The arbitrary prefix
may revisit all original flag-target states. An exhausted relaxation NO is
unrestricted NO; a relaxation YES need not be a witness.

A joint word-action algorithm decides whether the numbers of final-bit markers
in actual last-aligned violations are bounded, and computes the exact maximum
or a positive-cost pumping certificate. Zero-cost cycles are not confused with
unbounded cost. Finite marker spectra make the relaxation exact and give a
complete decision for that certified class.

A reset-marker corollary handles arbitrary terminal automata whose marker
edges all lead to one reset state or the final state. A six-state nonflat NO
instance with recurrent marker targets is solved at H=1 although every finite
necessary length/gap language is inhabited and its comparison lengths are
unbounded. Removing one flag gives a checked positive companion, 1110110.

An exact two-letter uniform encoding of the older five-state NO obstruction
has an inhabited relaxation at EVERY H. Therefore increasing raw marker bounds
is not a complete negative semiprocedure. This failure is retained, not hidden
behind UNKNOWN. A general complete encoding-aware or shared-obligation method
is still missing.

[Full statements, proofs and limitations](../notes/2026-09-08-semantic-marker-tails.md).

## Reproduce

```sh
python3 experiments/check_marker_tails.py
python3 experiments/run_experiments.py
```

[Relaxation](../experiments/marker_tail.py),
[weighted spectrum/semantic decision](../experiments/marker_spectrum.py),
[independent checker](../experiments/check_marker_tails.py),
[result](../results/semantic-marker-tails.json).

Seed 2026090821: 2,984 weighted graph analyses, 15,471 lasso checks, 800 complete
acyclic relaxation queries, 200 complete acyclic semantic decisions, 366 exact
spectra, 360 complete queries over 75 infinite equality-schema languages,
82,810 tuple checks, and 1,034 small terminal instances. Short-word diagnostics
are not NO oracles. All explicit input/resource guards preserve their scope.
The unchanged core output is byte-identical to blob
`aa6d1680b5442493744c667024d2df77a1bd8e78`.

No full local repository CI, global link scan or Lean build was run. The
registry/tracker comparison is scoped: original registry and rendered tracker
were reconstructed byte-for-byte before changing A012/A017. Other branches,
claim IDs, Q labels and evidence statuses are not silently merged or promoted.
