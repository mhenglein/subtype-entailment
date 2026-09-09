# Saved research recovery — September 9, 2026

Integration starts from `917ced2d49c3c7173368d99bf134bf7cc1212f42`.
This record publishes the two September 8 research bundles previously delivered
as local archives. It does not merge other branches or promote proof status.

## Durable contents

[Flag transport and separator-tail scope](FLAG_TRANSPORT.md) links the local
rewrite theorem, nine-state and nonflat eleven-state obstructions, general-data
reference solver, and their independent checks.

[Collective and cross-gap scope](COLLECTIVE_GAP_INFERENCE.md) links the guarded
cyclic rule, two exact bad-gap implication backends, greatest gap-equivalent
annotation, periodic-grid inference, finite three-stage census, and preserved
limits of the finite calculus. Both arguments remain **written proofs pending
independent mathematical review**, not new Lean theorems. Problem 1.7 remains
unresolved; finite normalization does not supply complete witness coverage.

The source/proof files are preserved byte-for-byte. The two large result files
are compact JSON without any data changes. Pretty-printing with Python's
`json.dumps(value, indent=2, sort_keys=True) + '\n'` recovers the original Git
blobs `7322020482b193eaa1259b01917e6f4c2b2170fc` and
`56ac73257de00c02ee8457b29111428754769adf` respectively.

## Checks performed before publication

Both original archives were independently extracted and their `reproduce.py`
commands rerun on September 9. Both completed successfully; every manifested
source, proof, and result byte was unchanged. The core and prior last-flag
regressions were included. This was a partial local snapshot, not a full local
repository CI or Lean build.

Run the recovered checks and verify all recorded identities with:

```sh
python3 scripts/check_recovered_research.py --replay
```

The [integrity script](../scripts/check_recovered_research.py) lists 17 exact
source/proof blob hashes and two canonical result hashes. It verifies them
before and after replay, then restores compact JSON serialization. Its checks
are integrity/reproducibility evidence, not mathematical refereeing.

## Shared-state integration

[The additive integration script](../scripts/integrate_recovered_research.py)
adds dated pointers to STATE, both approach histories, their evidence lists,
and the experiment index. It preserves existing owners, statuses, next steps,
unrelated evidence, and all earlier work. It is idempotent and has no Git writes.
The dedicated recovery workflow runs the replays and normal index checks first;
only the specially tagged recovery commit can activate its one-time metadata
publication step. That step uses a normal fast-forward push, never force.
Ordinary later changes run the read-only replay job only.

The full source for the separately named `synchronized_tail.py` companion is
not imported by this recovery: it was not in either saved archive. The distinct
`separator_tail.py` solver recovered here implements the documented arbitrary-
data combination and has its own source and regression provenance. No missing
artifact is silently presented as recovered.

## Next obligation

Retain the existing short necessary tests and exact arithmetic methods alongside
new flag inference. Neither the greatest gap-equivalent relation nor saturation
by the current cross-gap calculus is an unrestricted decision. A complete
refutation system needs an effective coverage theorem for richer candidate
contexts, or a different existence-preserving normalization argument.
