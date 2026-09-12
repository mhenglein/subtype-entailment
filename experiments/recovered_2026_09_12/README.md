# Recovered source-visit and closed-walk research

Integrated 2026-09-12 from the two complete research bundles delivered in the
preceding investigation. The canonical claims, experiment IDs, and handoff are
in [the recovery record](../../research/RECOVERED_SOURCE_WALKS.md).

## Read first

- [Source-visit proof](subtail_source_visit_bound/RESEARCH_NOTE.md): exact counts
  for the existing C046 modular family, live flags, and the prime-period lower
  bound. This does not refute Q004 or provide a general upper bound.
- [Counter-lift proof](subtail_closed_walk_lift/RESEARCH_NOTE.md) and
  [route outline](subtail_closed_walk_lift/ROUTE_OUTLINE.md): exact compilation
  for a supplied closed-source-walk power scheme, including repeated labels.
  The unrestricted finite-cover obligation remains open.

The original notes, source, compact checks, and checksum manifests are retained
byte-for-byte. Their statements that no remote files were changed describe the
original delivery, before this integration. They are not the current publication
status. The original exploratory search for the interior-deletion example was
not included in either bundle; its explicit fixed regression and checker are
included. No search log or additional review has been invented.

## Recover every original generated artifact and replay

From the repository root, using Python 3.10 or newer and the standard library:

```sh
python3 experiments/recovered_2026_09_12/reproduce.py
```

The command prints a new temporary output directory. To choose one, pass
`--output tmp/recovered-source-walks`; the directory must be new or empty.
Do not use Python's `-O` option: the archived tests use assertions.

The runner restores both original bundle layouts. In particular it generates
`results.json` with all 1,161 live-flag certificates, `run.log`, the complete
1.3 MB `formula-example.json`, and `witness-model.json`. These four deterministic
outputs are not duplicated in Git: their full generators, original SHA256 hashes,
and byte lengths are committed. Every recovered file is checked against the
original manifests before the positive certificate is accepted. There is no
network download, external solver, or reliance on this chat.

The historical commands in each bundle's README operate in the recovered
output directory, where all generated files are present. The expanded formula
contains no opaque power operator; the explicit assignment produces `1010110`.

[Provenance and generated-file hashes](PROVENANCE.json) record the original
archive checksums. The archives themselves are not required for recovery.

## Evidence boundary

Both original suites and the new full recovery runner were executed during
integration. All 14 manifest-listed files matched their original SHA256 values;
all four generated outputs were recovered byte-for-byte. The serialized
positive certificate and both original word predicates passed.

This is reproducibility evidence, not independent mathematical review or Lean
verification. The compiler is not the complete word-equation decision backend.
False supplied assignments are not UNSAT certificates, and a bounded search
failure is never an unrestricted NO. The full subtype problem remains open.
