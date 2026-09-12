# Subtail source-visit lower-bound reproduction

**This package does not solve general subtype entailment.** It contains a written derivation and finite checks of source-visit lower bounds for Subtail's existing modular synchronization family (C046), relevant to Q004.

Base repository commit: `f85ba3af769041349979e6130f1e2bc109b07c91`.

Read `RESEARCH_NOTE.md` for complete definitions, proofs, sources, and limitations. The construction itself is existing repository work. No independent mathematical review or Lean verification was performed, and no repository files were modified.

## Reproduce

Python 3.9+ and the standard library suffice. The recorded execution used Python 3.13.5.

```sh
python3 source_visit_bound.py --self-test --output replay.json
python3 -c "import json; assert json.load(open('results.json')) == json.load(open('replay.json')); print('Exact replay: PASS')"
```

Describe one member of this already-decidable family without enumerating its witness:

```sh
python3 source_visit_bound.py --periods 2 3 5
```

The latter prints 14 states, minimum source visits 62, and shortest witness length 93. It applies only to the explicitly constructed family, not an arbitrary supplied automaton or constraint system.

## Files

- `RESEARCH_NOTE.md`: exact all-length proof and scope.
- `source_visit_bound.py`: separate family implementation, direct and reverse predicates, finite tests, and per-flag certificate construction.
- `results.json`: complete deterministic run, including individually verified live-flag certificates.
- `run.log`: compact console output.
- `SHA256SUMS`: integrity hashes for the above files and this README.

The asymptotic source count uses the prime-number theorem as stated in the note. Computed finite samples are not evidence by themselves for that asymptotic or for a general decision procedure. Very large witness lengths in the output are arithmetic formulas, not claims to have enumerated or materialized those words.
