# Subtail continuation: closed-source-walk counter lifts

A proof and standalone Python reproduction package extending supplied source-simple power schemes to supplied closed source walks with repeated state labels.

**This is not an unrestricted subtype-entailment solver.** The implementation compiles an exact existential word-equation formula, using the repository's C071 primitive. It does not execute the complete external word-equation decision algorithm. No Lean verification or independent mathematical review is claimed.

## Read

- `RESEARCH_NOTE.md`: definitions, new lemmas, compilation proof, imported theorem, experiments, exact remaining completeness gap.
- `ROUTE_OUTLINE.md`: the end-to-end route and what is still unproved.
- `checks.json`: deterministic recorded results and their interpretation.

## Reproduce

Use Python 3.10 or newer. No third-party packages are required.

```sh
python3 closed_walk_lift.py --compile-example formula-replay.json
python3 check_closed_walk_lift.py --output checks-replay.json
python3 verify_example.py
```

On the checked version, `checks-replay.json` is byte-identical to `checks.json`, and `formula-replay.json` is byte-identical to `formula-example.json`.

`verify_example.py` evaluates the saved explicit word assignment against the serialized Boolean formula and its DFA constraints, and independently checks the resulting original witness word. It does not search for a model.

## Files

- `closed_walk_lift.py`: automata, exact counter lift, power guards, two word predicates, explicit formula compiler/evaluator.
- `check_closed_walk_lift.py`: seeded regressions and grounded-assignment checks.
- `formula-example.json`: an expanded formula, with no unresolved power or universal-comparison operators.
- `witness-model.json`: one satisfying assignment for that formula, yielding `1010110`.
- `verify_example.py`: replays that positive certificate.
- `checks.json`: saved check counts, limits, examples, and evidence status.
- `SHA256SUMS`: hashes of delivered files other than the checksum manifest itself.

## Result and limit

For an unknown base whose supplied source walk has d arrivals, the automaton product with a source-arrival counter modulo d turns every source occurrence's rotation into a first-return loop. This makes the existing boundary formula applicable. Counters are phase-local; shared word variables remain shared.

Decidability and a PSPACE upper bound follow for a **supplied finite scheme**, at the written-proof level and using the precisely cited external theorem. A computable complete bound on scheme complexity for arbitrary instances remains unproved.

Work is pinned to repository commit `52d5270342b27aee3cad10e1b2d0ac7d9307a580`. No remote files were changed. False assignments in the tests are not UNSAT certificates. Search limits are never used as an unrestricted NO answer.
