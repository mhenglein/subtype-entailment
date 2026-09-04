# Collaborating on Subtail

Start with [the problem](research/problem.md), [the research tracker](research/README.md), and [claims and evidence](research/claims.md). The September 4 [review](REVIEW.md) is the initial snapshot; the tracker records later progress.

## Pick and claim work

1. Find an untried approach or a useful next step in a tried record. Read its history before repeating work.
2. Open a GitHub issue using the research template, or join the linked discussion. Name the approach ID and the exact question.
3. Agree on an owner, then update `research/approaches.json` to `active`. Use a branch and pull request so others can see the work.

Names in the tracker identify current owners. Historical authors belong in dated attempt entries. An unassigned record is not a commitment by any collaborator.

## Record every attempt

Append a dated entry to the approach record, including unsuccessful or inconclusive attempts. Use [the attempt template](templates/attempt.md). Include the exact statement, assumptions, proof or command, result, evidence, and what the result does not show.

- New approaches get the next unused A ID and a record in `research/approaches/`.
- Claims use C IDs in `research/claims.md`. Keep mathematical status separate from activity status.
- Experiments use E IDs in `experiments/README.md`. Record seeds, input coverage, state or length caps, output paths, and the commit used.
- Add original sources to `papers/` without rewriting them; record source, date, and checksum.
- Keep larger explorations and dated working notes in `notes/`. Link them from the relevant approach.

Do not erase a failed argument after finding a repair. State what failed and link to the replacement. A new run should record whether it repeats an existing experiment or tests a new hypothesis.

## Finish or pause a session

Update the central registry with the current status, outcome, owner, evidence, and one next step. If blocked, say exactly what is missing. If stopped after a limit, record UNKNOWN and the limit. If a claim changed, update its ledger entry in the same pull request.

Issues are for discussion and coordination. Approach metadata is the source for current research status; evidence files establish what was actually done. Do not infer a proof from a closed issue or a passing test.

## Verify a contribution

Run from the repository root with Python 3.9 or newer:

```sh
python3 scripts/research_index.py
python3 scripts/research_index.py --check
python3 experiments/run_experiments.py
git diff --check
```

The first command rebuilds the dashboard from the registry. CI checks that it is current, all referenced files exist, and the recorded experiment results reproduce. Local path checking does not validate web URLs, Markdown anchors, or mathematical claims.

For a new theorem, ask a reviewer to check the argument independently. For a new witness or counterexample, provide a small input and an independent checker where possible. Current proofs are written arguments, not proof-assistant formalizations.

## File ownership

| Material | Canonical location |
|---|---|
| Current approach status, owner, next step | `research/approaches.json` |
| Readable dashboard | Generated `research/README.md` |
| Dated successes, failures, and inconclusive attempts | `research/approaches/Axxx.md` |
| Exact claims and mathematical status | `research/claims.md` |
| Experiment commands and coverage | `experiments/README.md` |
| Executable checks | `experiments/` |
| Compact reproducible outputs | `results/` |
| Sources and provenance | `papers/` |
| Working analysis | `notes/` |

Share access through the private repository's collaborator settings. Adding an issue or naming an owner does not grant access.
