# Collaborating on Subtail

Start with [the problem](research/problem.md), [current shared memory](STATE.md), [the research tracker](research/README.md), and [claims and evidence](research/claims.md). The September 4 [review](REVIEW.md) is the initial snapshot; the tracker records later progress.

The [research plan](research/PLAN.md) gives current priorities first and preserves
the original programme as history; use `STATE.md` and the conjecture records
for the current mathematical frontier. The
[Lean workstream](research/approaches/A018.md) records completed local proofs
and the remaining obligations. Its [build guide](lean/README.md) explains the
pinned toolchain and validation commands.

For a new route, reuse or complete [the proof-outline template](templates/proof-outline.md)
before substantial supporting implementation or formalization. Exact definitions
and named gaps are required from the beginning; a cheap counterexample search
need not wait for a complete outline. New Lean work needs a specific semantic
risk, disputed implication, or stable critical dependency to resolve; existing
checks remain maintained. See [the operating rules](AGENTS.md).

## Pick and claim work

1. Find an untried approach or a useful next step in a tried record. Read its history before repeating work.
2. Read the [active tasks and owned files](STATE.md#active-work-and-file-ownership), relevant issues and their recent comments. Before nontrivial work, post a scoped claim with the approach, question, base commit, branch and exact write paths. Use an existing issue when it fits; coordinate shared paths in [#37](https://github.com/mhenglein/subtail/issues/37).
3. Agree ownership, then update `research/approaches.json` to `active` through the integrator. Work on a named branch in a separate worktree. Only the owner-authorized integrator publishes reviewed and checked contributions to `main`; a pull request is optional when direct integration is authorized.
4. Post progress, blockers and handoffs in the owning issue. Release paths explicitly when work completes or stops, and update the active-work record. A queued task or an old timestamp does not reserve or release files.

Names in the tracker identify current owners. Historical authors belong in dated attempt entries. An unassigned record is not a commitment by any collaborator.

Retrieve a record without changing files:

```sh
python3 scripts/research_index.py --lookup Q003
python3 scripts/research_index.py --lookup C045
python3 scripts/research_index.py --lookup A017
```

The JSON contains the canonical source and content; A records also include
current execution metadata. Follow linked proof and experiment records for
exact evidence. The lookup is navigation, not a verifier of mathematical claims.

## Record every attempt

Append a dated entry to the approach record, including unsuccessful or inconclusive attempts. Use [the attempt template](templates/attempt.md). Include the exact statement, assumptions, proof or command, result, evidence, and what the result does not show.

- New approaches get the next unused A ID and a record in `research/approaches/`.
- Claims use C IDs in `research/claims.md`. Keep mathematical status separate from activity status.
- Experiments use E IDs in `experiments/README.md`. Record seeds, input coverage, state or length caps, output paths, and the commit used.
- Add original sources to `papers/` without rewriting them; record source, date, and checksum.
- Keep larger explorations and dated working notes in `notes/`. Link them from the relevant approach.

Do not erase a failed argument after finding a repair. State what failed and link to the replacement. A new run should record whether it repeats an existing experiment or tests a new hypothesis.

For lookup, give each C/E record its lowercase explicit ID anchor followed by
a `###` heading. Use `####` for subsections inside the record; a `##` heading
ends the record group. Q filenames and first headings must share the same ID.
Keep the full proof in its linked note when the central entry is only an index.

## Finish or pause a session

Update the central registry with the current status, outcome, owner, evidence, and one next step. If blocked, say exactly what is missing. If stopped after a limit, record UNKNOWN and the limit. If a claim changed, update its individual ledger and Q lookup entries in the same commit, correct known original entry points, and record which dependent uses were checked or remain unaudited.

Issues are for discussion and coordination. Approach metadata is the source for current research status; evidence files establish what was actually done. Do not infer a proof from a closed issue or a passing test.

## Verify a contribution

Run from the repository root with Python 3.9 or newer:

```sh
python3 scripts/research_index.py
python3 scripts/research_index.py --check
python3 -m unittest discover -s scripts -p 'test_research_index.py'
git diff --check
```

The first command rebuilds the dashboard from the registry and conjecture records.
CI checks that it is current, referenced files exist, and the results included
in its workflow reproduce. The checker also rejects unregistered A/C/E/Q
references, duplicate record IDs, and broken explicit ID anchors. It does not
validate web URLs, other heading anchors, or mathematical claims.

For organization-only changes, the checks above are enough. If the border checker or its experiment suite changes, also run `python3 experiments/run_experiments.py`. Run the experiment commands relevant to the changed files; see the
[experiment index](experiments/README.md). For Lean changes, run
`python3 scripts/check_lean.py` with Lean 4.33.1 installed. This builds the
proofs, replays compiled declarations, audits axioms, and checks agreement
with Python. It rejects unexpected axioms in the named dependency closures.

Separate implementation checks, ordinary mathematical review, and formal verification. For a new theorem, ask a reviewer to check the argument independently, with exact construction definitions, quantifiers, imported theorem hypotheses, and both directions of any claimed reduction. For a
new witness or counterexample, provide a small input and an independent
checker where possible. State whether a result has a written proof, a Lean
proof, or only bounded evidence. A binary formalization must not be described
as covering every finite alphabet. Keep every unproved hypothesis explicit.

## File ownership

| Material | Canonical location |
|---|---|
| Current approach status, owner, next step | `research/approaches.json` |
| Current scientific frontier and route overview | `STATE.md` |
| Current research priorities and historical programme | `research/PLAN.md` |
| Exact open hypotheses, assumptions, and discriminating tests | `research/conjectures/Qxxx.md` |
| Readable dashboard | Generated `research/README.md` |
| Dated successes, failures, and inconclusive attempts | `research/approaches/Axxx.md` |
| Exact claims and mathematical status | `research/claims.md` |
| Experiment commands and coverage | `experiments/README.md` |
| Executable checks | `experiments/` |
| Lean definitions and proofs | `lean/` |
| Compact reproducible outputs | `results/` |
| Sources and provenance | `papers/` |
| Working analysis | `notes/` |

Share access through the private repository's collaborator settings. Adding an issue or naming an owner does not grant access.
