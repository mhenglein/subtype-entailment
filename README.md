# Subtail

Collaborative research on **Problem 1.7: subtype entailment over bottom and binary product**, with possibly infinite trees. The repository now contains a complete Lean-checked decision theorem for this problem; see [C081](research/claims.md#c081).

## Start here

Read these in order when joining or resuming the project:

1. **[Problem](research/problem.md)** — exact statement and notation.
2. **[Current research state](STATE.md)** — compressed scientific memory: established results, evidence, dead ends, and the current frontier.
3. **[Research tracker](research/README.md)** — generated status of every approach and its next step.
4. **[Claims and evidence](research/claims.md)** — exact scope and proof/evidence level of individual results.
5. **[Agent operating rules](AGENTS.md)** — how humans and agents coordinate without losing or duplicating research.

For a focused agent handoff, retrieve an exact record without rewriting files:

```sh
python3 scripts/research_index.py --lookup Q003
```

Use A/C/E/Q IDs. The response is JSON with source paths and the record's content.
Read [the attempt template](templates/attempt.md) before starting a new attempt.

Other useful entry points:

| You want to… | Go to |
|---|---|
| Choose a research direction | [Research plan](research/PLAN.md) |
| Inspect important open hypotheses | [Conjecture registry](research/conjectures/README.md) |
| Reproduce a result or find its limits | [Experiment index](experiments/README.md) |
| Build the checked word lemmas | [Lean core](lean/README.md) |
| Join the work or hand it off | [Contribution guide](CONTRIBUTING.md) |
| Read the initial analysis | [September 4 review](REVIEW.md) |
| Find the original memo | [Sources and provenance](papers/README.md) |

## Research operating model

The repository is the canonical collective memory. Individual chats, notebooks, and issue discussions are disposable working context unless their reusable conclusions are integrated back into the repo.

```text
problem
  ↓
STATE.md ── current scientific frontier
  ↓
scoped investigation / GitHub issue
  ↓
agent or human branch/worktree
  ↓
proof · experiment · counterexample · failure
  ↓
independent review where material
  ↓
claims / approach history / conjecture registry
  ↓
STATE.md updated
  ↺
```

Exploration can be massively parallel. Integration is deliberately serialized through evidence and review.

## Stable research objects

- **A IDs** — approaches/workstreams with dated attempt histories.
- **C IDs** — mathematical claims and evidence status.
- **E IDs** — reproducible experiments.
- **Q IDs** — important open conjectures/hypotheses.

Current approach metadata lives in `research/approaches.json`; `research/README.md` is generated from it. Failed and inconclusive attempts remain in the record so another agent does not rediscover the same dead end.

## Current technical position

`Subtail.EntailmentDecision.entailsCheck_correct` proves that a total executable
Boolean decides entailment for every finite constraint list and query built
from variables, bottom and binary product. Valuations range over arbitrary,
possibly infinite trees. The theorem assumes no satisfiability, finite-model,
regular-model, witness-bound or caller-supplied absorption condition.

The proof composes finite-expression normalization, exact summary construction,
the absorbing infinite/terminal split, and both checked branch decisions.
Pinned Lean build, kernel replay, runtime dependency audits and independent
semantic readback support the result. [Complete argument and validation](notes/2026-09-19-entailment-decision.md).
Native tests are supplementary finite evidence; the exhaustive backend can
be impractical even for simple inputs, and test timeouts remain UNKNOWN.

The candidate explicit `U/F` bound in [C080](research/claims.md#c080) remains
unproved and is not needed for this decision. [STATE.md](STATE.md) separates
the checked theorem, ordinary corollaries, performance limits and prior failed
attempts. No complexity, novelty or human peer-review claim follows from CI.

## Run the checks

Python 3.9 or newer; no third-party packages required for the core suite.

```sh
python3 scripts/research_index.py --check
python3 experiments/run_experiments.py
python3 experiments/check_topfree_bridge.py
python3 experiments/check_context_cuts.py
python3 experiments/search_budgets.py --replay-stored
python3 experiments/check_boundary_slices.py
python3 experiments/check_summary_bridge.py
python3 experiments/check_summary_bridge_audit.py
python3 experiments/check_minimal_structure.py
python3 experiments/shortest_witnesses.py
python3 experiments/trim_budget_example.py
```

For later continuation work, consult `experiments/README.md` for the exact registered commands and evidence. With Lean 4.33.1 and Lake installed, also run:

```sh
python3 scripts/check_lean.py
```

GitHub Actions validates the tracker and local document paths and replays the checks wired into CI. Passing CI is evidence of reproducibility, not a mathematical proof.

## Repository map

```text
STATE.md                 Canonical compressed research state and frontier
AGENTS.md                Operating rules for human/agent researchers
research/problem.md      Exact problem and notation
research/approaches.json Canonical workstream status/ownership metadata
research/approaches/     Dated attempt histories, including failures
research/claims.md       Exact mathematical claims and evidence status
research/conjectures/    Stable Q-ID hypotheses shared across investigations
research/PLAN.md         Longer-horizon research programme
experiments/             Executable checks and experiment registry
lean/                    Checked entailment decision and supporting word lemmas
results/                 Compact reproducible outputs
papers/                  Unchanged source documents and provenance
notes/                   Detailed audits and chronological working analysis
templates/               Research-note and attempt templates
scripts/                 Tracker generation and repository checks
.github/                 Issue forms, PR template, and CI
```

Keep scratch files in ignored `tmp/`. Use the [contribution guide](CONTRIBUTING.md) for the complete handoff and review workflow.