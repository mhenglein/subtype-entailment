# Subtail

Collaborative research on **Problem 1.7: subtype entailment over bottom and binary product**, with possibly infinite trees. The unrestricted problem remains open.

## Start here

Read these in order when joining or resuming the project:

1. **[Problem](research/problem.md)** — exact statement and notation.
2. **[Current research state](STATE.md)** — compressed scientific memory: established results, evidence, dead ends, and the current frontier.
3. **[Research tracker](research/README.md)** — generated status of every approach and its next step.
4. **[Claims and evidence](research/claims.md)** — exact scope and proof/evidence level of individual results.
5. **[Agent operating rules](AGENTS.md)** — how humans and agents coordinate without losing or duplicating research.

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

The Lean core proves the binary witness and budget predicates, stronger truncation rules, and an exact decision for at most two automaton states. Its general finite-budget decision theorem still assumes the missing bound. Python constructs actual summary instances from normalized subtype constraints and validates regular countermodels for supplied paths.

Later work proves an exact three-state bound, a family with `B=2k-4`, actual summary absorption, and decision results for important terminal subclasses. The terminal-final branch can realize arbitrary finite abstract flags; a genuine subtype instance has a nonregular terminal separating language. Exact Presburger skeleton formulas and a complete flat-terminal cover now exist, together with a complete normalized four-state terminal census.

The unrestricted problem, a general computable witness/skeleton bound, and the full formal subtype reduction remain open. The live frontier is summarized in **[STATE.md](STATE.md)**. Newer written proofs are not automatically Lean-checked; consult the [claims ledger](research/claims.md) for exact status.

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
lean/                    Checked binary word lemmas and conditional framework
results/                 Compact reproducible outputs
papers/                  Unchanged source documents and provenance
notes/                   Detailed audits and chronological working analysis
templates/               Research-note and attempt templates
scripts/                 Tracker generation and repository checks
.github/                 Issue forms, PR template, and CI
```

Keep scratch files in ignored `tmp/`. Use the [contribution guide](CONTRIBUTING.md) for the complete handoff and review workflow.