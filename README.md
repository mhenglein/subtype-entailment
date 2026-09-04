# Subtail

Collaborative research on **Problem 1.7: subtype entailment over bottom and binary product**, with possibly infinite trees. The problem remains open.

## Start here

| You want to… | Go to |
|---|---|
| Read the latest results and remaining terminal-path problem | **[September 4 continuation: C021-C029 and E016-E020](research/CONTINUATION.md)** |
| Understand the problem and notation | [Problem statement](research/problem.md) |
| Choose the next research direction | **[Research plan: eleven angles](research/PLAN.md)** |
| See what we tried, what failed, and what is next | **[Research tracker](research/README.md)** |
| Check exactly what a result establishes | [Claims and evidence](research/claims.md) |
| Reproduce a result or find its limits | [Experiment index](experiments/README.md) |
| Build the checked word lemmas | [Lean core](lean/README.md) |
| Join the work or hand it off | [Contribution guide](CONTRIBUTING.md) |
| Read the initial analysis | [September 4 review](REVIEW.md) |
| Find the original memo | [Sources and provenance](papers/README.md) |

## How the research is tracked

Each approach has a stable **A ID**, a current status, an owner when active, and a dated history of attempts. Failed and inconclusive attempts stay in the record. Claims have **C IDs** and separate mathematical statuses. Experiments have **E IDs**, commands, and evidence links.

The [tracker](research/README.md) is generated from [one registry](research/approaches.json), so status is updated in one place. GitHub issues hold discussions linked to those records. See the [issues](https://github.com/mhenglein/subtail/issues) or [start a discussion using a template](https://github.com/mhenglein/subtail/issues/new/choose).

The original memo's `analysis-2026` code is still pending. The current scripts are an independent implementation, and their results must not be confused with the memo's full census.

The Lean core proves the binary witness and budget predicates, stronger
truncation rules, and an exact decision for at most two automaton states.
Its general finite-budget decision theorem still assumes the missing bound.
Python constructs actual summary instances from normalized subtype constraints
and validates regular countermodels for supplied paths. The full problem,
computable bound, and formal subtype reduction remain open.
See the [claims ledger](research/claims.md) for the exact scope of each result.

The later [written continuation](research/CONTINUATION.md) proves the exact
three-state bound, a family with B=2k-4, and actual summary absorption. The
[denial-aware continuation](notes/2026-09-04-denials-and-continuations.md)
removes the separate safety subset and decides the infinitely-extendable-
witness branch. Terminal safe witnesses with unbounded pre-final histories
remain unresolved. These new proofs are not Lean-checked; an infinite safe
continuation of a separating path is not the same as an infinite type tree.

## Run the checks

Python 3.9 or newer; no third-party packages required.

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

For the later continuation:

```sh
python3 experiments/check_budget_growth_family.py
python3 experiments/three_state_decision.py
python3 experiments/check_summary_absorption.py
python3 experiments/run_denial_continuation.py
```

With Lean 4.33.1 and Lake installed, also run:

```sh
python3 scripts/check_lean.py
```

GitHub Actions validates the tracker and local document paths, reruns the
original checks, and compares their saved results. The newer continuation
commands are not yet wired into that workflow. The Lean theorem statements
establish their specific implications; Python comparisons remain bounded evidence.

## Repository map

```text
research/     Current tracker, claims, problem definition, and approach histories
experiments/  Executable checks and experiment index
lean/         Checked binary word lemmas and conditional decision framework
results/      Compact, reproducible output files
papers/       Unchanged source documents and provenance
notes/        Detailed audits and working analysis
templates/    Research-note and attempt templates
scripts/      Tracker generation and repository checks
.github/      Issue forms, pull request template, and automated checks
```

Keep scratch files in ignored `tmp/`. Use [the contribution guide](CONTRIBUTING.md) for the complete update and review workflow.
