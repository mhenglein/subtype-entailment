# Subtail

Collaborative research on **Problem 1.7: subtype entailment over bottom and binary product**, with possibly infinite trees. The problem remains open.

## Start here

| You want to… | Go to |
|---|---|
| Understand the problem and notation | [Problem statement](research/problem.md) |
| Choose the next research direction | **[Research plan: eleven angles](research/PLAN.md)** |
| See what we tried, what failed, and what is next | **[Research tracker](research/README.md)** |
| Check exactly what a result establishes | [Claims and evidence](research/claims.md) |
| Reproduce a result or find its limits | [Experiment index](experiments/README.md) |
| Join the work or hand it off | [Contribution guide](CONTRIBUTING.md) |
| Read the initial analysis | [September 4 review](REVIEW.md) |
| Find the original memo | [Sources and provenance](papers/README.md) |

## How the research is tracked

Each approach has a stable **A ID**, a current status, an owner when active, and a dated history of attempts. Failed and inconclusive attempts stay in the record. Claims have **C IDs** and separate mathematical statuses. Experiments have **E IDs**, commands, and evidence links.

The [tracker](research/README.md) is generated from [one registry](research/approaches.json), so status is updated in one place. GitHub issues hold discussions linked to those records. See the [issues](https://github.com/mhenglein/subtail/issues) or [start a discussion using a template](https://github.com/mhenglein/subtail/issues/new/choose).

The original memo's `analysis-2026` code is still pending. The current scripts are an independent implementation, and their results must not be confused with the memo's full census.

## Run the checks

Python 3.9 or newer; no third-party packages required.

```sh
python3 scripts/research_index.py --check
python3 experiments/run_experiments.py
```

GitHub Actions validates the tracker and local document paths, reruns the experiments, and checks the saved results. Passing tests do not establish a mathematical proof.

## Repository map

```text
research/     Current tracker, claims, problem definition, and approach histories
experiments/  Executable checks and experiment index
results/      Compact, reproducible output files
papers/       Unchanged source documents and provenance
notes/        Detailed audits and working analysis
templates/    Research-note and attempt templates
scripts/      Tracker generation and repository checks
.github/      Issue forms, pull request template, and automated checks
```

Keep scratch files in ignored `tmp/`. Use [the contribution guide](CONTRIBUTING.md) for the complete update and review workflow.
