# Subtail

Private research workspace for the subtype entailment problem over bottom and binary product, particularly Problem 1.7 of the August 31, 2026 memo.

Start with [the review and research plan](REVIEW.md), then see [open questions](QUESTIONS.md).

This work reviews Problem 1.7 of the supplied `sep-topfree.pdf`. It does not solve the problem.

Run the independent experiments:

```
python3 experiments/run_experiments.py
```

- `experiments/border_lab.py`: exact finite-word predicates, N/S automata, and truncation criteria.
- `experiments/run_experiments.py`: deterministic cross-checks and explicit counterexample families.
- `results/independent-checks.json`: generated counts and exact examples.
- [papers/](papers/README.md): original papers and source provenance.
- [notes/](notes/README.md): proof audits, literature findings, and research notes.
- [templates/](templates/): a template for new research notes and experiments.
- `tmp/`: ignored local scratch files, including extracted PDF text.

## Working conventions

Keep source papers unchanged. Add dated notes that link to the exact source theorem or page. Distinguish proved statements, conjectures, refuted claims, and bounded experimental evidence.

Commit reproducible scripts and compact result files together. Record the seed, command, and search limits. A search limit means UNKNOWN, never NO. Use branches for new research directions and GitHub issues for discussions that need follow-up.

No third-party Python packages are needed. Python 3.9 or newer is sufficient.

The memo's original `analysis-2026` code was not supplied. This implementation was written independently.
