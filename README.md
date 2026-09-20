# Subtail

Collaborative research on **Problem 1.7: subtype entailment over bottom and binary product**, with possibly infinite trees. The repository now contains a complete Lean-checked decision theorem for this problem; see [C081](research/claims.md#c081).

The [completion checklist](research/COMPLETION.md) separates release requirements
from the remaining performance, complexity and extension research.

**Before starting agent work:** read the [active tasks and owned files](STATE.md#active-work-and-file-ownership),
the [research tracker](research/README.md#active-work), and the latest
[coordination comments](https://github.com/mhenglein/subtail/issues/37).
Claim a disjoint scope before editing; queued tasks are not file reservations.

## The result

Given any finite list of constraints and a query built from variables, bottom
and one covariant binary product, a total executable Boolean decides whether
every satisfying valuation also satisfies the query. Values may be infinite
and nonregular. No satisfiability or witness-bound assumption is supplied by
the caller.

```text
Subtail.EntailmentDecision.entailsCheck G s t = true
    iff every arbitrary-tree model of G satisfies s <= t.
```

Read the [ordinary mathematical paper](paper/manuscript.md), its
[PDF](output/pdf/subtail-paper.pdf), the [proof dependency map](paper/dependency-map.md)
and the [paper-to-Lean map](paper/lean-map.md). The terminal-decision construction
is explained in Sections 5–9, including coverage and reconstruction of the
whole path-query conjunction. [The source module](lean/Subtail/EntailmentDecision.lean)
contains the final composition.
The revised paper uses conventional theorem numbering and a full bibliography,
integrates the Henglein–Rehof lineage, and gives ordinary proofs of effective
regular countermodels and the constant-free PSPACE transfer. Source pins and
review records are kept in the artifact guide, outside the manuscript.
Section 13 now gives the full finite-tree proof, including the cycle test,
finite canonical replacements and worked differences between the two domains.
[Current manuscript acceptance and review scope](notes/2026-09-20-publication-acceptance.md).

**Small example.** From `x <= y`, covariance gives
`x × bottom <= y × bottom`. The reverse query fails: set `x = bottom` and
`y = bottom × bottom`. At address `0`, the reverse query's left side has a
product node and its right side has bottom. The paper also gives a regular
infinite countermodel and examples of the terminal first-return construction.

**Limits.** This theorem has no explicit top constructor, multiple labelled
constructors or contravariant function type. Finite-tree entailment has a
separate [unconditional checked decision](research/claims.md#c085). The complete fallback can be very slow.
The proved implementation now completes all 38 fixed benchmark inputs,
including all seven raw-backend probes, under the matched 20-second cap.
The deeper suite completes 19/19. Separate empty-constraint raw probes with
four and five variables now finish in 1.221s and 7.139s; six variables
still return `UNKNOWN`.
[Exact proof, matched measurements and limits](notes/2026-09-20-raw-summary-readback.md).
A timeout remains `UNKNOWN`. Qualitative decidability does not establish the old C080 numerical
bounds, a complexity class, or novelty. The [post-C081 programme](research/POST_C081.md)
tracks these separate questions. Author names and affiliations are placeholders;
licensing is pending. The paper is a research draft, not a peer-reviewed publication.

## Try the solver

With the pinned Lean toolchain on PATH, build the solver once before timing queries:

```sh
(cd lean && lake build +Subtail.EntailmentPrepared)
python3 scripts/subtail.py examples/entailment/premise.json --timeout 20
python3 scripts/subtail.py examples/entailment/reverse.json --timeout 20
```

Input is JSON with `variables`, a list of `constraints`, and one `query`.
An inequality is `[left,right]`. An expression is a variable name, `"bottom"`,
or `{"prod":[left,right]}`. The command returns ENTAILED, NOT_ENTAILED, or
UNKNOWN on a resource limit. It materializes the five primitive transition
relations once, then uses proved positive closure and cached exact separation checks, then the complete Lean decision when those checks are
inconclusive. The raw fallback reuses exact relation and physical-state tables,
streams the exact cycle search and keeps the original terminal procedure. The CLI timeout includes any needed build and explanation work;
the benchmark measures queries after the initial build.

Negative answers trigger a complete countermodel search: without resource
limits it eventually returns a finite graph and a separating path (`[]` is
the root). Graphs can contain cycles and denote regular infinite trees. If
extraction runs out of time, `explanation_search` is UNKNOWN and the completed
Lean decision remains NOT_ENTAILED. The search strategy and its ordinary proof
are [documented separately](notes/2026-09-20-regular-countermodels.md).

You can independently check a supplied graph without running Lean:

```sh
python3 scripts/subtail.py examples/entailment/zero-spine.json \
  --check-model examples/entailment/zero-spine-model.json
```

To check the finite graph with Lean too, use `--verify-certificate`:

```sh
(cd lean && lake build +Subtail.EntailmentFast +Subtail.RegularTreeCertificate)
python3 scripts/subtail.py examples/countermodels/alternating-spine.json \
  --timeout 60 --verify-certificate
```

The alternating-spine example requires `x = bottom × y` and `y = x × bottom`.
It returns a cyclic countermodel to `x <= bottom × bottom`, separated at `[1]`.
`certificate_verification: VERIFIED` means Lean accepted the graph against the
emitted original expressions. JSON parsing, source emission and extraction
remain ordinary Python; this is not a Lean-verified extractor. A verification
timeout is reported separately. [Certificate proof and validation](notes/2026-09-20-regular-countermodels.md);
[solver proof and performance limits](notes/2026-09-20-fast-summary.md).

## Finite-tree mode

[C085](research/claims.md#c085) gives a separate decision procedure for finite
bottom/product trees. First test for a consuming reverse-pop cycle. Such a
cycle forces an infinite branch, so there are no finite models and every
query is entailed. Otherwise the arbitrary-tree answer is also the finite-tree
answer; negative cases have finite canonical countermodels.

```sh
python3 scripts/subtail.py examples/finite-trees/forced-infinite.json --finite-trees
python3 scripts/subtail.py examples/finite-trees/reverse.json --finite-trees --verify-certificate
```

The first input has an infinite countermodel under arbitrary semantics, but
returns `ENTAILED` with reason `no_finite_model` under finite semantics. The
second returns a finite countermodel of height 1 and separator `[]`.

The complete reduction has an independently reviewed ordinary proof and an
unconditional Lean Boolean theorem:
`FiniteTreeDecision.entailsCheck G s t = true ↔ FiniteExprEntails G s t`.
The executable cycle classifier now supplies the obstruction or length bound
used by the semantic proof. The CLI calls this checked function directly.
JSON parsing/emission and graph finiteness remain Python; C084 certificates
check arbitrary non-entailment. Resource limits stay UNKNOWN.
[Ordinary proof](notes/2026-09-20-finite-tree-reduction.md),
[checked construction and limits](notes/2026-09-20-finite-tree-decision-readback.md),
[reproduction evidence](results/finite-tree-decision.json).

```sh
python3 scripts/check_finite_tree_decision.py --output tmp/finite-tree-decision.json
```

## Bounds and research checkpoint

[C082](research/claims.md#c082) gives a checked explicit terminal witness bound.
It also records why the earlier concrete C080 weight estimate is false; the
original F alone remains open. The [input resource account](notes/2026-09-20-c081-input-complexity.md)
gives a very large explicit bound for a specified reference decision algorithm,
including normalization, summary tables, arithmetic and storage.
[C083](research/claims.md#c083) supplies an NL lower bound by directed
reachability. The full input-cost derivation and NL reduction are ordinary
mathematics; the terminal witness bound is Lean-checked. These do not give a tight
complexity class or bound the runtime of this native frontend.

The earlier reader checkpoint is
[`c081-research-2026-09-20`](https://github.com/mhenglein/subtail/tree/c081-research-2026-09-20),
at `29cda9a`, with all four main checks passing. Its paper explains the
qualitative C081 proof. Later quantitative, solver and standalone-paper revisions are separate
additive contributions; original proof source pins remain unchanged.
The revised standalone paper is preserved at
[`c081-paper-2026-09-20`](https://github.com/mhenglein/subtail/tree/c081-paper-2026-09-20).
Its [review record](notes/2026-09-20-paper-rewrite-readback.md) separates the
manuscript readback, literature comparison, PDF inspection and formal evidence.

## Reproduce the result

The mathematical source checkpoint is
[`c946d86`](https://github.com/mhenglein/subtail/commit/c946d86b9e65da2877e0df42c710abbdcb5a4037).
Its [verification record](notes/2026-09-19-entailment-decision.md) names exact
builds, kernel replay, semantic reviews and native checks. Use Lean **4.33.1**,
selected by `lean/lean-toolchain`, and Python 3.9 or newer for the core checks.

For the logged clean-build procedure, use pinned Python **3.13.14** and a
fresh clone with no `lean/.lake`, then run `python3 scripts/reproduce_release.py`.
The [clean reproduction record](notes/2026-09-20-clean-reproduction.md) gives
the exact checked revision and 18-step receipt, including optional modules,
kernel/runtime audits, CLI countermodels and finite/arbitrary/timeout cases.
Installed tools are reused; this does not claim a fresh OS installation.
Individual checks can also be run as follows:

```sh
git clone https://github.com/mhenglein/subtail.git
cd subtail
python3 scripts/check_lean.py
(cd lean && lake build +Subtail.ExpressionNormalizationAudit)
python3 scripts/check_entailment_decision.py
python3 experiments/check_entailment_decision.py --phase smoke --strict
(cd lean && lake build +Subtail.FiniteTreeDecision && lake env lean --run ../paper/example.lean)
python3 scripts/research_index.py --check
python3 paper/check.py
```

The Lean check builds the default library and replays its proofs in the kernel.
The [small executable example](paper/example.lean) prints `true` for a listed
premise and `false` for its reverse query.
It then prints `false` and `true` for the forced-spine query under arbitrary
and finite semantics. The finite theorem has its own [source and validation](notes/2026-09-20-finite-tree-decision-readback.md).
The declaration audit inspects the computational dependencies as well as theorem
axioms. The native smoke suite checks a small completed subset; it does not
claim that all diagnostic cases run quickly. For the full performance record,
run `python3 experiments/check_entailment_decision.py`; capped cases remain
`UNKNOWN`. More [experiment commands](experiments/README.md) cover the separate
proof branches and earlier investigations.

The paper's source/declaration check needs only Python. Building its PDF also
needs Pandoc 3.11 and Tectonic 0.17.0; see [paper reproduction](paper/README.md).
PDF generation and source-link checks do not repeat Lean verification.

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
| Read the final proof rather than discovery history | [Paper and dependency map](paper/README.md) |
| Check what may be new | [C081 literature review](notes/prior-work/c081-review-2026-09-19.md) |
| Check extension boundaries | [Regular/finite/top/variance study](notes/2026-09-19-post-c081-extensions.md) |

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

The old concrete weight estimate in [C080](research/claims.md#c080) is refuted;
its original F alone remains open. [C082](research/claims.md#c082) supplies a
separate corrected bound. Neither numerical estimate is needed by C081. [STATE.md](STATE.md) separates
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
research/POST_C081.md    Paper, complexity, performance and extension programme
paper/                  Ordinary final proof, declaration maps and PDF source
output/pdf/             Rendered paper, generated TeX and provenance manifest
experiments/             Executable checks and experiment registry
lean/                    Checked entailment decision and supporting word lemmas
results/                 Compact reproducible outputs
papers/                  Unchanged source documents and provenance
notes/                   Detailed audits and chronological working analysis
templates/               Research-note and attempt templates
scripts/                 Tracker generation and repository checks
.github/                 Issue forms, PR template, and CI
```

The paper and C081 verification record are the final-proof entry points.
Chronological notes and approach histories preserve failed and conditional
arguments; a historical statement is not automatically part of the final proof.
`CITATION.cff` contains provisional metadata. No license grant is implied for
the repository or supplied third-party papers.

Keep scratch files in ignored `tmp/`. Use the [contribution guide](CONTRIBUTING.md) for the complete handoff and review workflow.
