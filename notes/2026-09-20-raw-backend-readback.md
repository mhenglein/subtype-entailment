# Incremental raw backend: proof and validation readback

Session: raw-backend-20260920. A010/A018, C029/C081, #61/#37.
Base: `b02352efba0ceabec1c542da66e534bdc5675890`.
Proof/runtime checkpoint: `262f57ad031aef2307f6398875dea108413067b3`.
Status: native proof/CLI checks pass; benchmark and final integration pending.

## Exact mathematical result

`InfiniteDecisionLazy.infiniteWitnessCheckLazy_eq` states equality with
`InfiniteDecision.infiniteWitnessCheck` for every `Instance k`. There is no
absorption, reachability, satisfiability, witness bound or positive-answer
hypothesis. `infiniteWitnessCheckLazy_correct` keeps the existing `Absorbing I`
hypothesis when interpreting that Boolean as existence of an infinite witness.

`rawNormalizedEntailsCheckLazy_eq` preserves the same `summaryInstance C a b`,
then substitutes only the infinite-branch Boolean. Terminalization and
`TerminalDecisionLazy.terminalWitnessCheckLazy` are unchanged. Its semantic
correctness remains unconditional normalized arbitrary-tree entailment.
`EntailmentPrepared.afterPositive_eq` substitutes this equality into the final
fallback; its unchanged final theorem still covers all finite expressions and
arbitrary, possibly nonregular trees. No finite-tree endpoint changes.

The new runtime streams words through a structurally recursive exact-length
search and a finite increasing-length scan. It skips endpoints failing
necessary final/flag-column conditions. It tests initial safety before this
scan. The proof of that gate uses an actual safe prefix run and its zero cut;
it never treats endpoint safety as a substitute for prefix reachability.
The exact prefix monitor, cycle length bound and terminal promotion are retained.
[Full ordinary argument and failed ablation](2026-09-20-raw-backend.md).

## Checked evidence

All native commands run serially in the isolated wb-marcus worktree
`/home/marcus/workspaces/subtail-worktrees/raw-backend-20260920`, using Lean
4.33.1 (commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Python 3.13.14.
The inactive previous checkout's `.lake` cache was copied; actual builds and
kernel checks followed. No active build directory was shared.

At `262f57a`:

```sh
python3 scripts/check_infinite_lazy.py --cli --output tmp/infinite-lazy-audit.json
python3 scripts/check_lean.py
```

The first command builds the two affected modules, replays their imported
proofs through the kernel, and audits every named declaration in both sources:
39 closures, including 19 runtime definitions/types. Executable dependency
closures exclude `Classical.choice`; theorem closures use only standard allowed
axioms. Source scanning rejects unfinished or trusted replacement declarations.
This audit is separate from the ordinary semantics review.

Five actual CLI runs pass: reflexive and zero-variable positives, depth-six/eight
negatives with expected countermodels and separating paths, and a forced cap
returning UNKNOWN with exit two and `time_limit`. The CLI name/API is unchanged.
The default core passes build/kernel replay, 10,160 witness and boundary checks,
60,960 checks of each budget predicate, 511 suffix checks and 33 two-state
comparisons, with zero failures. Those checks are finite regression evidence.

Local checks pass: 77 focused Python tests; research index validation; paper
source/map/literal checks. The paper guard did not build or replay Lean and
is not presented as formal evidence. No new PDF was needed.

## Review scope and corrections

A separate read-only source reviewer checked `262f57a`: generic enumeration
identities, the initial zero-cut gate, its exact quantifiers, retained absorption
on the semantic theorem, raw and prepared composition, runtime order and audit
coverage. No blocker was found. This review inspected the proposed argument
and parent-provided diagnostics; it was not blind rediscovery, an independent
native timing run, or human peer review. The reviewer made no source edits.

The first draft `f09a45b` needed explicit function-composition simplification
and a Boolean-conjunction elaboration correction. Statements and hypotheses
were unchanged. An initial tracker update supplied an integer issue ID where
the existing schema requires a URL; validation caught it and the URL was fixed.
The streaming-only ablation remains preserved: it resolves three of the five
raw timeouts but does not finish the two unsafe-initial positive instances.

## Limits and next question

An exhaustive negative cycle search may still inspect exponentially many words.
The prefix monitor and promoted terminal query can also be expensive. No
improved worst-case complexity, memory bound, general speedup, new signature,
C080 bound or novelty result follows. A cap remains UNKNOWN. Licensing and
authorship remain as deferred by the owner. The next performance experiment
should force the terminal-promotion branch; formal countermodel production
and explicit-top separation remain separate research questions.
