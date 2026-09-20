# Incremental raw backend: proof and validation readback

Session: raw-backend-20260920. A010/A018, C029/C081, #61/#37.
Base: `b02352efba0ceabec1c542da66e534bdc5675890`.
Proof/runtime checkpoint: `262f57ad031aef2307f6398875dea108413067b3`.
Status: proof, native regressions and matched benchmark pass; publication is recorded in #61/#37.

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

## Matched execution evidence

The independently authored harness was pushed as `76fb9eb`, inspected and
integrated with provenance as `471f973`. It owns no Lean implementation. At
`471f9730bf3b93ef71446f2e105f0743d4c3c3ef`, the parent ran:

```sh
python3 experiments/check_infinite_lazy.py --components --full38 --compare-baseline --timeout 20 --output tmp/infinite-lazy-matched.json --scratch tmp/infinite-lazy-matched
python3 experiments/check_infinite_lazy.py --stress-raw --timeout 20 --output tmp/infinite-lazy-stress.json --scratch tmp/infinite-lazy-stress
```

Each fixture uses the original fresh-process `lake env lean FILE` and `#eval`
protocol, after module building. Limits are 20 seconds wall/CPU, Linux 16 GiB
address space, one thread and a 32768 KiB Lean stack. These are uninstrumented
end-to-end query times, including process/import overhead. No peak-memory
improvement is claimed.

| Fixed original corpus | Baseline | Candidate |
|---|---:|---:|
| Raw backend | 2 PASS, 5 UNKNOWN | 7 PASS |
| Original expressions | 26 PASS | 26 PASS |
| Normalized guarded inputs | 5 PASS | 5 PASS |
| Total | 33 PASS, 5 UNKNOWN | 38 PASS |

The raw baseline is `TerminalDecisionLazy.rawNormalizedEntailsCheckLazy`; its
candidate is `InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy`. Those probes
bypass the frontend. The other rows compare the existing `EntailmentFast` and
`EntailmentPrepared` endpoints. No additional full-expression completion is
claimed. All seven new raw results take 0.669–0.719 seconds; the five former
UNKNOWNs reach their 20-second limits in the matched baseline. Completed
answers agree, and every candidate matches its original independent fixture
expectation. The combined report remains UNKNOWN because it retains those
five baseline timeouts; that status is not relabelled PASS in the raw receipt.

Fourteen abstract C029 probes compare both exact implementations. Twelve have
an independently stated expected Boolean or an existing named guard; two
nonabsorbing cases test Boolean equality only. Three probes are nonabsorbing:
the diagonally unsafe initial state also has a direct expected false answer
from necessary initial safety. Missing transitions, terminal-only witnesses,
ordered flags, pre-final loops and a positive stem/cycle are included. All
28 native evaluations pass. This is bounded evidence, not a new completeness
argument or a complete small-state census.

A separate fresh E058 component/generated run at `262f57a` retains all 19
prepared generated completions and six successful component vectors on
62 systems. Its length/two-checksum comparison keeps the documented collision
limitation; it is not an individual equality comparison of every vector bit.
The matched harness manifest is
`d5ed9de3af8e8b4fb5d1d088e1d7551a2e8bdc9617762c8bc0ed0057bdfbdb02`.
[All receipts, including failed ablations and remaining UNKNOWNs](../results/raw-backend.json).

The final uninstrumented larger probes complete n=3 in 1.220 seconds and leave
n=4 UNKNOWN at 20.008 seconds. They are separate from the fixed 38. The
corresponding diagnostic trace locates the n=4 cost in summary construction.
Every executed source hash in the accepted proof, matched, stress and prepared
receipts matches this contribution's final runtime source. Earlier traces
retain their original revisions and hashes.

## Review scope and corrections

A separate read-only source reviewer checked `262f57a`: generic enumeration
identities, the initial zero-cut gate, its exact quantifiers, retained absorption
on the semantic theorem, raw and prepared composition, runtime order and audit
coverage. No blocker was found. This review inspected the proposed argument
and parent-provided diagnostics; it was not blind rediscovery, an independent
native timing run, or human peer review. The reviewer made no source edits.

The same read-only reviewer separately checked the independent harness and CI
at `96306cd`: both fixture manifests, exact raw routing, marker protocol,
nonabsorbing/expected-value handling, caps, triggers, all required acceptance
checks and artifact retention. No blocker remained. The writer's original
`76fb9eb` contribution was released before integration. Neither worker ran the
accepted native benchmark; the parent ran it and verified the combined receipt.
The exact CI assertion block also passes against projections of actual native
rows. This validates the guard logic, not a separate performance run.

The first draft `f09a45b` needed explicit function-composition simplification
and a Boolean-conjunction elaboration correction. Statements and hypotheses
were unchanged. An initial tracker update supplied an integer issue ID where
the existing schema requires a URL; validation caught it and the URL was fixed.
Parent review of the independent harness caught an E058 result-marker mismatch,
a diagonally unsafe fixture incorrectly labelled absorbing, a missing decoder
hash, and candidate-only acceptance without an expected answer. These were
corrected before the native matched run; no failed native result was discarded.
The two cases lacking an independent expected Boolean now remain UNKNOWN in
candidate-only validation and are compared with the reference in the accepted
component run. The streaming-only ablation remains preserved: it resolves three of the five
raw timeouts but does not finish the two unsafe-initial positive instances.

## Limits and next question

An exhaustive negative cycle search may still inspect exponentially many words.
The prefix monitor and promoted terminal query can also be expensive. No
improved worst-case complexity, memory bound, general speedup, new signature,
C080 bound or novelty result follows. A cap remains UNKNOWN. Licensing and
authorship remain as deferred by the owner. A separate diagnostic at `262f57a` uses the same empty-constraint raw problem
with three or four normalized variables. The three-variable case completes in
1.471 seconds; the four-variable case is UNKNOWN at 20.008 seconds inside
summary construction, before cycle search. This trace uses the gated ablation
and `--run`, so it is not a matched final-endpoint timing. The independent
root-only/bottom valuation proves the expected negative answer in both cases.
The next measured target is this summary construction; a separate family
should also force terminal promotion. Formal countermodel production and
explicit-top separation remain separate research questions.
