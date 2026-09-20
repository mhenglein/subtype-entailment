# Cached raw summary: proof and validation readback

Session: raw-summary-20260920. A010/A018, C081, #62/#37.
Base: `5adaa2949ffaeab94c4b7687d12b8ca6bd84ee94`.
Current proof/runtime: `2233aeabc04e284e14761b6565d64ffcb62c5680`.
Status: proved runtime refinement; native acceptance and independent source review pass. Six-variable raw stress remains UNKNOWN.

## What is proved

For every normalized constraint list `C`, finite System `M`, cache for `M`,
and variable query `a,b`, `SummaryInstanceCached.summaryInstance_eq` states
literal equality to `SummaryAutomaton.summaryInstance C a b`, provided that
`M = systemOf C` and `CanonicalReachabilityFast.Correct M cache`.

These hypotheses are essential for arbitrary supplied runtime data. The public
`EntailmentPrepared.rawNormalizedEntailsCheck` prepares that data internally.
Its exact equality and semantic correctness have no extra assumptions:

```lean
EntailmentPrepared.rawNormalizedEntailsCheck C a b =
  InfiniteDecisionLazy.rawNormalizedEntailsCheckLazy C a b

EntailmentPrepared.rawNormalizedEntailsCheck C a b = true ↔ Entails C a b
```

`EntailmentPrepared.afterPositive` reuses its existing prepared machine and
cache in the complete fallback. Its equality theorem still applies to the
record produced by `prepare`, not to every arbitrary `Prepared` record. The
final original-expression `entailsCheck_correct` retains C081's arbitrary,
possibly infinite and nonregular prefix-closed-tree semantics.

## Construction and ordinary argument

The physical state space, subset-list order and state indices are unchanged.
Forward and reverse matrix rows give the initial subset pair. A transition
uses the existing cached pop/ balanced relation test for both components.
The reference `encode` indexes that exact ordered pair in the original list.
All successor subsets are filters of `finRange`, so the constructor is defined
even before cache correctness is assumed.

The backward path matrix at `(d,m)` means that a denied control `d` reaches
`m` in the reversed control graph. This is the reference danger predicate;
transposing it would change the construction. Cached control reachability
tests the original forced roots for satisfiability. These values determine
the same global and state-local Bad bits.

`stateTable` stores the original ordered physical-state list as a vector.
`stateTable_get` proves lookup at every `q` equals `decode q`. It is used for
Bad/final/flag construction, avoiding repeated enumeration inside the dense
flag matrix. Final bits still exclude forced members of the reverse subset.
The flag at `(p,q)` still records intersection of the forward subset at `p`
with the reverse subset at `q`. Empty subsets, ordered flags, diagonal pairs
and unreachable physical states are retained.

The existing cache correctness theorem replaces each cached Boolean with its
reference counterpart. Exact filter-list equalities then give identical
initial and transition indices. Componentwise equality proves the entire
`Instance` equal. Applying the unchanged infinite and terminal Booleans
proves the raw equality. `prepare_eq` removes the internal machine/cache
hypotheses for the public wrapper and frontend composition. This is an exact
runtime refinement, not a new soundness or completeness argument for C081.

All enumerations remain finite and effective. No reference decision, state
bound, signature, finite-tree endpoint or default import aggregator changes.
The [route and failed attempts](2026-09-20-raw-summary.md) precede this readback.

## Declaration map

| Ordinary obligation | Checked declaration |
|---|---|
| Physical-state lookup keeps the original ordering | `stateTable_get` |
| Every generated subset pair has a physical state | `initialPair_mem`, `advancePair_mem` |
| Initial subset lists and index are unchanged | `initialPair_eq`, `initial_eq` |
| Every transition index is unchanged | `advancePair_eq`, `advance_eq` |
| Correctly oriented danger and global SAT | `dangerCheck_eq`, `satCheck_eq` |
| All fields, including unreachable states and flags | `summaryInstance_eq` |
| Conditional same-cache raw composition | `rawWith_eq` |
| Unconditional prepared raw equality and semantics | `EntailmentPrepared.rawNormalizedEntailsCheck_eq`, `rawNormalizedEntailsCheck_correct` |
| Existing original-expression theorem | `EntailmentPrepared.afterPositive_eq`, `entailsCheck_eq`, `entailsCheck_correct` |

Unqualified names in the table belong to `Subtail.SummaryInstanceCached`.

## Native proof and interface checks

Native execution uses the isolated wb-marcus checkout
`/home/marcus/workspaces/subtail-worktrees/raw-summary-20260920`, Lean 4.33.1
(`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Python 3.13.14. An inactive
prior cache was copied; subsequent builds and kernel checks are actual runs.

At `2233aea`:

```sh
python3 scripts/check_summary_cached.py --cli --output tmp/raw-summary/table-audit.json
```

PASS: pinned module build, bundled kernel replay, 47 complete named declaration
closures, including 23 executable definitions/types without `Classical.choice`.
The source scan excludes unfinished or trusted replacement declarations.
The semantic proof may use the allowed standard axioms. Runtime definitions
are audited separately from erased proofs.

Five actual CLI checks pass: reflexive and zero-variable positives, depth-six
and depth-eight negatives with valid countermodels and expected zero paths,
and an enforced cap returning UNKNOWN/exit 2/`time_limit`. The CLI name, API,
parser, extractor and independent certificate boundary are unchanged.

## Diagnostic ablations

These use `lake env lean --run` to preserve partial phase output. They include
printing/forcing overhead and are not the final matched `#eval` benchmark.
Preparation is inside the timed cached-summary phase. Each process has a
20-second wall/CPU cap, Linux 16 GiB address space, one Lean thread and a
32768-KiB stack.

The summary marker forces the final-vector size; it is not an independent
measurement of every table cell. Exact full-field comparisons are a separate
acceptance check. Final claims use uninstrumented endpoint measurements.

| Constructor | Revision | Three variables | Four variables | Five variables | Six variables |
|---|---|---:|---:|---:|---:|
| Reference | `3d7ee86` | PASS, 1.371s | UNKNOWN, summary | Not run | Not run |
| Relation cache only | `3d7ee86` | PASS, 1.322s | UNKNOWN, summary | UNKNOWN, summary | UNKNOWN, summary |
| Relation and decoded-state caches | `2233aea` | PASS, 0.820s | PASS, 1.321s | PASS, 7.137s | UNKNOWN, summary |

All probes have empty constraints and query variable 0 below variable 1.
An independent finite countermodel assigns only a product root to variable 0
and bottom to all others, so their expected answer is false. These probes
directly exercise the raw backend and bypass frontend shortcuts.

The final diagnostic summary phases take 25ms, 303ms and 4111ms for three,
four and five variables; their subsequent infinite searches take 19ms, 199ms
and 2266ms. The six-variable timeout remains in summary construction. This
does not isolate its remaining subphase or imply a bound for other inputs.

The first vector-lookup proof draft at `c74323b` left an index-cast equality
after simplification. Adding definitional reduction (`rfl`) fixed elaboration
without changing a theorem statement, runtime definition or semantic premise.

## Matched acceptance and exact component evidence

The final uninstrumented run uses `66f545e8fb1cc3d0fd19bea2468f31a872c5bc46` on the same isolated wb-marcus
host. Both variants complete all **38/38** fixed cases. The seven candidate raw
calls take 0.669–0.719s. Raw baseline calls use the preceding
`InfiniteDecisionLazy` endpoint; nonraw baseline calls retain the E058
`EntailmentFast` renderer. Candidate raw calls use the new public prepared
endpoint. Both are checked against independent expected answers.

| Normalized variables, empty premises | Previous raw endpoint | Cached raw endpoint |
|---|---|---|
| 3 | PASS, 1.221s | PASS, 0.769s |
| 4 | UNKNOWN, 20.008s | PASS, 1.221s |
| 5 | UNKNOWN, 20.007s | PASS, 7.139s |
| 6 | UNKNOWN, 20.008s | UNKNOWN, 20.008s |

Every row has query `0 <= 1`, expected false, with the root/bottom countermodel
above. Wall/CPU caps remain 20 seconds per complete raw query; this table uses
`#eval` without diagnostic phase markers. Larger-variable completion is only
claimed for these displayed inputs. Six-variable diagnostic output locates the
remaining timeout in construction, without distinguishing its subphase.

At `8c42c7a3d09bb9e6b466af5cef09f28008f4592d`, all 29 component cases and **83 query pairs** pass:
166 separately launched candidate/reference instances match each other and
the independent P-automaton oracle exactly. Each side compares 2,432 physical
states and 121,088 ordered flags across the queries. Initial indices, both
transitions, Bad and final bits are included; there is no checksum substitute.
All one-variable primitive masks, forward/reverse constraints, lower/upper
nodes, denials, contradictions, diagonal flags and unreachable states are
covered. This is bounded regression evidence; the Lean equality handles all
inputs. The accepted component receipt records a 60-second process cap.

The existing 19 deeper generated cases and six component vectors on 62 Systems
pass at `2233aea`, with identical current Lean sources. Those older component
vectors use two checksums and retain that limitation. The default Lean core
passes at the same revision: 80 instances, zero disagreements, build and kernel
replay. Local verification passes 77 focused Python tests and the paper/index
checks; the paper check is a source correspondence guard, not a new proof build.

Reproduce after building the pinned optional module:

```sh
(cd lean && lake build +Subtail.EntailmentPrepared)
python3 scripts/check_summary_cached.py --cli --output tmp/summary-audit.json
python3 experiments/check_summary_cached.py --components --timeout 60 --output tmp/summary-components.json --scratch tmp/summary-components
python3 experiments/check_summary_cached.py --full38 --compare-baseline --timeout 20 --output tmp/summary-matched.json --scratch tmp/summary-matched
python3 experiments/check_summary_cached.py --stress-raw --compare-baseline --timeout 20 --output tmp/summary-stress.json --scratch tmp/summary-stress
python3 experiments/check_prepared_summary.py --components --generated --timeout 20 --output tmp/prepared-regression.json --scratch tmp/prepared-regression
python3 scripts/check_lean.py
```

The 60-second component command gives the expensive original constructor
validation headroom; CI also accepts complete evidence under a stricter cap.
It does not change the raw performance limit or assert a 60-second solver
speedup. The CI job retains its 40-minute total cap. The preceding successful
main job took about 27 minutes; the added check must fit the remaining budget.
If the job is interrupted, missing final receipts remain missing evidence.

## Independent review, failed validation attempts and handoff

The disjoint validation writer supplied `b44b2b5`, integrated as `82b3e68`.
That worker ran parser/source mocks but no native benchmark. A separate
read-only reviewer checked the exact theorem hypotheses, state order, backward
path orientation, every physical flag and unconditional public composition at
`2233aea`. This is source review of the supplied argument, not blind discovery.
The reviewer did not rerun Lean or the performance measurements.

Native testing exposed excessive batching: three n=3 cases returned UNKNOWN
when nine pairs shared one process. Splitting to one pair at `5047afa` exposed
the shared runner's 8,000-byte output tail; each pair printed over 9,000 bytes,
losing the first marker. Some forced-denial reference comparisons also reached
the 20-second cap. After capture was fixed, the stricter run at `66f545e`
completed all 83 candidate and 74 reference processes; the nine forced-denial
reference processes remained UNKNOWN. The final correctness run uses 60 seconds.
The earlier failures are retained in
[the receipt](../results/raw-summary.json), not relabelled as agreement.

At `66f545e`, each query and variant has its own process. The largest fixture
marker is 4,611 bytes. All 166 routes and malformed/UNKNOWN handling were also
checked with protocol mocks. The reviewer rechecked the repair and exact
83-query CI gates at that revision, and the separate 60-second correctness /
20-second raw budgets at `8c42c7a`. Actual native validation is parent-owned.
The fixture hash remains `94e242ddfee45b8e1553f665c75e7ca027cac908d04d9acdffdc0ee2b10e8d63`.

Every accepted Lean, runner and oracle source hash matches the final candidate.
Earlier revisions remain historical. E060 freezes its raw, 38-input and
component fixtures; the preceding E058 gate retains the separate 19 deeper
inputs. The new CI assertion block passes against the actual native receipts,
with preceding E059-shaped rows taken from the matched raw baseline. This is
validation of the assertions, not another native timing run. Timeouts never
become false.
No worst-case complexity, peak-memory, numerical-bound, novelty or extension
claim is made. Next measure the six-variable constructor's remaining subphases
before choosing another representation change. No successor is assigned.

Publication, actual main/CI readback and release of all reservations are recorded
in [#62](https://github.com/mhenglein/subtail/issues/62) and
[#37](https://github.com/mhenglein/subtail/issues/37). No historical worktree,
branch or stash is retired; unowned local workspaces were not audited.
