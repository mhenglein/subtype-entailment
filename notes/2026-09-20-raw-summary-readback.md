# Cached raw summary: proof and validation readback

Session: raw-summary-20260920. A010/A018, C081, #62/#37.
Base: `5adaa2949ffaeab94c4b7687d12b8ca6bd84ee94`.
Current proof/runtime: `2233aeabc04e284e14761b6565d64ffcb62c5680`.
Status: proof/kernel/CLI checks and independent source review pass; matched measurement pending.

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

## Pending acceptance

Matched raw/original-expression measurements, exact whole-instance Python
oracle comparison, CI gates, final canonical records and publication are
pending. None of these
is inferred from the phase timings or the module build above. No worst-case
complexity, memory, quantitative-bound, novelty or extension claim is made.
