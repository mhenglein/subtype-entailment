# Raw decision backend: measurement and refinement route

Date/session: 2026-09-20, raw-backend-20260920. A010/A018, C081; #61/#37.
Base: `b02352efba0ceabec1c542da66e534bdc5675890`. Status: exploratory outline.

## Exact target

For every finite normalized bottom/product constraint list C and query a,b,
preserve the Boolean of `TerminalDecisionLazy.rawNormalizedEntailsCheckLazy`.
Its truth means entailment over arbitrary prefix-closed trees. The raw backend
must still decide through the same summary instance and infinite/terminal
witness branches. Frontend reflexivity, premise and supplied-path shortcuts
are excluded from this experiment. An implementation refinement is useful
only if it improves measured execution under unchanged limits.

## Construction and measurement

The summary automaton has states consisting of two subsets of the n normalized
variables, hence 4^n physical states, indexed in the existing enumeration. Its
binary transitions advance both pop summaries. Its initial state contains the
empty-word summaries, its Bad bit includes inconsistency and denial danger,
its finals avoid forced target roots, and its ordered flags record intersection
of the source subset with the target subset. The existing checked definitions
and their arbitrary-tree correspondence remain authoritative and unchanged.

The complete Boolean negates the disjunction of C029's infinite-witness test
and the terminalized instance's exact terminal test. The first diagnostic
splits summary construction, eager cycle-candidate construction, and prefix
monitor search; if reached, it splits terminalization, empty witness, safe
one-letter gate, query promotion and candidate scan. These are forced IO trace
boundaries in the same order as the reference code. Trace overhead is included;
only a subsequent original-#eval run can support an end-to-end improvement.

Run the seven unchanged E052 raw fixtures, including five prior UNKNOWNs, on
an isolated wb-marcus checkout with 20-second wall/CPU, 16-GiB Linux address-space,
one-thread and 32768-KiB stack limits. Killed processes retain trace evidence
but never a Boolean answer. Any final result requires completed protocol,
normal exit and agreement with the fixture's independent expected answer.

## Proof and falsification gates

The next link is deliberately unresolved until measurement: identify a costly
finite construction and propose an exactly equivalent executable definition.
State its all-input equality and ordinary proof before substantial Lean work.
Do not replace complete coverage with a bounded prefix search or assume that
a safe cycle endpoint is reachable. Preserve safe runs, empty words, diagonal
flags, missing transitions, pre-final loops and strong-absorption assumptions.
A merely faster shortcut is not an improvement to these raw probes.

A separate reader reviews source costs and semantic boundaries while the parent
runs the profiler. Any new Lean module needs pinned build/kernel/dependency
checks and a semantic readback, plus independent small-instance regressions.
The old receipts and failed trials stay unchanged. Tests do not strengthen C081,
C080 bounds, finite semantics or novelty. This already decided fragment has no
remaining undecidability route; richer signatures retain separate questions.
