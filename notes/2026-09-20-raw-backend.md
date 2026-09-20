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

## Measured obstruction and sufficient ordinary proof

Baseline `9b359df` completes summary construction in 13–28ms on the five n=2
fixtures, then exhausts each 20-second limit inside eager cycle-candidate
construction. The two n=1 controls complete. At `a47e59f`, streaming alone
completes five/seven; the two entailed n=2 cases still exhaust their limits
while searching cycles. The initial-safety gate completes all seven in
0.819–0.870s diagnostic wall. These are ablations, not final matched timings.

For a finite alphabet list X, define E(X,d,P) recursively. At d=0 it returns
P([]). At d+1 it tests, in order, each x in X using E(X,d,w ↦ P(x::w)),
stopping at the first true result. Induction on d proves equality with
`(exactLists X d).any P`: the successor step is exactly list flatMap followed
by any, and mapping a cons is composition with P. Duplicates and the empty
alphabet do not matter. Then B(X,k,P) scans d=0,...,k with E. The definition
of `boundedLists` as this flatMap proves equality with its any. Both procedures
terminate structurally and store no complete exponential word list. They may
still examine exponentially many words if every answer is false.

For each endpoint q, keep its final and empty-incoming-column checks ahead
of B. These conjuncts are already necessary in `cycleCheck`, so inserting
them changes neither successful pairs nor the final disjunction. Within B,
test the unchanged `cycleCheck I q c && prefixCheck I q c`. The finite
q scan and exact word scan therefore have the same Boolean as the original
candidate-list filter followed by any. No PrefixGood check is approximated.

Finally, every successful pair in the reference infinite check supplies,
by `candidate_prefixCheck_correct`, a word w with `SafeRun I I.initial w q`.
Its cut at zero exists and is safe, even if w is empty. Thus a false
`safeState I I.initial` makes the whole reference check false. Testing this
bit first preserves the Boolean for all finite instances, including those
which are not absorbing. Only the inherited interpretation as InfWitness
requires absorption. This proof does not confuse a safe endpoint with a
reachable endpoint; `prefixCheck` still decides the full safe prefix language.

Substitute the resulting equality into the raw disjunction while retaining
the exact same summary automaton, terminalization and terminal decision.
Substitution into the prepared frontend's final fallback then preserves its
original-expression correctness. No frontend shortcut enters a raw probe.
The initial unsafe case skips only the infinite branch; the terminal branch
is still evaluated by its established procedure.

Outstanding acceptance obligations: Lean proof and runtime audit; independent
ordinary readback; native abstract-component checks; matched original #eval
benchmark; current frontend/deeper/CLI regressions. Performance outside these
measured families, a memory bound, and the terminal promotion cost remain open.


## Larger diagnostic boundary

At `262f57a`, separate gated diagnostic probes with empty constraints and query
0<=1 finish for n=3 in 1.471 seconds, but return UNKNOWN for n=4 at 20.008
seconds while constructing the summary instance. The expected false answer
has the same direct root-only/bottom model, with unused variables bottom.
These probes stay outside the original seven-fixture identity. The n=4 trace
does not evaluate the new cycle scan and suggests reusing the already proved
balanced tables in summary construction as the next exact refinement. That
construction, its equality proof and any resulting speedup are unperformed.
The terminal-promotion branch still needs its own discriminating family.
