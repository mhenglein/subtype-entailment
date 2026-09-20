# Subtail — current research state

## September 20: post-C081 package and usable solver

The [post-C081 programme](research/POST_C081.md) has delivered the ordinary
paper, focused novelty review, reader checkpoint, explicit resource account,
proved evaluation gate and CLI, explicit-top feasibility study and transfer
map. Licensing remains owner-deferred; authors and affiliations are placeholders.
This is a reproducible research draft, not a human-reviewed publication.

The [input resource account](notes/2026-09-20-c081-input-complexity.md) gives a
reviewed total-recursive time/space bound for a specified reference algorithm,
including normalization, summary construction, arithmetic and storage. It uses
the checked C082 witness bound. [C083](research/claims.md#c083) proves the
variable-only directed-reachability reduction, giving an NL lower bound.
Neither result supplies a tight complexity class or a practical runtime bound
for the native implementation.

The [solver](notes/2026-09-20-c081-solver.md) accepts finite-expression JSON.
Its optional Lean gate is unconditionally equal to the original decision;
build, kernel and runtime audits pass. Independent boundary review and 16
Python tests cover parsing, process limits and exact finite-graph checking.
Negative answers can include a regular countermodel and separating path;
the explanation search is incomplete and the Python boundary is not Lean-verified.

Matched E054 on wb-marcus completes 24/38 gated versus 22/38 original cases,
with no disagreements. The two gains are direct raw-backend calls; full-expression
coverage is unchanged. Fourteen gated cases remain UNKNOWN. Historical E052
Mac results are not rewritten. [Pinned native receipts](results/entailment-lazy.json)
distinguish the full source check from the later trust-label repair and rerun.

Next questions: reduce summary construction costs with a proved representation
change, extract complete regular countermodels, narrow the complexity gap,
seek external mathematical review, and investigate label-aware explicit-top
semantics. The original C080 F and an existential smaller compiler remain open.
The later sections preserve their dated milestones and earlier open status.

## September 20: corrected quantitative theorem (C082)

[C082](research/claims.md#c082) proves an explicit terminal witness bound with
`T_0=k+10`, `T_(j+1)=64*k*T_j^(6*T_j^2+2)`, `Fhat(1)=0` and
`Fhat(k)=2*(k+1)*product_(j=1..k-2)(T_j+2)` for k>=2. It covers the original
Witness and needs only terminal final states. Joint interval reconstruction
retains the shared word and every observation. Q004 now has the ordinary
explicit source-visit bound Fhat(k)+1.

A checked five-state counterexample **refutes the old universal concrete
compiler weight estimate** `64*k*T^(2*T+2)`. The original F alone and an
existential smaller compiler remain open. The earlier favourable size audits
are corrected at their entry points; their semantic results are kept separate.
C081's qualitative decision does not depend on the false size estimate.

[Independent source readback](notes/2026-09-20-c080-quantitative-independent-readback.md)
and [fresh combined build, kernel and runtime checks](notes/2026-09-20-post-c081-quantitative-integration.md)
pass at 7525724. The optional new modules leave the original core definitions
and paper source pins unchanged. This does not establish practical runtime or
a complexity class. The later original-input accounting and proved evaluation
gate are recorded in the current programme entry above.

## September 20: ordinary paper and post-C081 review checkpoint

The [ordinary mathematical paper](paper/manuscript.md) now gives the complete
C081 route, with full terminal preimage coverage/reconstruction, worked
examples, a [declaration map](paper/lean-map.md) and a
[proof dependency map](paper/dependency-map.md). An independent source readback
reviewed the central exposition; its seven local clarification requests were
addressed and rechecked. [Review scope and limits](notes/2026-09-19-post-c081-paper-readback.md).
This is an ordinary proof draft, not human peer review. The Lean source and
qualitative theorem remain those of the C081 checkpoint below.

The [focused novelty review](notes/prior-work/c081-review-2026-09-19.md)
separates inherited address/cap/periodic methods from the candidate new
whole-conjunction terminal construction and checked composition. A reviewed
guarded reduction to NP99 now gives a PSPACE upper bound for inputs without
bottom constants; that fragment's decidability is inherited. The full-C081
PSPACE upper/lower-bound transfers remain unproved. The later C083 elementary
NL lower bound is separate. The NP03 automata characterization alone is not
an earlier general decision theorem.

The [extension study](notes/2026-09-19-post-c081-extensions.md) gives an ordinary
regular-countermodel construction, the finite-tree zero-spine distinction,
small failures of naive explicit-top encodings, and separate arity, label
and variance obligations. E053 checks the literal counterexamples and a bounded
corpus; it does not prove an extension theorem. Explicit top first breaks the
old product-root propagation rule. No decision or undecidability result for
that extension is claimed.

The [complexity note](notes/2026-09-19-c081-complexity-review.md) records an
alternative witness-enumeration route whose quantitative dependency is now
supplied by C082 above. The [independent accounting readback](notes/2026-09-20-post-c081-cost-readback.md)
repairs omitted construction and storage costs. Its early open original-input
accounting is superseded by the reviewed note above. C083 supplies only the elementary reachability lower bound; stronger
transfers remain open. The original 13 Mac timeouts remain historical evidence.
The later E054 result and new interface are recorded separately above.

[The programme](research/POST_C081.md) tracks deliverables and remaining questions.
Author names and affiliations remain placeholders; licensing is owner-deferred.
No earlier numerical bound or unintegrated proposal is promoted by this
documentation checkpoint.

## September 19: complete checked subtype entailment decision (C081)

`EntailmentDecision.entailsCheck_correct` proves that a total executable
Boolean decides every finite expression constraint list and query over
bottom and binary product. Entailment ranges over arbitrary, possibly infinite
trees. There is no caller SAT, finite/regular-model, witness-bound or absorption
hypothesis. Finite named constraint sets and variable queries embed effectively
in this formal syntax. The same normalized summary instance feeds both checked
branches; expression normalization preserves the original query and models.

The default pinned Lean build, whole-library kernel replay, runtime dependency
audits and independent final semantic readback pass. Both distinct normalization
implementations have fresh regression checks. Native full-frontend tests record
which cases execute and which exceed their resource cap; the complete algorithm
contains no timeout. [C081](research/claims.md#c081),
[proof, source pins and validation](notes/2026-09-19-entailment-decision.md),
[independent review](notes/2026-09-19-entailment-decision-independent-readback.md).

This completes the repository's qualitative Problem 1.7 theorem. It does not
supply C080's specific U/F estimates, efficient execution, a complexity class
or a novelty claim. Q004 follows as a separate ordinary corollary of the
complete terminal decider: classify the finitely many labelled k-state inputs,
enumerate a witness for each positive input, and take their maximum source-visit
bound. [Construction and limits](research/conjectures/Q004.md).

The next useful work is a readable end-to-end proof account, careful prior-work
comparison and separately proved runtime improvements. No new worker or write
scope is assigned by this status. Older entries below preserve discovery and
failure history; statements that the overall problem was open describe their
own checkpoints and are superseded by C081.

## September 19: C029 has a checked executable infinite-continuation decision

`InfiniteDecision.infiniteWitnessCheck_correct` proves, for every finite binary
instance I under the existing strong `Absorbing I` condition:

```text
infiniteWitnessCheck I = true iff AbsorbingTerminal.InfWitness I
```

The total executable enumerates safe nonempty cycles of length at most k and
searches every finite prefix through a finite reverse monitor. The witness
prefix remains unbounded. Both directions of the monitor language theorem,
the actual periodic run, finite witness extraction, complete graph search and
candidate enumeration are checked. No unproved bound, monitor or reduction
premise remains. The original Witness, directed flags, Bad states, partial
transitions, diagonal cuts and empty prefix are unchanged. Equal rotations
of nonprimitive periods are compared explicitly.

The combined pinned Lean build, kernel replay and complete dependency audits
pass. Runtime definitions have no classical choice. Independent source reviews
cover the concrete trace, periodic helpers, both monitor directions and final
composition. The native executable agrees on all 15914 absorbing one/two-state
instances (885 positive), 29760 supplied-prefix/period cases and seven larger
guards. These finite tests are separate from the all-state theorem.
[Exact construction, proof readback, checked revisions and limits](notes/2026-09-19-c029-completion.md),
[native reproduction evidence](results/infinite-decision.json).

A negative C029 answer excludes infinitely continuable witnesses; terminal
witnesses remain possible. The terminal branch and normalized semantic split
below were already checked at this C029 checkpoint. The later C081 entry above
integrates the reviewed normalization and composes the complete expression-level
entailment decision. Separate C030 certification and quantitative U/F work are
not promoted by either result.

## September 19: normalized subtype separation splits into two exact branches

For every finite normalized constraint list C, queried variables alpha,beta,
and finite word w, `SummaryAutomaton.witness_iff_separation` proves that the
explicit finite summary instance has original Witness w exactly when w is a
canonical separating address. `not_entails_iff_witness` lifts this to
non-entailment over arbitrary, possibly infinite prefix-closed trees. No
finite-model, regular-model or word-length assumption occurs.

The instance enumerates pairs B,A of control subsets. Ordered flags are
B(left) intersect A(right); final states avoid forced roots. Bad states
combine the exact global UNSAT check with B meeting denial-danger controls.
The latter replaces the third safety subset while preserving every-prefix
checks. Last-letter Pop decomposition proves exact reachable transitions;
`summary_absorbs` proves empty-incoming-column absorption for ALL enumerated
states, including unreachable ones.

The two modules passed pinned Lean build, kernel replay, complete dependency
audits and separate source readback. Runtime definitions have no classical
choice. Native checks agree with an independent P-automaton oracle on 1803
query-word pairs across 42 normalized systems, including infinite-tree,
forced-root, diagonal, empty-word and missing-prefix cases. The tests also
compare every table entry in 528 physical states and 10752 ordered flags.
[Exact proof, construction, review and limits](notes/2026-09-19-subtype-summary-bridge.md),
[regression evidence](results/subtype-summary-bridge.json).

The absorbing safe-extension and finite safe-cycle/terminal-sink dichotomy
also compile. `SubtypeTerminalBridge.not_entails_iff_infinite_or_terminal`
combines them with the existing terminal decision:

```text
not Entails C alpha beta
  iff InfWitness (summaryInstance C alpha beta)
      or terminalWitnessCheck (terminalize (summaryInstance C alpha beta)) = true
```

InfWitness retains an original witness and an explicit safe finite stem plus a
nonempty safe cycle. Terminalization removes unsafe edges BEFORE selecting
safe ORIGINAL final sinks; Bad/flags/initial state are preserved. The combined
default build, kernel replay, all 100 new declaration dependency
closures and independent final source readback passed at source checkpoint
85a9e812544e1fb055f7fc2f5f8beb157ed33a0d. The native terminalization differential
exhausts all 15914 absorbing one/two-state encodings with no mismatch;
[results](results/absorbing-terminal.json).

**Later completion:** C029 supplies the infinite-branch executable, and C081
above integrates normalization and proves the unconditional full entailment
Boolean. C080's explicit U/F estimate remains a separate unresolved quantitative
claim; the exact normalized semantic split here is unchanged.

## September 19: terminal BorderAvoid has a checked executable decision

For every finite binary instance with terminal final states, the new total
Boolean `RankQueryDecision.terminalWitnessCheck` returns true iff there exists
a word satisfying the original `Basic.Witness`. The proof includes Bad states,
ordered flags, diagonals, the empty suffix and the empty witness. Both
`terminalWitnessCheck_correct` and the concrete `rankDecisionStatement` compile
and pass kernel replay. The algorithm enumerates finitely many one-letter
references and applies the checked finite preimage compiler at most k-2 times.
It does not assume the candidate clause-weight bound or its explicit F(k).

The discharged obligations are original-witness reversal, safe prefix
restriction, labelled milestone-chain coverage, maximal-rank finishing,
semantic promotion unwind and Boolean correctness. The maximum is over all
prefixes, not just the complete word. The executable definition and all new
interface declarations pass dependency audits; runtime definitions use no
`Classical.choice`. See the [proof and review readback](notes/2026-09-19-terminal-rank-decision.md),
[Lean theorem](lean/Subtail/RankQueryDecision.lean), and
[reproducible small-state differential](results/terminal-decision-regressions.json).

**Later completion:** the September 19 C081 checkpoint above discharges the
summary, C029, normalization and final composition obligations left by this
terminal result. The explicit U/F formulas remain unproved. The exhaustive
query compiler can be impractical; the runtime differential covers all
one/two-state terminal inputs, not performance at larger sizes. C080 remains
a candidate for its stronger quantitative bound.

## September 15–18: a candidate unrestricted decision by rank-query preimages (CANDIDATE, not established)

The A017 rank-query route proposes a complete ordinary proof that binary
terminal BorderAvoid, and hence Problem 1.7 through C029/C031, is decidable.
Terminality bounds the reversed prefix's positive border depth by k-1 (stage 1).
Successive first depth milestones are first returns of the preceding reference
(stage 2), and a first return has an exact coloured successor/KMP prefix-graph
description whose only entrance from the old graph is its first fresh vertex
(stage 3). The central claim is a promotion-preimage lemma (stage 4): a WHOLE
conjunction of existential directed regular-path queries with finite-colour
guards on the promoted graph compiles, in both directions, to a query of the
same grammar on the old graph, using one shared generator word per physical
interval. Closure of the grammar with an explicit clause-weight bound
`U_k(T)=64*k*T^(2T+2)` (stage 5) yields the computable, tower-sized bound

    F(1)=0,  F(k)=2*(k+1)*prod_{j=1..k-2}(T_j+2),  T_0=k+10,  T_(j+1)=U_k(T_j),

on the length of SOME witness of every positive k-state instance. If stage 4 is
correct, exhaustive search through F(k) decides every terminal instance, and the
audited semantic bridge (stage 6) transfers the decision to arbitrary, possibly
infinite trees. No polynomial, elementary or practical bound is claimed.

Evidence status as of September 18, 21:00 UTC, kept deliberately distinct.
Ordinary mathematics: written candidate proof (Sept 15) and full symbolic
compiler with the bound (Sept 17); two separate AI-assisted audits found no gap
in stages 1–5 and in the C029/C031 bridge, both informed by the author's
argument, neither a blind derivation nor a human referee. Finite evidence:
differential oracles agree on every recorded corpus; independent adversarial
fixtures for joint conjunction, shared generators and two-atom unions found no
discrepancy in the compiler, with one zero-length two-atom union exhausted and
the other joint or higher-rank unions certificate-guided or work-capped
([fixtures](notes/2026-09-18-closure-fixtures.md)). Lean, all kernel-checked
with no `sorry` and no custom axiom: stages 1–3 (terminal border depth,
milestone first returns, the exact coloured first-return graph identified with
the literal query graph, single entrance, at most s+1 fresh intervals;
[note](notes/2026-09-18-lean-first-return-graph.md)); stage 4a, the Closure
Lemma PINNED as the unproved `ClosureFor`/`ClosureStatement` with decidable
query satisfaction ([readback](notes/2026-09-18-lean-rank-query-statement.md));
stage 4c, an executable diagram compiler mirroring `compile_diagram` and
`closure_reverse`, the reverse half of `ClosureFor` for every diagram
enumeration ([compiler note](notes/2026-09-18-lean-rank-compiler.md)); the
conditional stage-5 unwind and the exact `T_h` weight recurrence, assuming
`ClosureFor`; also the semantic-only unwind specialized to the concrete compiler,
without a query-weight hypothesis (2026-09-19,
[checked pilot and separate statement review](notes/2026-09-19-wb-semantic-pilot.md));
and the stage-6 foundation: arbitrary-tree path-set semantics,
the canonical least model, `not_entails_iff_canonical`, exact stack
reachability and total executable normalized satisfiability
([canonical model](notes/2026-09-18-canonical-model-formalization.md),
[finite propagation](notes/2026-09-18-finite-propagation-formalization.md)).
Stage 4b is now kernel-checked as well: a finite diagram enumerator with exact
membership and an explicit computable budget, and `coverage : DiagramCoverage
I budget`, so `closure_iff` gives both directions of the semantic conjunct of `ClosureFor I
(preimage I budget)` for every safe reference
([coverage note](notes/2026-09-19-lean-rank-coverage.md); author readback
only). Correction on September 19: the terminal decision schema and finishing support
are now proved and integrated as described above. The later C081 also proves
the full stage-6 entailment decision. Still unproved in this integrated Lean
checkpoint are the clause-weight conjunct of `ClosureFor` and explicit `F(k)`.
The effective instance, ordered-cut/denial semantics, absorption and safe
terminal-split subclaim are now checked in the later September 19 entry above. The direct decision uses finite compiler
iteration, independently of the extra quantitative clause-weight contract. A
prior-work audit ([dossier](notes/prior-work/README.md)) found no source
supplying C080's whole-conjunction, shared-generator closure; it records
Schubert's withdrawn 2021 PSPACE claim (Lemma 5.5) as a failed attempt whose
invariant must be compared with stage 4 before any independence claim, and the
2019 Breuvart–Penelle–Rehof 2-EXPTIME restriction as mandatory prior art for
C067/C077. The generic compiled driver is resource-limited; timed UNKNOWN
results are not negative certificates. Problem 1.7's accepted status is
unchanged: CANDIDATE PROOF. Owner decision 2026-09-19: no external human
referee will be commissioned; the acceptance path is the kernel-checked
end-to-end decision theorem (`RankDecisionStatement` with its concrete
compiler and the stage-6 composition) together with statement readback by
a session other than each module's author (#33). Following the earlier pause,
the owner resumed a bounded next-step review and workbench/Lean proof pilot on
2026-09-19. That pilot discharged only semantic promotion unwind. The subsequent #30
assembly discharged terminal decision; continue with #31; consult
#34 and #37 for proof scope, integration and branch dispositions. No broader
worker launch or completed full decision is implied.

Failed attempts on the way are retained, not erased: the proposed finite
quotient of references by endpoint, transition action, visited set and full
agreement profile is false (four- and six-state examples), and the single-entry
hypothesis fails if inverse failure edges are admitted.

[Claims record C080](research/claims.md#c080),
[prerequisite rank hierarchy and failed quotients](research/RANK_ATTEMPT.md),
[candidate proof record](research/RANK_QUERY_CANDIDATE.md),
[compiler, bound and both audits](research/RANK_QUERY_COMPILER.md),
[closure proof](notes/2026-09-17-rank-query-closure-audit.md),
[closure review](notes/2026-09-17-rank-query-independent-review.md),
[semantic-bridge review](notes/2026-09-17-semantic-bridge-independent-review.md),
[Lean milestone readback](notes/2026-09-18-lean-rank-milestones.md),
[referee brief for stage 4](notes/2026-09-18-closure-lemma-referee-brief.md).
Formalization and review obligations are tracked one per GitHub issue under the
milestone "Rank-query closure formalized". Q004 would follow from F(k) if the
candidate holds, but remains OPEN. This entry is status synchronization by an
integrator session (issue #25), not a new proof, review or Lean result.

## September 13: source-sensitive target-return elimination with legal repeats

C079 replaces last-target uniqueness with a productive synchronized-return
certificate for each incoming target column. A certified earlier violation
transports to the last occurrence of that original target label. The certificate
survives deterministic regular restrictions with an explicit state projection.
Legal occurrences at unflagged source states remain permitted.

An exact fixed-tail filter stores the longest matching proper prefix and its
starting domain state, using at most K*m+1 states for a length-m pattern. Finite
last-target tails have length at most K-1; the filter therefore squares state
count at most. Each recursive step removes one ORIGINAL target column, not a
single product-state copy. Together with the prior C077 infinite-tail lemma,
this gives a native complete decision for initially return-closed inputs and
witness bound 2*k^(2^r), where r counts original target labels. All recursive
constraints act on the same full candidate word. This is not a general bound.

A five-state recurrent positive example has no accepted word with a unique
last-target suffix; three eliminations return 0100. An eight-state recursive
negative example also goes beyond the prior target-anchor wrapper. Independent
finite-language filter checks and negative-proof replay retain all branches.
The modular word 111101111110 passes every last-per-target check but violates
(0,5) at cuts (0,7), so dropping the return certificate is unsound. The known
modular positive and marking-barrier negative inputs remain UNKNOWN here.

[Canonical C079 / E051 record](research/TARGET_RETURN.md),
[full proof and exact projection hypotheses](notes/2026-09-13-target-return-elimination.md),
[solver](experiments/target_return.py),
[independent filter and negative-proof checks](experiments/check_target_return.py).
Written proof plus reproducible compact/full replay; independent mathematical
review pending, not Lean. No full local repository suite was run. The dedicated
read-only workflow checks the integrated index and reproduction; its remote
result must be read before claiming success. Q004 and unrestricted Problem 1.7
remain unresolved. Existing dependencies, history and ownership are preserved.

## September 13: native last-target anchoring and a quadratic certified-class bound

C077 collapses complete target-column constraints to uniqueness of the suffix
at the LAST target cut. A productive accepting tail cycle with no positive
return to any target supplies a witness of length at most k^2+k-2. This positive
criterion works for arbitrary flags. Otherwise the last-target tail languages
are finite, their productive graphs are acyclic, and explicit pattern-avoidance
products decide every possible tail. This is a complete native decision for the
complete-column class, not a reliance on an unimplemented string backend.

C078 gives an automatic polynomial finite-graph certificate for sparse flags:
finest transition colors preserve all last-aligned violations, and a second
pair-graph check certifies that completing target columns creates no new bad
words. State count and word length are unchanged. The same quadratic bound
therefore holds on the certified original instances, including nonflat graphs
with several recurrent sources and targets. No general polynomial bound follows.

The known positive (2,3) modular instance and the six-state marking-barrier NO
instance both remain UNKNOWN for this wrapper. An eight-state sparse instance
fails coloring but is solved positively by the target-free tail-cycle criterion.
These failures are retained, not promoted to NO or evidence of a complete cover.

[Canonical C077-C078 / E050 record](research/TARGET_ANCHOR.md),
[ordinary proof and exact scope](notes/2026-09-13-target-anchoring.md),
[native solver](experiments/target_anchor.py),
[checks and independent negative-product replay](experiments/check_target_anchor.py).
Local deterministic replay passed, including 58 finite negative certificates.
Written proof; independent mathematical review pending; not Lean. The dedicated
read-only CI job checks the integrated index and reproduction. Q004 and the
unrestricted subtype problem remain unresolved. Prior history below is retained.

## September 13: exact exponential scheme cost; switching does not close coverage

C076 strengthens the obstruction from source visits to the precise C075 symbolic
scheme cost. A binary counter/synchronization family has at most 18d^2+11d+8
states, one witness, and exact minimum cost (d+1)*(d*2^d+1), even after every
semantically dead flag is removed. Same-phase counter windows are injective,
so no source-pivot loop can repeat twice. Unknown bases and unbounded powers
therefore do not give a polynomial-cost cover in this syntax. A larger computable
cover, Q004 and C075's supplied-scheme theorem are not refuted. The underlying
synchronization/counter construction is prior C048/C050 work.

The attempted alternative gives an exact finite-action solver for finite-control
switching among shared marked suffixes, with regular guards and a common terminal
master. Its targets stay in that master, overlapping the earlier target-frontier
regime. It does not establish new general recurrent-target coverage. The failed
closing implication and the working restricted implementation are both retained.

[Canonical C076 / E048-E049 record and handoff](research/SCHEME_COST_BARRIER.md),
[proof, exact scope and commands](notes/2026-09-13-scheme-cost-and-switching-audit.md).
Both deterministic suites were executed and replayed with identical compact
results. Written proofs await independent mathematical review; no Lean or full
local repository suite was run. The new read-only CI job checks the integrated
index and both reproductions. Problem 1.7 remains unresolved.

## September 12: recovered source-visit bounds and closed-source-walk schemes

C073 records exact source-visit counts for the existing C046 modular family,
including genuinely live flags and the prime-period growth
`exp((1+o(1))*sqrt(k*log(k)))`. Polynomial total-source-visit bounds are excluded;
Q004's unrestricted computable-bound question is not refuted.

C074 supplies an exact source-arrival counter lift. A loop with a supplied
number of arrivals and every source-position rotation become first-return in
the corresponding lift. Commutation plus the lifted pivot-loop condition
represents whole-base powers, without lexical primitivity. Flags must be
lifted over all residue pairs, not just equal residues.

Using C071, C075 extends supplied power-scheme compilation to closed source
walks with repeated labels. Phase-local counters retain one shared assignment
of bases and tails. The formula gives a PSPACE upper bound INSIDE A SUPPLIED
SCHEME through the stated external theorem; the implementation is a compiler,
not the complete decision backend. A computable existence-preserving bound on
phase count and total listed base-source occurrences remains unproved.

Both formerly chat-only bundles are now recoverable from the repository:
original proofs, code, route outline, counterexamples, compact checks and
original manifests, plus deterministic reconstruction of every large result
and the explicit positive certificate. All fourteen manifest-listed files
replayed byte-for-byte during integration. No independent mathematical review,
Lean check, or full local repository CI is claimed. False assignments are not
UNSAT certificates. Earlier history, evidence levels and ownership are retained.

[Canonical C073-C075 / E046-E047 record and handoff](research/RECOVERED_SOURCE_WALKS.md),
[full recovery command and provenance](experiments/recovered_2026_09_12/README.md).
The unrestricted subtype-entailment problem remains open.

## September 10: exact synthesis inside unbounded source-cycle power schemes

C071 eliminates every forbidden comparison from the repeated boundaries of
B^m Y, with one unknown first-return loop word B, unknown terminal tail Y,
and unbounded m. Periodic-prefix matches reduce to the earliest source;
other matches reduce to finitely many captures of borders of Y and an exact
three-case power-conjugacy calculation. A pair-state regular monitor checks
all relevant block boundaries without expanding the exponent. The exceptional
conjugacy is essential: 010010101 passes its earliest source but is invalid
at a later copy. Lexical primitivity of B is not required.

C072 rotates a source-simple cycle to cover its internal sources and composes
finitely many such powered phases with shared tails. It gives a positive
existential word-equation reduction, hence a decision and PSPACE upper bound
for witness existence INSIDE A SUPPLIED SCHEME, allowing mixed good/bad families.
This goes beyond listing a bounded number of source visits, but does not prove
that a finite family of schemes covers every positive input. Changes of loop
word and an unbounded number of phases remain the global gap; Q004 is open.

[Canonical C071/C072/E045 record](research/SOURCE_POWER_SCHEMES.md),
[proof and exact external-theorem mapping](notes/2026-09-10-source-power-schemes.md),
[compiler](experiments/source_power_formula.py),
[deterministic checks](results/source-power.json).
Written proof plus reproduction; independent review pending, not Lean. The
optional string engine remains incomplete: all six larger two-cycle probes
and both free-exponent probes were UNKNOWN at the recorded caps. Earlier
results, refutations, ownership and historical handoffs below are preserved.


## September 10: copy-cycle acceleration and nonrational length counts

C069 supplies an eleven-state, three-flag terminal instance whose witnesses
have lengths 2N+2 exactly for composite N. Its exact count is tau(N)-2; the
length support is nonsemilinear and its counting series is nonrational.
Two- and one-flag variants also have nonrational RAW counts. This does not
contradict C065, which counts an existence-preserving return-free normal form,
or the newer C067 source-capture decision. The fixed instance has a short
witness; no noncomputability or undecidability conclusion follows.

C070 supplies an exact finite summary for a concrete unbounded-copy recurrence:
B^m 01 B with one shared primitive B=E(u)00. The equation UB=BU represents
all positive copy counts. A finite action-product/orbit solver decides the
family under arbitrary regular constraints on u and the whole output, without
an external SMT engine. This is not a general automaton decomposition.

[Canonical C069/C070/E044 record](research/COPY_CYCLES.md),
[proof and precise scope](notes/2026-09-10-copy-cycles-and-length-series.md),
[implementation](experiments/copy_cycle.py),
[result](results/copy-cycle.json),
[remaining route obligation](notes/2026-09-10-copy-cycle-route-outline.md).
Written proofs plus reproduction; independent review pending, not Lean.
The unresolved step is a complete existence-preserving cover, or a different
terminating treatment when shared blocks change along recurrent interactions.
Earlier agent results and ownership below are retained.

## September 9: source capture bypasses the single-source pumping gap

C067 gives a written decision/PSPACE upper-bound proof for **all single-source
binary terminal instances**, including an interior source that may recur.
A target's safe terminal-acceptance language is prefix-free, so each fixed
source suffix has at most one accepted-prefix capture per target. Exact
existential word equations exclude the corresponding forbidden comparison.
A one-source first-to-last deletion supplies a one-visit normal form.

C068 compiles an exact supplied sequence of source visits, and hence a supplied
visit bound, while allowing arbitrary unflagged recurrent data paths. The
source-acyclic productive class is decided. This does not yet decide the general
problem: Q004 asks for a computable existential bound on flagged-source visits,
or a finite symbolic replacement retaining shared words. A five-state example
refutes naive sequential source compression by creating an earlier violation.

[Proof, precise external theorem and limitations](notes/2026-09-09-source-capture-word-equations.md),
[compiler](experiments/source_capture.py), [checks](experiments/check_source_capture.py),
[results](results/source-capture.json), [Q004](research/conjectures/Q004.md).
Written proof + reproduction; independent mathematical review pending; no Lean.
The optional SMT adapter is not the complete theoretical solver. Earlier
single-source root-pumping handoffs below are historical, not the required
next step; their individual lemmas are not promoted or refuted by this bypass.

## September 9: complete guarded-order chains; terminal anchoring remains open

<!-- guarded-order-route-2026-09-09 -->
The earlier finite three-stage census now has a uniform proof-producing decision for any supplied number of phase-blind unary stages, each with a positive lower bound and one congruence. Equality-guarded inequalities saturate finitely; strongly connected components force equal counts, and compatible arithmetic progressions supply distinct values for the remaining components. The solver returns compact witness vectors or independently replayable NO proofs. This is a complete restricted class, not a cover of arbitrary recurrent inputs.

An opposing two-counter reduction is explicit for a nearby two-copy pattern-containment problem with arbitrary trailing context. It does NOT remove that context under terminal suffix-comparison semantics. The constructive coverage and opposing terminal-anchor implications remain open. [Proof, scope, evidence](notes/2026-09-09-guarded-order-and-terminal-anchor.md); [end-to-end outline](research/ORDER_COVER_ROUTE.md). Written proofs with executed checks; independent review pending, not Lean-checked. Earlier work remains below unchanged.


## September 9: an exact decision for every terminal one-flag instance

C065 gives a complete finite procedure for binary terminal instances with at
most one forbidden ordered pair, including arbitrary Bad sets, initial/source
states and multiple terminal finals. After an existence-preserving reduction
to a return-free source, terminality makes the forbidden period unique. Rational
length series count candidates and period incidences; their difference counts
witnesses exactly. A numerator-degree bound gives a complete zero test and,
for k>=2, the explicit witness bound `[k(k+1)/2]*(k+1)^k+k-2`.

This closes the single-FLAG subcase, not arbitrary single-source target sets or
Problem 1.7. It does not depend on the unresolved root-pumping claim. The same
method applies when distinct productive targets cannot reach one another.
C066 gives a seven-state acyclic two-target example where naive subtraction
vanishes despite an existing witness: joint incidences of the SAME word are
needed to extend the method. Rational length counting does not assert regularity
of the witness language, nor that source-wise decisions compose.

[Canonical C065/C066/E042 record](research/ONE_FLAG_COUNTING.md),
[proof](notes/2026-09-09-one-flag-counting.md),
[route outline](notes/2026-09-09-one-flag-route-outline.md),
[code](experiments/one_flag_counting.py),
[checks](results/one-flag-counting.json).
Written proof and executed regressions; independent mathematical review pending,
not Lean-checked. Earlier agent corrections and current unassigned handoffs below
are preserved; no worker is assigned by this update.

## September 9 research-method update (organizational)

Current priorities now require an end-to-end conceptual route, targeted
falsification, and a genuine opposing undecidability investigation alongside
the leading terminal existence-preserving approach. Exact definitions remain
mandatory; new Lean work is selective rather than the default milestone.
[Current plan](research/PLAN.md#current-research-priorities-2026-09-09),
[operating rules](AGENTS.md), [outline template](templates/proof-outline.md).

The C041/C044/C045 entries and the known Q002/Q003 source-note entry points
now distinguish the refuted universal conjectures from surviving identities,
equivalences and conditional local lemmas. This is status synchronization, not
a new proof or complete dependency re-audit. No mathematical evidence level,
problem status, or worker ownership is promoted by this update.


## September 9 audit: overlapping deletions need full alignment closure

<!-- overlap-deletion-audit-2026-09-09 -->
The equality-preservation clause of the paired-overlap pumping lemma is false for overlapping occurrences, including its stated large-shift window. A six-state family preserves acceptance after the two loop deletions but destroys the selected factor equality. The original note now carries a visible correction.

A corrected deletion-mask closure computes all physical positions that must be removed consistently across the supplied equalities. Loop and protected-cut checks give executable certificates for acceptance, those equalities, and their endpoint states. This repairs the local example, not the no-new-forbidden-border or global small-model obligation. [Proof, counterexample, and checks](notes/2026-09-09-overlap-deletion-audit.md). Written proof plus reproduction; independent review pending, not Lean.


## September 9 recovery: flag rewrites and cross-gap inference

<!-- saved-research-recovery-2026-09-09 -->
The two previously local research bundles are now repository-contained: source, proofs, counterexamples, and reproducible results. Exact gap-implication backends compute the greatest gap-equivalent annotation on a fixed terminal automaton. Guarded cyclic predecessor proofs and periodic-grid cross-gap rules preserve witnesshood; they close the recorded six-state barrier and seven-state equality-cycle examples. A terminating flag calculus is NOT a complete existence procedure; its preserved counterexamples still require other methods.

[Recovery, commands, and scope](research/SAVED_RESEARCH_RECOVERY.md). Written proofs remain pending independent mathematical review; no new Lean proof or unrestricted decision is claimed. The earlier and concurrent work below is retained unchanged.


Navigation updated: 2026-09-08. Scientific evidence remains at the status recorded in the linked proofs, experiments, and Lean checks.

This is the compressed scientific memory of the project. Read this after `research/problem.md` and before starting new work.

## Problem

Decide Problem 1.7: subtype entailment over bottom and binary product for arbitrary, possibly infinite trees. **Completed by C081 above.** The following earlier frontier remains historical.

## Latest continuation: combined tails and a regular-decoration barrier

The synchronous-separator and semantic-tail methods have now been combined
and tested locally for arbitrary nonflat data paths. A weaker G-specific
compiler synchronizes only productive last-aligned comparisons, preserving
witnesshood rather than every flagged agreement. This resolves the previous
three-state target-recurrent structural obstruction and strictly improves on
all-pair synchronization in a separate encoded regression.

The proposed closing strengthening is false. A fixed six-state nonflat NO
instance survives every finite semantic-tail bound after EVERY regular,
candidate-covering choice of optional separator markings. This includes
history, regular lookahead, nondeterministic decoration relations and finite
families of them, with original cut-state flags unchanged. A suffix-viability
and periodicity proof establishes the general statement. The instance itself
has a simple all-length arithmetic NO certificate with an arbitrary regular
middle region. This is not an undecidability result.

The remaining normalization must be allowed to change or discard candidates
with proof, or use a complete symbolic cover; larger finite-state separator
memory by itself is not a complete repair.

[Proof, checker, evidence levels and companion-code availability](research/SYNCHRONIZED_TAILS.md).
The proof and standalone barrier checker are repository-contained. The full
combined solver/checker were tested locally and provided in the reproduction
package; their larger source upload was blocked. No new Lean proof,
independent mathematical review or full local repository CI is claimed.

## Same-day continuation: strategy decision and the single-source target

A September 8 review compares the four recorded routes (terminal small-model
theorem, complete NO certificates / regular containment, undecidability, new
logic or well-structured systems) against the accumulated refutations and
selects the terminal small-model route, executed bottom-up by flag structure.
By C030/C031 nothing is lost by restricting to terminal-final instances.

The first concrete target is the single-source case: all flags leave the
start state. Its witnesses are exactly accepted words none of whose periods
lands on a flagged target state of their own run, i.e. Anderson's
unbordered-word problem with coloured borders. A junction lemma and two
small-root lemmas prove that a shortest single-source witness longer than
`n^2 + 6n` is a near-power of a primitive word longer than `n` with a defect
and tail shorter than `n` (at most `n+2` periods); bounding that root length
is the one remaining single-source obligation, with its two missing steps
stated. An exact census decides all single-source instances through five
states (longest shortest witness 4 and 6; a six-state search found 8).

Every recorded hard family uses flags in both comparison directions; a
one-directional flag pattern expresses only a colexicographic inequality
between compared blocks, never equality. This is an observation about known
constructions, not a theorem.

[Review, exact forms, and obligations](notes/2026-09-08-strategy-review-and-period-state-form.md),
[single-source lemmas, theorem, and open step](notes/2026-09-08-single-source-shape-lemmas.md),
[checker](experiments/check_period_state_form.py),
[results](results/period-state-form.json),
[census](results/single-source-census.json).
No new claim or experiment identifier; no evidence level changes; no Lean.

## Previous continuation: encoding-aware synchronous separators

The raw-marker obstruction from the previous continuation is no longer an
obstruction to every delimiter-based method. A finite union-find colouring now
synchronizes transition colours along every pair path rooted at a flag. The
exact compiler maps each transition `a` to `1a` plus an optional `00` separator
and preserves every flagged suffix comparison in both directions.

If synchronized separator classes avoid original cycles, the compiled instance
falls under C053. If terminal synchronization forces an early separator cycle,
C056 can still pump it when it occurs before relevant targets. In particular,
the ten-state `0->00, 1->10` NO example that survives every raw-zero tail bound
has its latent logical-zero separators recovered and is inside the exact C053
class. Thus the previous failure was encoding-sensitive, not a barrier to
finite symbolic separator recovery.

The next preserved obstruction is sharper: a separator cycle forced by terminal
synchronization can be reachable from a relevant flag target. The current C056
wrapper returns UNKNOWN there. The highest-value continuation for this route is
to combine these encoding-aware transition classes with the semantic-tail
pending-context construction so target-recurrent separator cycles are summarized
rather than structurally forbidden.

[Proof and limits](notes/2026-09-08-synchronous-separators.md),
[compiler/deciders](experiments/synchronous_separators.py),
[result](results/synchronous-separators.json).
Written proof + reproducible checks; independent mathematical review pending;
no new Lean theorem is claimed.

## Previous continuation: semantic marker tails

The September 8 A012/A017 attempt decides the fixed-H marker-tail relaxation
by finite shared-reference saturation. Earlier original flag-target STATES
may recur without restriction: the omitted targets are positions before the
last H blocks, not state labels. Weighted joint word actions decide whether
actual last-aligned comparisons have bounded marker count. Finite marker
spectra make this relaxation exact, even with unbounded comparison LENGTHS.

A six-state nonflat NO example with recurrent marker targets is certified at
H=1 although every finite necessary length/gap language is inhabited. Removing
one flag gives the checked witness 1110110. The reset-marker corollary supplies
a complete subclass independent of the older target-cone cycle prohibition.

The closing strengthening fails: the exact code 0->00, 1->10 applied to the
older five-state NO example produces an inhabited relaxation for EVERY H.
Increasing raw marker budgets is therefore not a complete negative procedure.
The synchronous-separator continuation above repairs this specific encoding
obstruction but does not settle target-recurrent separator cycles.

[Scoped record and commands](research/SEMANTIC_MARKER_TAILS.md),
[proof and limitations](notes/2026-09-08-semantic-marker-tails.md),
[results](results/semantic-marker-tails.json).

## September 8 consolidation

The reviewed research PR stack #6–#14 has been consolidated onto current main without replaying stale branch copies of shared ledgers/trackers. The integration preserves proof notes, implementations, and independent regressions while keeping later main-branch work authoritative.

[Consolidation record and canonical result map](research/CONSOLIDATION_2026-09-08.md). [Repaired PR #12/#14 supplement](research/REPAIRED_12_14_2026-09-08.md).

The first consolidation merge integrated the scientifically surviving material from PRs #6–#11 and #13. The concrete review defects that initially held PR #12 and PR #14 back have since been repaired and their distinct results are indexed as C060–C064 and E038–E041. These remain written-proof/reproducer results at the evidence levels stated in the repair supplement; they are not newly Lean-checked and do not resolve Problem 1.7.

A dedicated CI job runs the imported continuation regressions together on one tree, including the repaired #12/#14 checks.

## Major consequence: Q002 and Q003 are refuted

The modular-synchronization construction gives an eight-state terminal binary instance whose exact witness language is

    { (1^(6t) 0)^2 : t>=1 }.

Its unique shortest witness has length 14 and exact sufficient budget 7, while `k-2=6`. Any accepted word whose agreement profile is contained in that shortest witness's profile is itself a witness, so neither a budget-six profile-dominated replacement nor a strictly shorter profile-dominated replacement exists.

Therefore [Q002](research/conjectures/Q002.md) and [Q003](research/conjectures/Q003.md) are **REFUTED**. Their earlier bounded searches remain valid historical observations about smaller tested ranges.

The same modular family, using periods `1,...,m`, gives terminal witness budgets at least `2^(Omega(sqrt(k)))`. This rules out every polynomial state-count budget bound but does not rule out a larger computable bound or a symbolic decision method.

[Proof](notes/2026-09-05-modular-synchronization.md), [reproducer](experiments/check_modular_sync.py).

## Exact synchronization and certified recurrent subclasses

Several integration results substantially enlarge the exact decidable toolkit without closing the unrestricted problem.

### Whole-word synchronization

Binary terminal flags can force multiple regular blocks to be copies of one common word. The direct compiler reduces supplied DFA intersection to a terminal BorderAvoid subclass with an exact finite product solver. This supplies the recorded fragment-specific PSPACE-hardness route and a counting-word family showing that fixed-word skeleton bodies / ordinary concatenation descriptions can require superpolynomial size.

[Implementation](experiments/word_sync.py), [counting family](experiments/counter_intersection.py), [regression](experiments/check_word_sync.py).

### Necessary-budget incompleteness and bounded delimited schemas

A fixed five-state flat terminal NO instance defeats the general strategy of waiting for some finite `Necessary(L,D)` automaton to become empty: for every finite budget pair there is a different non-witness that survives that test.

For a supplied bounded delimited-block schema, however, a reverse padded-convolution machine with persistent equal-tail/hit masks decides arbitrary logical flag relations exactly; the supplied-schema problem is PSPACE-complete. A raw-input certificate derives a finite complete cover for a checkable bounded-marker class.

[Proof](notes/2026-09-06-delimited-convolution.md), [schema solver](experiments/delimited_blocks.py), [raw certificate](experiments/marker_certificate.py).

### Target-frontier and target-tail pumping

The target-frontier construction permits unbounded marker cycles before the first relevant flag target, provided no productive marker cycle is reachable from a relevant target. A powerset keeps all possible early-block observations tied to one common reference tuple.

A separate target-tail construction gives a finite pending-context pump when all flag targets have bounded marker distance to final. Its checker is retained as differential evidence on overlapping certified inputs.

[Target-frontier proof](notes/2026-09-06-target-frontier.md), [implementation](experiments/target_frontier.py), [target-tail proof](notes/2026-09-06-target-local-pumping.md), [implementation](experiments/target_tail.py).

## Universal terminal run normalization

For every defined binary word ending at a terminal accepting state, fixing the number `r` of maximal homogeneous runs is enough to bound and normalize the **run lengths** while preserving:

- the run-letter pattern and run-boundary states;
- the visited-state set;
- the complete suffix-agreement profile.

The construction compresses gaps between sorted repeated counts rather than truncating counts independently. It therefore preserves every flag relation and Bad annotation on the fixed automaton.

Consequently witness existence with a supplied maximal-run bound `R` is decidable by finite symbolic search; with `R` supplied in unary the problem is NP-complete. For each fixed `R` there is an exact polynomial-time enumeration with degree depending on `R`.

**What is not proved:** no computable bound on the number of runs required by some witness of every positive instance is known.

[Proof](notes/2026-09-06-run-normalization.md), [normalizer](experiments/run_normalization.py), [bounded-run search](experiments/run_bound_decision.py).

## Latest main-branch last-flag spectrum result

The September 7 A017 continuation decides whether lengths of actual last-aligned flag comparisons are bounded. A finite word action on states and synchronized pairs yields an effective unary-regular spectrum. If finite, its exact maximum `H` makes `Witness = Necessary(H,0)` on the stated boundary-normalized slice; if unbounded, the procedure returns a pumping certificate.

Unbounded last-aligned spectra are **not** existential NO certificates. The existing seven-state example has unbounded last-aligned comparisons while another comparison supplies a constant short violation.

[Scoped record](research/LASTFLAG_SPECTRUM.md), [proof](notes/2026-09-07-realizable-lastflag-spectrum.md), [results](results/lastflag-spectrum.json).

## Shared-word relations and fixed-skeleton arithmetic

The earlier A017 work provides exact finite composition of shared-word templates and exact universal verification for supplied regular families. Generic iteration of those relations cannot be treated as a decidable black box because two-output append relations already encode Post correspondence; this is not itself a reduction to BorderAvoid.

A016 provides exact Presburger formulas for fixed word skeletons and a finite complete cover for flat terminal candidate graphs. Once a finite schema is known, large arithmetic exponents are manageable. The missing problem is obtaining a complete finite/existence-preserving cover for arbitrary nonflat recurrent structure.

[Shared-word composition](notes/2026-09-06-shared-word-composition.md), [recurrent residuals](notes/2026-09-06-recurrent-residuals.md), [flat arithmetic](notes/2026-09-05-terminal-arithmetic.md).

## Established / strongest prior results

- The top-free characterization has been audited and supports canonical regular countermodels under its stated satisfiability premise.
- Principal binary truncation/context rules have Lean-checked core versions; finite-budget predicates, reversal machinery, and an exact two-state decision are Lean-checked.
- The terminal-final branch is fully expressive for abstract binary terminal BorderAvoid: every `k`-state terminal-final instance has a word-preserving subtype realization on `2k+1` variables.
- A genuine nine-variable subtype system has a nonregular terminal separating language.
- Flat terminal graphs have an exact finite Presburger skeleton decision.
- The normalized four-state terminal census is complete.
- Terminal suffix comparisons have several bounded structural invariants, but none currently bounds arbitrary essential recurrent structure.

Consult `research/claims.md` before treating any older result as formally established; evidence levels differ.

## Refuted ideas / dead ends worth preserving

Do not restart these without a materially new hypothesis:

- Q002's `k-2` agreement-profile / budget bound;
- Q003's unconditional strict profile descent;
- any universal polynomial terminal witness-budget bound;
- any universal constant bound on simultaneous loop deletions;
- the negative semiprocedure that waits for a fixed `Necessary(L,D)` language to become empty;
- completeness of candidate-covering regular separator decoration followed by finite semantic-tail emptiness, with unchanged cut-state flags;
- the old prefix-reachability regular-language formula;
- a universal rigid-word bound from nonmerging runs;
- ordinary state repetition as justification for loop deletion;
- reading bounded-search failure or resource exhaustion as mathematical `NO`.

## Current frontier

**September 18 update.** The highest-value question is now whether the
stage-4 promotion-preimage lemma of the rank-query candidate (C080, top entry)
survives independent human review and formalization. If it does, the frontier
below is resolved by that route; if it fails, the obstructions below remain the
map. Nothing below is superseded until then.

The central problem had sharpened to **existence-preserving control of arbitrary recurrent structure**.

We can now:

1. normalize run magnitudes exactly once the number of runs/markers/skeleton pieces is fixed;
2. solve arbitrary regular data languages inside supplied bounded schemas;
3. recover some latent logical separators through exact transition encodings rather than raw symbols;
4. pump target-free and pre-target recurrent prefixes using finite pending contexts;
5. decide several broader certified marker/target classes;
6. represent and solve large arithmetic synchronization symbolically.

What is still missing is one of:

- a complete treatment of synchronized separator cycles reachable from relevant targets;
- a computable bound on essential runs/markers/schema pieces needed by some witness;
- an effective finite symbolic cover that need not literally bound that count;
- a different terminating exact decision procedure; or
- a genuine undecidability reduction using only the normalized subtype fragment.

The highest-value constructive question is now:

> Can a G-specific transformation change or discard candidate words with a proved existence-preserving finite symbolic cover, while retaining shared assignments across recurrent components?

The new regular-decoration barrier rules out one candidate-preserving route to
this goal, not the goal itself. Fixed-H pending contexts remain useful exact
subroutines; their tested combination does not supply global coverage.

A negative result would also be decisive if it supplies a real reduction rather than only showing that a proposed abstraction fails.

## Repaired reviewed work

PR #12's broader nonterminal final-symbol/run-profile contraction now includes the iterable-API repair and list/tuple/generator parity regression. PR #14's regular-family/shared-lasso/one-flag continuation now carries the boundary-safe theorem scope, whole-bad-language argument, corrected lower-bound scope, deterministic evidence publication, and narrowed MSO audit. Canonical records are C060–C064/E038–E041 in [the repair supplement](research/REPAIRED_12_14_2026-09-08.md). Independent mathematical review is still pending where noted.

## Research map

- A008 — structure and bounds of minimal witnesses.
- A009 — lower-bound families and candidate-bound destruction.
- A010 — exact subtype-to-automata bridge.
- A011 — converse/expressiveness, including exact terminal realization.
- A012 — complete nonexistence certificates and encoding-aware certified subclasses.
- A013 — restrictions shared by actual summary automata.
- A014 — periodic/cap saturation.
- A015 — occurrence-context truncation.
- A016 — exact fixed-skeleton arithmetic and terminal covers.
- A017 — bounding/representing essential repeated blocks; central; its rank-query candidate (C080) is under review.
- A018 — backwards formalization from executable Lean decision infrastructure; now formalizing C080's stages in order.

## Integration rule

A research session is not finished merely when an agent has an answer. It is finished when the reusable part is integrated into shared state:

`investigation -> evidence -> review -> stable record -> STATE.md frontier update`

Keep bounded evidence, written proofs, independent review, and Lean verification visibly distinct.
