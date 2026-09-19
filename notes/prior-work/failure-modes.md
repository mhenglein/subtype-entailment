# Failure-mode catalogue

This is an indexed inventory of known obstructions and audit hazards, **not a claim to enumerate every possible failure**. Source keys resolve in [bibliography.md](bibliography.md). `LOCAL` is a concrete calculation from this investigation, not an independently refereed theorem; `REPO` points to an existing canonical record; `BOUNDARY` is a cited source result; `HAZARD` is a reasoning obligation, not a demonstrated counterexample to C080.

## Semantics and logical scope

| ID / status | Invalid inference | Evidence / minimal check | What remains possible |
|---|---|---|---|
| F01 HAZARD | No top in the hypotheses means no top in the model. | PW-HR98 / PW-NP99 and [problem](../../research/problem.md). List allowed valuation labels, not only syntax. | A proved top-free simulation may transfer a result. |
| F02 HAZARD | A regular infinite countermodel is a finite-tree countermodel. | The memo's arbitrary-tree domain. Read back the quantifier over trees and its representation. | A separate finite/regular equivalence theorem with matching assumptions. |
| F03 BOUNDARY | Full first-order undecidability settles Horn entailment. | PW-SU06. Audit every negation and quantifier introduced by the reduction. | A reduction preserving the exact target fragment. |
| F04 HAZARD | Hardness of arbitrary BorderAvoid transfers backwards to subtype entailment. | [Known dependency direction](../../research/problem.md). Supply realization of allowed side conditions. | Hardness for the auxiliary problem alone, or a new reverse encoding. |
| F05 HAZARD | A fixed-word matching algorithm decides regular-language containment. | PW-KU26 versus the [terminal-copy question](../2026-09-08-terminal-backreference-literature-audit.md). Write the outer word quantifier. | An effective uniform cover of all candidate words. |
| F06 HAZARD | One decidable not-contains predicate decides arbitrary synchronized conjunctions. | PW-HHL25; [C079 route](../2026-09-13-target-return-route.md). List all predicates and shared variables. | A special reduction satisfying the single-predicate or other stated hypotheses. |

## Factorization, periodicity and automata

| ID / status | Invalid inference | Evidence / minimal check | What remains possible |
|---|---|---|---|
| F07 LOCAL | Straight left-factor language guarantees a unique concatenation split. | [Priesnitz audit](dossiers/priesnitz-2004.md): `{0,01}` and `{1,11}` give `0.11 = 01.1`. | Prefix-free left factors suffice for this split lemma; the thesis's final theorem is not refuted here. |
| F08 LOCAL | Merging accepting states with the next automaton's start preserves determinism because no accepting state is cyclic. | Same finite example: the boundary can have competing outgoing transitions. | An explicit deterministic construction or stronger boundary property, with a language-preservation proof. |
| F09 BOUNDARY | Bounded resets imply a decidable modulo-counter emptiness problem. | PW-RS14 Theorems 3.9/3.15. Count input-head reversals, counter wraps/reversals and resets separately. | Import the positive theorem only with all its bounds. No Subtail reduction is supplied. |
| F10 BOUNDARY | If every instance defines a regular language, construct a DFA and decide it. | PW-KS10 Theorem 5.2. Demand a uniform algorithm, not existence. | An effective construction for a more restricted instance family. |
| F11 BOUNDARY | Unique decipherability in a monoid of languages is ordinary unique parsing of a word. | PW-KS11 Theorem 2.1 concerns equality of language products. Specify the monoid elements. | Separate word-code or prefix-free arguments. |
| F12 HAZARD | A finite transition monoid automatically captures future border obligations. | PW-KUF07 applies to a supplied morphism; [rank failures](../../research/RANK_ATTEMPT.md). | A new finite algebra with a proved witness-preserving composition invariant. |
| F13 REPO | Endpoint, transition action, visited set and an agreement profile determine all future extensions. | [RANK_ATTEMPT](../../research/RANK_ATTEMPT.md) and current STATE retain finite collisions. | A richer invariant or a weaker existential replacement theorem. |
| F14 REPO | Ordinary unbordered-word shortening preserves a state-colored target relation. | PW-BORD09 and [source-color audit](../2026-09-05-source-border-anderson.md). Recompute the target start state after each splice. | The additional closure hypotheses in the restricted argument. |
| F15 REPO | Last-target checks alone cover earlier source-sensitive violations. | [TARGET_RETURN](../../research/TARGET_RETURN.md): the recorded modular example needs the return certificate. | Certified synchronized-return transport; legal repeats need not be forbidden globally. |
| F16 REPO | A lifted product-state target is interchangeable with its original target label. | [TARGET_RETURN](../../research/TARGET_RETURN.md). Check projected flags and removal of the whole original column. | A lift that preserves the original relation and all copy obligations. |
| F17 HAZARD | A nonoverlap copy decomposition covers proper overlaps as well. | [terminal bad-language decomposition](../2026-09-07-terminal-bad-language-decomposition.md). Test nested/overlapping copies separately. | A separate periodic-overlap theorem with its exact nonmerging assumptions. |

## Shared witnesses, graph surgery and completeness

| ID / status | Invalid inference | Evidence / minimal check | What remains possible |
|---|---|---|---|
| F18 HAZARD | `(exists C P(C)) and (exists C Q(C))` implies `exists C (P(C) and Q(C))`. | Logical counterexample: `P(C): C=0`, `Q(C): C=1`. The actual compiler must share generators for shared intervals. | One joint reconstruction with all atom transports. |
| F19 REPO | Single entrance remains true after adding inverse failure edges. | [rank-query candidate history](../../research/RANK_QUERY_CANDIDATE.md) and STATE. Audit the literal directed edge alphabet. | The established directed construction, or a new theorem for the enlarged graph. |
| F20 HAZARD | An extension exists, therefore it satisfies the original query. | Require a satisfaction conclusion about that same extension. Do not confuse the old intermediate theorem with current `closure_reverse`. | Explicit atom/run transport; current main already records reverse progress. |
| F21 HAZARD | Enumerating all chosen syntactic diagrams proves every semantic witness has one. | [compiler record](../../research/RANK_QUERY_COMPILER.md), issue #28. Produce a diagram from an arbitrary valid extension. | A separate forward coverage and bounded-visits proof. |
| F22 HAZARD | An unwind theorem assuming `ClosureFor` proves the concrete compiler's closure. | Read all declaration parameters and dependencies, not only the theorem name. | Discharge the concrete closure contract independently. |
| F23 REPO | A solver for supplied schemes proves a finite complete scheme cover. | [SCHEME_COST_BARRIER](../../research/SCHEME_COST_BARRIER.md). Separate solver, cover existence and effective bound. | The supplied-scheme result remains useful; a larger computable cover is not refuted. |
| F24 REPO | Superpolynomial visits/cost or nonsemilinear lengths exclude every computable witness bound. | C069/C073/C076 in [claims](../../research/claims.md). State the bound being disproved. | A larger computable bound or a different representation. |
| F25 HAZARD | Timeout, failed certificate or bounded search exhaustion is NO. | Require a complete negative certificate or proved exhaustive bound. Otherwise retain UNKNOWN. | Another certificate, longer witness or stronger complete procedure. |
| F26 HAZARD | General invalid-history patterns automatically respect a terminal-copy anchor. | PW-TF24 and the [older audit](../2026-09-08-terminal-backreference-literature-audit.md). Locate each second copy relative to the whole word's end. | A new regular encoding exposing every error at the allowed anchor. |

## Scholarship and integration

| ID / status | Invalid inference | Evidence / minimal check | What remains possible |
|---|---|---|---|
| F27 BOUNDARY | A search-visible abstract is an established theorem after withdrawal. | PW-SCH21 v2 record. Follow version/status links before importing a bound. | Independently reproved unaffected components; no blanket rejection of every definition. |
| F28 HAZARD | A corrigendum title identifies the exact corrected theorem and dependencies. | PW-REGEX25 is still metadata-only. Obtain the repair text. | A scoped downstream audit once the correction is understood. |
| F29 HAZARD | A local lemma counterexample disproves the source's final theorem. | PW-PRI04. Track dependency uses and possible repairs separately. | Alternative proofs or restricted repaired statements. |
| F30 HAZARD | A syntactically excluded example proves novelty; no search hit proves priority. | [novelty matrix](novelty-matrix.md) and [coverage log](search-log.md). Check equivalent encodings and unsearched sources. | A documented non-subsumption argument and external review. |
| F31 HAZARD | Many green checks, agreeing agents or checked local lemmas close a missing global implication. | Current [AGENTS](../../AGENTS.md), [STATE](../../STATE.md). List exact discharged obligations and review independence. | Genuine proof progress, without using activity counts as evidence. |
| F32 HAZARD | A stale snapshot may replace active proof files or all work is saved because remote branches are clean. | Issues #36/#37 and [AGENTS](../../AGENTS.md). Compare current blobs and obtain workspace checkpoint reports. | Narrow non-forced integration of the explicitly handed-off contribution. |

| F33 HAZARD | A safe reachable cycle is enough to satisfy InfWitness. | C031 and the current subtype split retain an original Witness in addition to a safe stem and cycle. | Prove a method to eliminate every earlier flagged comparison, as required by C029. |
| F34 HAZARD | Equal infinite words permit moving a cut without checking ordered flags. | PW-BLLS25 saturation concerns representation-invariant acceptance; BorderAvoid retains distinguished finite positions and states. | An explicit phase-aware, flag-preserving representation theorem. |

## How to add a failure

Give the exact statement under attack, status, all preserved hypotheses, smallest known input, independent predicate/check, source and immutable evidence reference. State what the example does **not** refute. Do not turn a universal-profile counterexample into a refutation of a weaker existential replacement statement. Link a new mathematical result through the repository's canonical C/A/E/Q process when warranted; this catalogue does not create such a result by itself.
