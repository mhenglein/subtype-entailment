# Research plan

Updated: 2026-09-20 (post-C081 research package)

**Completed qualitative goal:** decide [Problem 1.7](problem.md) for bottom
and binary product over arbitrary, possibly infinite trees. [C081](claims.md#c081)
gives the total executable Boolean and unconditional correctness theorem.
[Source pins and validation](../notes/2026-09-19-entailment-decision.md).

## Post-C081 results and next questions

The [seven-part programme](POST_C081.md) now has a full ordinary paper,
focused novelty review, explicit input resource account, small usable solver
with a proved evaluation gate, extension study and reader checkpoint.
C082 supplies a corrected quantitative bound; C083 gives an elementary NL
lower bound. The original concrete C080 U is refuted, while its F alone and
an existential smaller compiler remain open. No issue closure changes that.

The next discriminating tasks are:

1. Prove and measure caching or a smaller representation for balanced/summary
   reachability. Use the matched E054 cases and preserve UNKNOWN.
2. Turn the ordinary regular-countermodel construction into a complete
   finite-graph extractor with an independent exact checker.
3. Narrow the large gap between the explicit reference upper bound and NL
   hardness. Prove each literature transfer under the exact signature.
4. Obtain outside mathematical review of the terminal coverage/reconstruction
   and the claimed novelty. The current reviews are agent source readbacks.
5. Investigate explicit top with labelled semantics; the tested naive encodings
   fail. New arities, constructors and variance need separate arguments.

These are proposals, not active worker assignments. Ownership and reservations
remain in [the registry](approaches.json), [#53](https://github.com/mhenglein/subtail/issues/53)
and [#37](https://github.com/mhenglein/subtail/issues/37). The owner deferred
licensing and requested author/affiliation placeholders. No license grant or
publication-ready authorship is asserted.

The original programme below is historical. Its open qualitative status is
superseded only for the exact checked semantics.

## Earlier mathematical continuation: single-source capture (2026-09-09)

C067/C068 now provide a written single-source decision and exact bounded-source
word-equation compilation; independent mathematical review is pending. The
single-source root-pumping task below is superseded as a route to deciding that
subclass, not proved by the new result. Use the
[source-capture argument](../notes/2026-09-09-source-capture-word-equations.md)
as the current end-to-end outline. First audit capture uniqueness, boundary
cases, one-visit normalization and the exact external free-monoid theorem.
Then attack [Q004](conjectures/Q004.md): control repeated interacting sources
or produce a complete shared-word symbolic cover. For the opposing route,
seek an encoding genuinely outside the now-decidable bounded-source setting.
No general SEP decision or computable source-visit bound is claimed.

## Current research priorities (2026-09-09)

This is an organizational change following collaborator feedback, not a new
proof, experiment, or change to the decidability status. The operating rules
are in [AGENTS.md](../AGENTS.md); ownership and execution status remain solely in
[approaches.json](approaches.json). No investigator is assigned by this plan.

### The target, not a stronger substitute

Keep terminal-final BorderAvoid as the principal mathematical testing ground,
using the recorded C030/C031 bridge at its stated evidence level. The leading
constructive hypothesis is an existence-preserving normalization, an effective
finite symbolic cover, or another terminating exact procedure. A witness-bound
route would suffice if it establishes

```text
there exists a total computable F such that, for every finite binary
terminal instance I with k states,
    (there exists w with Witness_I(w))
    implies (there exists v with Witness_I(v) and |v| <= F(k)).
```

Here `Witness_I` is the exact existing predicate, including Bad states,
diagonal flags and the empty suffix; see [the problem](problem.md) and
[the checked binary definition](../lean/Subtail/Basic.lean). This is an
existential target, not a claim that every candidate can be shortened, that
all agreement profiles can be preserved, or that the witness language is
regular. Q002/Q003 and the modular family already refute several stronger
substitutes. A new proposal must survive those examples without assuming its
missing completeness or termination argument.

The single-source case remains a focused subproblem, not an automatic route
through the multi-source case. The current root-length and new-border
obligations are in the [single-source handoff](../notes/2026-09-08-strategy-review-and-period-state-form.md).
C042 rules out a source-wise viability shortcut. The [overlap audit](../notes/2026-09-09-overlap-deletion-audit.md)
repairs selected-equality preservation, not full witnesshood or a global bound.

### Two hypotheses, forward and backward

| Hypothesis | Forward from existing evidence | Backward from the final conclusion |
|---|---|---|
| SEP is decidable | Combine normalization, arithmetic and shared-word tools into an existence-preserving invariant. | State exactly what effective bound, complete finite cover, or terminating exact procedure would finish the reduction. |
| SEP is undecidable | Test whether recurrent copying and shared-word interactions enforce transformations or computation steps. | Start with a named undecidable source problem; specify the finite encoding and both directions of correctness in our exact terminal fragment. |

An obstruction in either row must yield a question for the other row. The
constructive route remains the lead hypothesis, not a presumption of the
answer. Block equality, nonregularity, a failed pump, or an undecidable more
expressive relation is not by itself an undecidability reduction here. A
failed encoding only rules out its stated gadget or construction class unless
a broader impossibility theorem is proved.

### Next research cycle: concrete handoffs

Use one [end-to-end outline](../templates/proof-outline.md) per route, with all
open implications named, before investing heavily in supporting machinery.
A short falsification attempt can start immediately. The next assignments are:

1. **Constructive and adversarial pair — A017/A008, with A016 support.** Choose
   one replacement or finite-cover obligation. For the single-source root
   pump, test the complete witness predicate after alignment-compatible
   deletion, including new borders and primitivity; acceptance and selected
   equality checks are not enough. Minimize counterexamples while preserving
   the exact hypotheses. Explain how a surviving restricted lemma enters the
   general outline, rather than assuming different sources compose.
2. **Opposing investigation — A011.** Use the terminal converse to test a
   specific computation/word-transformation gadget. Write both implications
   of a proposed reduction and the missing gadget before building a solver.
   Return a proved encoding, a precise obstruction to that encoding class,
   or an explicitly unresolved obligation; feed the structural finding back
   to A017/A012. This is a real research target, not a token negative route.
3. **Coverage and critical review — A012, with selective A018 support.** Make
   certificate soundness, coverage of all relevant instances, and termination
   separate obligations. Audit exact construction definitions and critical
   transfers in the leading outlines. New Lean work must resolve a specific
   uncertainty or verify a stable critical dependency; maintain existing
   checks without automatically extending the conditional framework.

These are proposed handoffs, not reports of launched agents or completed
research. Separate contexts may run sequentially or in parallel. Use an
independent first attempt where useful, exchange checkable artifacts, and
compare results surviving review per unit of effort. Different model families
may diversify search but do not establish independence or correctness.

### Review and stopping rules

The default order is conceptual sketch, targeted falsification, precise
ordinary proof, independent mathematical review, then selective formalization;
iterate when a test or review exposes a gap. Exact definitions and openly
labelled assumptions are required at every stage. Keep failed arguments and
small counterexamples, and distinguish a local repair from the missing global
existence/coverage theorem. Report which obligations were discharged, not how
many lemmas remain or how close a result feels. A strategy-only update must
not promote evidence labels, mark unperformed work active, or claim new checks.

## September 4 starting order (historical)

This programme predates C021–C045 and Q001–Q003. Some targets below have since
been completed or refuted. Use [current shared memory](../STATE.md),
[the tracker](README.md), and [conjecture records](conjectures/README.md)
to select work; keep the original programme below as research history.

The Lean direct budget predicates and actual subtype summary bridge now
exist. The two-state abstract case is decided. A new six-state example has
exact budget five versus boundary-only budget one. Focus angles 1 and 2 on
minimizing and generalizing that proper-border obstruction. Use actual bridge
outputs for angle 4.
In angle 11, the remaining O4 work is the exact finite automaton for word
existence; the direct sufficient predicate is already proved sound.

Use those results to choose between structural proofs in angles 4–7 and complete certificates or saturation in angles 8–9. Keep the converse and negative-result investigation in angle 10 separate. [A007](approaches/A007.md) is retired by the owner's decision of 2026-09-19: assume the original sources will not arrive and make no further source requests. The original census remains unreproduced; independent proposals use their own recorded evidence.

## Eleven angles (historical programme)

### 1. Find the structure of shortest witnesses — A008

Enumerate small instances, find shortest witnesses, and record why every stronger truncation rule fails. Look for a recurring obstruction involving suffixes, states, and flags. An exhaustive search through the first successful length proves shortestness for that instance; merely applying cuts gives only a witness irreducible under those cuts.

**Target:** a computable bound on the smallest successful budget, as in [C012](claims.md#c012). The target concerns minimal witnesses, since the universal rigid-word bound was refuted. [Approach record](approaches/A008.md).

### 2. Search for instances that defeat candidate bounds — A009

Generate and mutate automata to maximize the minimum successful budget B.
The [six-state budget-five example](claims.md#c020) already exceeds
`max(0,|K|-2)`, the tight bound for the certified regular subclass. Next seek
`B>|K|` or generalize the example into a proved growth family. Trim irrelevant
states and compare with full final-state boundary slices. Simply removing
flags leaves empty-suffix effects mixed with proper borders. Exhaust every
lower budget before claiming an exact B.

**Target:** a family with a proved lower bound or sharper evidence for an upper-bound conjecture. Finite examples alone establish neither asymptotic growth nor a general upper bound. [Approach record](approaches/A009.md).

### 3. Build the exact subtype-to-countermodel bridge — A010

Implement normalization, pushdown summaries, forced roots, and denial conditions. Generate small constraint systems and validate produced regular countermodels by exact automata operations against the original constraints.

**Target:** an experimental pipeline for Problem 1.7 itself and realistic inputs for angles 1, 2, and 4. Finite-depth model checks are insufficient. [Approach record](approaches/A010.md).

### 4. Exploit structure shared by summaries of one constraint system — A013

Compare bridge outputs with arbitrary BorderAvoid instances. Search for restrictions on transitions, reachable state pairs, or summary composition, then prove a candidate invariant from the same underlying pushdown system W.

**Target:** a decidable subclass containing every subtype-derived instance. The intersection-shaped representation of G alone imposes no restriction. [Approach record](approaches/A013.md).

### 5. Strengthen truncation using occurrence context — A015

Try comparing incoming flags only at states visited in the retained prefix, then at positions relevant to each repeated suffix. Test each precisely stated relaxation against the independent witness predicate and minimize failures.

**Target:** a stronger shortening lemma and a smaller class of resistant witnesses. The starting points are [C008](claims.md#c008) and [C009](claims.md#c009). [Approach record](approaches/A015.md).

### 6. Turn fixed-skeleton checkability into a checked solver — A016

Audit and implement the memo's Proposition 7.5, starting with words s u^k t and then two interacting repeated blocks. Express valid exponent choices in Presburger arithmetic, which allows addition, order, and quantifiers over integers. Check the translation against direct word predicates.

**Target:** a dependable solver for the stated restricted class. Then cover automata whose recurrent components are simple cycles by enumerating their finitely many path skeletons. The memo already claims fixed-skeleton checkability; implementation and audit are the proposed work. [Approach record](approaches/A016.md).

### 7. Bound the number of essential repeated blocks — A017

Study whether witnesses admit a bounded skeleton using the automaton's finite transition structure. First try deleting repeated blocks while tracking every new border crossing the deletion boundary. Bounded-height [factorization forests](https://arxiv.org/abs/0710.5130) are a possible tool; their height bound alone gives no bounded witness skeleton.

**Target:** an effective normalization theorem that extends angle 6 to a complete procedure. Preserving states must also preserve every border obligation. [Approach record](approaches/A017.md).

### 8. Make nonexistence certificates complete — A012

Build finite approximations of permitted reversed prefixes. Merge summaries only under a proved relation covering every relevant continuation. Refine when a candidate produced by the approximation is spurious.

**Target:** finite certificates that no witness exists, with a termination theorem for every such instance. Failure to find a witness within a chosen budget remains UNKNOWN. [Approach record](approaches/A012.md).

### 9. Test effective saturation of periodic-cap languages — A014

Annotate periods with endpoint states and flags. Test their behavior under powers, primitive roots, and rotation. The [2025 automata-saturation results](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2025.146) offer adjacent techniques, but require a transfer argument for our finite borders.

**Target:** a finite representation of the relevant periodic behavior. First produce an exact closure lemma or a minimal obstruction preserving Fin, Bad, and G. [Approach record](approaches/A014.md).

### 10. Complete the converse and explore a negative result — A011

Try encoding arbitrary BorderAvoid instances into subtype constraints while preserving regular side restrictions. Begin with small filters and prove both directions. If the encoding succeeds, investigate whether flagged borders can enforce copying or computation steps.

**Target:** clarify the expressive power of the exact subtype problem. An abstract undecidability result transfers only through a valid converse or a direct encoding into actual subtype-derived instances. The converse is not required for the upper-bound approaches. [Approach record](approaches/A011.md).

### 11. Work backwards from an executable Lean theorem — A018

State a terminating algorithm on finite subtype inputs and a theorem that its Boolean answer equals entailment over the memo's arbitrary-tree semantics. Work backwards through the conditional route:

**Executable witness-budget bound → complete finite search → BorderAvoid decision procedure → subtype decision procedure.**

Start with finite words and the witness definition, then formalize the suffix-trace and flag-profile lemmas. Prove the finite-search implication with the missing bound and unfinished reduction interfaces exposed as hypotheses. Record the fixed-budget automata's correctness as its own obligation; a bound on L+D is not a bound on word length.

**Target:** a small, checked core that turns unresolved mathematics into precise obligations and directs Python counterexample searches. A failed proof attempt should record the target, hypotheses, and whether the obstacle is mathematical or Lean bookkeeping. A classical, noncomputable Decidable instance does not provide the required executable algorithm. The [detailed workstream](approaches/A018.md) specifies the semantics, milestones, dependency checks, and acceptance criteria.

## Collaboration and evidence

Astra can lead proof design and integration. Independent agents can audit one exact lemma, minimize a counterexample, check an implementation, or formalize a bounded obligation. GLM support is optional; no model-specific claim of solving the open problem is justified by the current evidence.

For each attempt, record its A ID, exact statement, assumptions, input coverage, seed or proof command, resource limits, result, and smallest useful obstruction. Keep written proofs, Lean-checked statements, bounded evidence, and conjectures distinct. A Lean theorem with an explicit bound hypothesis establishes a conditional implication, while the bound itself remains a separate research obligation.
