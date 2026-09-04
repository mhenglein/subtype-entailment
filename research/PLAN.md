# Research plan

Updated: 2026-09-04

**Goal:** decide [Problem 1.7](problem.md) for bottom and binary product over arbitrary, possibly infinite trees. No general solution is established here.

This plan preserves the ten research angles and adds working backwards from a
Lean theorem as angle 11. Current execution status, owners, evidence, and next
steps live in the [research tracker](README.md). The entries describe each
investigation's target; dated approach records distinguish proposals from
executed attempts.

## Recommended starting order

The Lean direct budget predicates and actual subtype summary bridge now
exist. The two-state abstract case is decided. A new six-state example has
exact budget five versus boundary-only budget one. Focus angles 1 and 2 on
minimizing and generalizing that proper-border obstruction. Use actual bridge
outputs for angle 4.
In angle 11, the remaining O4 work is the exact finite automaton for word
existence; the direct sufficient predicate is already proved sound.

Use those results to choose between structural proofs in angles 4–7 and complete certificates or saturation in angles 8–9. Keep the converse and negative-result investigation in angle 10 separate. Reproducing the original memo's sources remains [A007](approaches/A007.md); the missing files do not block the independent proposals here.

## Eleven angles

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
