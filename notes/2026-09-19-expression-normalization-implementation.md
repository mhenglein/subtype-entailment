# Executable finite-expression normalization and exact semantic regressions

Date: 2026-09-19. Actor: ChatGPT `expression-normalization-implementation-20260919`.
Workstreams A010/A018; normalization in #31; parent #34; coordination #37.
Base commit: `3ce7cf18899ad24a5562d4b614f738bec8bc8427`.

**Delivered:** executable occurrence-based finite-expression normalizer, an
explicit model-extension evaluator, and independently evaluated model-correspondence
regressions. **Not delivered:** a Lean normalizer/proof or full subtype decision.
The normalization obligation is now implemented and tested in Python; its
kernel-checked allocation and model-preservation theorem remains open.

This follows the released [ordinary normalization advisory](https://github.com/mhenglein/subtail/blob/c33d0c8d65158fc7ba53e5bc24c14132f071dc42/notes/2026-09-19-finite-expression-normalization-advisory.md)
in PR #45, not a new discovery of conservative naming. It also follows the
[end-to-end audit](https://github.com/mhenglein/subtail/blob/99d951077ace1c93d0fec604839674fb3f19dbc9/notes/2026-09-19-end-to-end-semantic-audit.md)
in PR #44. Neither advisory PR is implicitly merged by this contribution.

The existing [TreeSemantics](https://github.com/mhenglein/subtail/blob/3ce7cf18899ad24a5562d4b614f738bec8bc8427/lean/Subtail/TreeSemantics.lean)
interfaces remain the target: arbitrary prefix-closed product-node predicates,
bottom, one covariant binary product, and the four normalized constraints.
No existing source, proof, ledger, import aggregator, workflow, or toolchain is
changed. C029 completion and the separate U/F investigation are excluded.

## 1. Files and actual evidence

- [Normalizer and extension evaluator](../experiments/expression_normalization.py).
- [Independent semantic checker](../experiments/check_expression_normalization.py).
- [Recorded results and source hashes](../results/expression-normalization.json).

The checker ran locally on Python 3.13.5 / Linux / x86_64, seed 2026091931.
Final code was replayed with PYTHONHASHSEED=1 and 73; the result JSON files
were byte-identical. Python AST parsing, JSON parsing, and source whitespace
checks passed. The checks below are actual executions, not proposed fixtures.

| Executed check | Scope / count |
|---|---|
| Exhaustive small input syntax | 1,352 systems: n=0 or 1, bottom/variable leaves and one product over leaves, every query, zero or one premise |
| Structural allocation/count/serialization checks | 1,603 systems including 250 seeded inputs and the deep-input stress case |
| Original valuation extensions | 10,600 checks, whether or not the original premises hold |
| All normalized assignments in the stated tiny domain | 112,880 assignments across 587 systems with at most four output variables |
| Total normalized-valuation model-correspondence checks | 115,340, including the exhaustive assignments, seeded extensions, and 1,210 fresh-value mutations |
| Definition models among these checked valuations | 2,401; the exact representative/uniqueness checks apply to all of them |
| Fixed-address membership/nonmembership comparisons | 38,936, at all binary addresses of length at most four in the selected cases |
| Adversarial groups | Nine, detailed below |
| Deep syntax stress | 10,000 nested products, iterative allocation and algebra evaluation |
| Malformed inputs | 14 rejected examples; CLI error handling separately checked |
| CLI | Three JSON round trips and one invalid-input exit-code check |

There is no general negative entailment/satisfiability verdict inferred from
these enumerations. The syntax and valuation domains are bounded tests.
Individual inclusion tests on the represented regular trees are exact and
unbounded in address length. That distinction is essential.

**NOT RUN:** Lean/Lake build, kernel replay, declaration axiom/dependency audit,
the existing full repository Python suite, or a full original-PDF readback.
The local container has no Lean/Lake executable; direct toolchain retrieval
failed DNS, and the alternative binary download route did not produce a
usable download. These are environment limitations, not a failed Lean proof.
No uncompiled Lean module is presented as certification. Remote PR checks,
when observed, are recorded separately in the commit-pinned issue handoff.

## 2. Input and output contract

### Finite expressions, not finite types

An input declares a finite old-variable domain `Fin n`, including query-only
and otherwise unused original variables. Its syntax is a topologically ordered
node table. A row is exactly one of:

```json
{"op": "var", "var": 0}
{"op": "bottom"}
{"op": "product", "left": 0, "right": 1}
```

Every product child refers to an EARLIER row; each variable index lies below n.
Premises and the query are pairs of node indices. All finite expressions over
variables, bottom and product have such an encoding, by a postorder traversal.
Shared table entries are allowed, but each use is a separate syntax occurrence
for allocation. A cycle in the syntax table is rejected. Recursive CONSTRAINTS
such as `x * bottom <= x` are accepted: old variable values may be infinite.

The flat table avoids a Python recursion limit on nested expression traversal.
Unused rows are validated but generate no definitions; in particular, an unused
bottom row does not cause allocation. There are no depth, solver, or search caps
in normalization. As with any implementation, practical memory is finite.

The output contains the old and enlarged variable counts, `definitions`,
translated `premises`, a separate variable `query`, and a postorder `bindings`
list. Clause argument order is precisely the existing Lean constructor order:

```text
leq(source, target)
upper(source, left, right)
lower(left, right, target)
denial(source)
```

Old indices are unchanged numerically. Fresh indices are contiguous starting
at n. The query comparison is never included among the premises.

### Reproducible example

This input has the premise `x * bottom <= x` and query `x <= bottom`:

```json
{
  "variables": 1,
  "nodes": [
    {"op": "var", "var": 0},
    {"op": "bottom"},
    {"op": "product", "left": 0, "right": 1}
  ],
  "premises": [[2, 0]],
  "query": [0, 1]
}
```

The normalized constraint list is:

```text
[denial, 1]
[upper, 2, 0, 1]
[lower, 0, 1, 2]
[leq, 2, 0]
```

The output query remains `(0,1)`. The exact infinite zero-spine model assigns
the same zero-spine to variables 0 and 2 and bottom to variable 1. It satisfies
the premises and separates at the empty address. The checker executes this case.
No finite type can satisfy the original premise: it forces product nodes at
all addresses consisting of finitely many zeroes. That last universal statement
is the ordinary argument, not an inference from the finite test pool.

Run:

```sh
python3 experiments/expression_normalization.py input.json --output normalized.json
PYTHONDONTWRITEBYTECODE=1 python3 experiments/check_expression_normalization.py --output /tmp/expression-normalization.json
```

Omitting the normalizer input path reads stdin; omitting `--output` writes stdout.
Malformed JSON/input syntax yields an explanatory stderr message and exit code 2.
The node-table schema requires its exact keys and rejects an unknown/top constructor.

## 3. Concrete algorithm and proof invariants

This section is the route/proof readback of the IMPLEMENTED algorithm. The
mathematical construction is inherited from PR #45; the new issue is whether
allocation, field order, traversal, and the separate query implement that
construction. No finite test is substituted for the quantified argument.

Let the root forest consist of the two sides of each premise in list order,
followed by the two query sides. P counts product occurrences in this expanded
forest. B is 1 iff a bottom occurs in this forest, and 0 otherwise.

**Pass 1.** Traverse reachable node-table rows, recording visited row indices,
to decide whether bottom is used. This traversal can exploit syntax sharing
because it computes only an existential occurrence property. If B=1, reserve
old count n as the single bottom proxy and emit its denial.

**Pass 2.** Traverse each forest root with an explicit stack. For a product,
push an expanded-parent marker, then its right and left child frames; LIFO
therefore completes the left, right, and parent in that order. This pass does
NOT memoize shared products. Its value stack contains completed child names.
At the parent marker, pop right then left, allocate the next fresh index p,
and emit both `upper(p,left,right)` and `lower(left,right,p)`.

Variables push their unchanged old index. Bottom pushes the reserved bottom
index. Each root traversal finishes with exactly one name. Premise root names
are paired in their original order; the last two names are returned as the
query, not emitted as another premise.

The structural invariant is:

1. Fresh indices form exactly the contiguous allocated interval; old indices
   retain their values. Every product's children have strictly smaller indices
   than the newly allocated parent.
2. Every completed occurrence has its correct representative on the value
   stack. Its entire definitional constraint block has already been emitted.
3. The binding at an allocated product index records the corresponding original
   syntax node and forest root. Repeated occurrences receive different fresh
   indices even when the original table row is shared.
4. Every allocated variable is either the optional bottom proxy or one product
   occurrence, and has its full defining constraints. There is no unconstrained
   padding variable in the enlarged domain.

The first invariant gives acyclic evaluation of fresh definitions, even when
premise dependencies among OLD variables contain cycles. This distinction is
why the normalizer must not impose an occurs check on original constraints.

## 4. Exact ordinary model theorem for this implementation

Write D for the definitions, A for translated premises, Delta=D++A, and r(e,o)
for the name of an occurrence o of e. For an arbitrary original tree valuation
rho, `extend` retains its values and evaluates the binding list in order:

```text
bottom binding -> bottom
product binding p with children l,r -> value(l) * value(r)
```

It does not call a subtype checker, test equality, enumerate models, inspect
product-node membership, or recursively unfold an old value. Its generic
`TreeAlgebra` interface asks only for bottom and product; the following theorem
specializes those operations to the existing arbitrary-tree semantics.

### Representative correctness and unique extension

For every original rho, induction on completed occurrence frames gives:

```text
extend(rho)(r(e,o)) = eval(rho,e).
```

At a variable this is literal preservation of the old value; at bottom it is the
reserved binding; at product both children already satisfy the induction
hypothesis and the binding applies the same binary constructor. Thus the
extension satisfies every definition, independently of the original premises.

Conversely take any eta satisfying D. The denial forces its bottom proxy to
be the empty product-node set. At every product occurrence, the two inclusions
force its proxy to equal the product of its children by antisymmetry. Structural
induction gives:

```text
eta(r(e,o)) = eval(restrict(eta),e).
```

Because every fresh index is accounted for, eta equals the binding-list
extension of its restriction. This proves the stronger definitions-only fact:

```text
for every rho, there exists exactly one eta such that
  restrict(eta) = rho and Models(D,eta).
```

This is uniqueness of trees as node predicates, not equality of their graph
presentations. The checker correctly uses semantic equality when different
finite graphs denote the same infinite tree.

### Models, entailment, and fixed separating addresses

For every normalized valuation eta, the exact characterization is:

```text
Models(Delta,eta)
  iff eta = extend(restrict(eta)) and ModelsOriginal(Gamma,restrict(eta)).
```

Proof: definitions force the equality just proved; every translated premise
is then precisely the inclusion between the evaluations of its original sides.
In the reverse direction, the canonical extension satisfies D and transports
all original premises. In particular every original model extends, every
normalized model restricts, and satisfiability is equivalent without a
consistency premise. The checker directly tests this equivalence, not only
a comparison of two satisfiability verdicts.

Apply the same representative equality to the two query roots. Universal
quantification over the corresponding model classes proves:

```text
ExprEntails Gamma s t iff Entails Delta leftRoot rightRoot.
```

For each fixed finite address w, extension and restriction preserve membership
in the left query value and nonmembership in the right query value at THAT w.
Hence the existential separating-model equivalence holds word by word, without
transforming w or assuming a witness bound. Inconsistent premises remain
inconsistent on both sides and entail every query vacuously.

No part of these arguments assumes that old values are finite, regular,
decidably presented, or computably enumerable. Only expression syntax is finite.
The executed examples use regular values for exact evaluability; they do not
restrict the ordinary theorem's model quantifiers.

## 5. Counts, termination, and implementation boundaries

The implementation allocates exactly P+B fresh variables and emits exactly
2P+B definitions plus m translated premises. The total variable count is n+P+B;
the total constraint-list length is m+2P+B. The query's expression occurrences
contribute to P and B, but its comparison is not an additional premise.

This count is over the expanded occurrence forest, NOT the compressed node-table
size. A compact DAG may encode exponentially many tree occurrences. The reference
normalizer intentionally follows the occurrence-based advisory rather than
silently substituting a sharing optimization; no polynomial compressed-input
runtime claim is made. A later shared-DAG normalizer needs its own refinement proof.

Both passes terminate on a finite acyclic node table. Pass 1 visits finitely many
rows. Pass 2 uses finite unfolding of those acyclic references; the postorder
frames recurse only into strictly earlier node indices. The extension evaluator
iterates over a finite binding list. There is no SAT branch, solver cap, classical
choice, or search for an unsupplied word in runtime normalization.

Python normal forms are a documented finite encoding of the existing Lean forms.
This contribution does not introduce a parser into the Lean library, compile the
Python code to Lean, or certify its allocator in Lean. Formal semantic fidelity
of the future Lean implementation must still be proved against the unchanged
`TreeSemantics` declarations.

## 6. Independent semantic oracle and adversarial tests

The checker evaluates ORIGINAL input nodes topologically, separately from the
normalizer's occurrence traversal and from its binding-list extension evaluator.
It interprets normalized clauses directly according to all four constructor
signatures, not by assuming the supplied bindings are sound.

Its test values are states of a finite graph whose nodes are bottom or a pair
of successor states. Cycles are allowed. A finite binary word is a product address
iff following the word ends at a product state without first passing bottom.
All resulting product sets are prefix-closed and may be infinite.

To decide inclusion of two graph-denoted trees, exhaust reachable pairs of
states. A left product with right bottom is a finite counterexample; left bottom
is harmless; two products generate their paired children. Exhaustion with no
violation proves inclusion for all addresses of those graph-denoted values.
Termination follows from the finite product of reachable state sets. The test
does not truncate trees to depth four: depth four is only a separate membership
regression horizon. Inclusion/equality and model checking are exact for each
represented regular valuation.

The exhaustive old-value pool is bottom, unit product, left-unit, right-unit,
both-unit, infinite zero-spine, and infinite full tree. Exhaustive normalized
valuations use bottom, unit, zero-spine, and full tree when the output has at most
four variables. Seeded inputs add arbitrary small cyclic graph values.

Nine adversarial groups retain the advisory's hazards:

1. Nested products and repeated subexpressions: separate product occurrences,
   exact P+B / m+2P+B counts, equal semantic interpretations.
2. Delete a LOWER definition: the inconsistent `bottom*bottom <= bottom`
   incorrectly admits all-bottom. The unmodified output rejects this model.
3. Delete an UPPER definition: an oversized proxy admits an original valuation
   violating `x <= bottom*bottom`. The unmodified output rejects it.
4. Query-only old variable and numeric freshness: its value and index survive;
   the bottom proxy is allocated outside the original range.
5. Recursive original premise with an exact infinite zero-spine model; the
   queried inclusion fails at epsilon, rather than being declared vacuously true.
6. Empty premises and a false compound query: query definitions are satisfiable,
   while the query comparison itself is not inserted as an assumption.
7. No bottom/product, repeated variables, and unused declared old variables:
   zero extra variables, identity original query indices.
8. Zero original variables with constant queries and shared DAG rows whose
   repeated product occurrences are deliberately expanded.
9. Unused bottom rows and 10,000-product depth: no spurious proxy and no recursion
   ceiling in the compiler or its extension evaluation.

The scalar deep-input algebra is a traversal/allocation stress check, not an
additional arbitrary-tree proof. Mutation tests and model checks are same-session
validation, not a separate human or blind-agent review.

## 7. Reproduction and exact handoff

Final source SHA-256 values are included in the result JSON. Reproduce locally:

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=1 python3 experiments/check_expression_normalization.py --output /tmp/normalization-a.json
PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=73 python3 experiments/check_expression_normalization.py --output /tmp/normalization-b.json
cmp /tmp/normalization-a.json /tmp/normalization-b.json
```

On a different Python/platform the environment fields may differ from the
committed record; compare the semantic counts, scope, seed and source hashes
separately. No timings or nondeterministic ordering are part of this result.
Tests write only the explicitly requested output file. They do not contact GitHub
or change any source, shared state, or existing stored experimental evidence.

Scope was announced in [#31](https://github.com/mhenglein/subtail/issues/31#issuecomment-5742920005)
and [#37](https://github.com/mhenglein/subtail/issues/37#issuecomment-5742926577).
Only the four new paths in section 1 and this note are owned. The final issue/PR
handoff records publication SHA, remote blob readback, observed CI, and release
of this scope. Other workers' unpushed work/stashes/worktrees were not inspected;
no main integration or other branch retirement is performed by this session.

### Remaining formal work and integrator proposals

The next normalization deliverable is a Lean implementation with a checked
allocation invariant and the exact model theorem above. Use the stable interface
proposals in PR #45 (normalize, extend, restrict, roots_correct,
normalize_entails_iff, variable_query_preserved), or explicitly agree a replacement.
An executable Python implementation and a finite test suite are not that theorem.
A future Lean regression can compare serialized outputs against this reference
and must separately audit runtime dependency closures and arbitrary-tree semantics.

The C029 owner should continue its disjoint monitor proof. Full subtype assembly
still needs the certified infinite checker, certified syntax normalization, and
one final original-language correctness theorem. Do not make the independent
U/F bound or C030 converse prerequisites of the qualitative forward decision.

For serialized integration, add a link in A010/A018, the normalization section of
#31, and the experiment registry, with wording such as:

> Finite-expression normalization now has the occurrence-based executable Python
> reference and exact regular-tree model-correspondence regressions. Its ordinary
> proof is preserved in the advisory and implementation readback. Lean allocation,
> model transfer, and final executable entailment composition remain open.

Do not upgrade the mathematical evidence label to LEAN or claim that Problem 1.7
is solved. The current parent integrator owns shared ledgers/imports/workflows;
this contribution supplies proposed wording rather than overwriting them.
