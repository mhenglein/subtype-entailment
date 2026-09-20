# Complete regular countermodels and checked certificates

Date / author: 2026-09-20, countermodels-20260920. A010/A018, C081, #57/#37.
Base: `25e5c124d4fc1dc3c31bcf13ab1b420d835c8639`.
Status: implementation route; ordinary completeness and new certificate proof
require the validation recorded below before release.

## Exact target

For a finite original expression input over bottom and one covariant binary
product, with arbitrary-tree non-entailment, compute a finite directed graph
whose unfolding satisfies every premise and falsifies the query at a supplied
finite address. No finite-tree hypothesis is made. A resource cap returns
UNKNOWN for extraction; it cannot retract a completed C081 decision.

## Construction and route

1. Name each distinct expression subterm, with both product inequalities for
   each product name, and a denial for the bottom name. Original variable
   indices stay fixed. This is an ordinary exact definitional normalization;
   it need not duplicate Lean's occurrence table. Model restriction and unique
   expression evaluation prove both directions. The original-input checker
   must validate the returned graph independently.
2. Form the finite epsilon/push/pop system W from normalized constraints.
   Compute its least balanced relation by reflexive/epsilon initialization,
   composition and matching push/balanced/pop closure. The finite pair carrier
   proves termination. Reverse W by swapping each rule's direction and
   exchanging pushes with pops; compute its balanced relation too.
3. For each proposed address w, seed forced roots and every alpha-prefix of w.
   For every seed (p,u), every cut i, and each r in Pop_W(p,u[:i]), attach the
   fixed suffix u[i:] to r in the reverse-pop NFA. Its controls are W's states;
   balanced reverse pairs are epsilon edges and reverse pops are letter edges.
   Suffix states are disjoint from controls, accept only the empty remaining
   suffix, and never return to controls. From initial q the exact language is
   the union of L(q,r) followed by u[i:]. The suffix is on the RIGHT.
4. Minimum-stack factorization (existing checked StackReachability theorem;
   ordinary manuscript Proposition 12.2) identifies this language with the
   full canonical closure. Forced roots plus prefix seeds make it prefix-closed.
   Test denials by finite NFA reachability to a final state, and test that beta
   does not accept w. These are exact finite tests, not bounded stack search.
5. Enumerate finite binary addresses fairly. C081-negative input supplies some
   separating address, so one test eventually succeeds. Determinize only that
   NFA. Each reachable accepting subset is a product node, rejecting subsets
   map to bottom, and the two successors follow 0/1. Prefix closure ensures a
   rejected prefix cannot acquire an accepted extension. Restrict to original
   variable roots. This terminates and yields the promised countermodel.
6. Verify original premises and query failure using the independent finite
   pair-graph checker. A new Lean certificate checker will discharge its own
   soundness statement against ExprEntails. Python normalization, NFA extraction,
   JSON and process boundaries are not silently promoted into Lean proofs.

## Weakest obligation and falsification

We need one countermodel for a negative input, not a minimal graph or preservation
of all possible countermodels. Check root/empty cases, zero variables, bottom
names, repeated subexpressions, both stack directions, shared suffixes, denial
propagation, recursive alternating spines, and separators beyond the former
five-shape library. Compare NFA word acceptance with explicit finite closures
where a bound is justified, and independent direct graph checking everywhere.
A finite word cap is UNKNOWN even if every tested word fails.

## Review and remaining proof boundary

The ordinary regular-language route already appears in the reviewed manuscript.
A separate read-only reviewer will inspect the present construction and code.
The Lean worker owns only a new certificate module, not the canonical core.
The specific formalization target is certificate soundness for original finite
expressions; a fully Lean-verified regular-language extractor remains separate
unless its entire construction is actually checked. The opposing undecidability
route is already excluded for C081's exact signature, not for its extensions.
