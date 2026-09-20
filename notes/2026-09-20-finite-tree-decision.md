# Completing the executable finite-tree decision

Date/session: 2026-09-20, finite-decision-20260920. C085, A010/A018; #58/#37.
Base: 52e790fb7360ec676ca76f5a391c9a35375a912b.
Status: exact implementation refinement of the independently reviewed C085
ordinary proof. Formal obligations below are not assumed discharged.

## Finish line and retained semantics

For every finite `G : ExpressionNormalization.Input n` and expressions s,t,
define a total executable Boolean whose true result is equivalent to
`FiniteTreeReduction.FiniteExprEntails G s t`. Finite trees use the existing
address-length-bound predicate. No SAT, supplied growth classification,
word-length bound or regularity hypothesis may remain on the final theorem.
JSON parsing, source emission and graph certificate checking remain separate.
Do not change C081, C084, normalized constraints or the existing C085 endpoints.

## Exact finite construction

For W=systemOf(C), reuse `CanonicalReachabilityFast.prepare W`, whose `paths`
matrix already denotes reachability in the reverse-pop epsilon NFA. Its states
are Fin n; epsilon edges are Balanced(reverse W); letter-a edges p->r are
(reverse W).pop a p r, equivalently W.push a r p. For language L(q,m), initial
state q and sole accepting state m give precisely Pop(reverse W,q,w,m).

Enumerate p,r in Fin n and a in {false,true}. The growth Boolean is true iff
W.push a r p and paths[r,p] are true. Enumeration is finite. Preparation uses
the already proved terminating balanced saturation and finite reachability.
No new guessed fuel or word cutoff is introduced.

## End-to-end obligations

1. Read the cached path result back as existence of a word w with
   Pop(reverse W,r,w,p), using prepare_correct and exists_pop_iff_path.
2. A positive test yields Pop(reverse W,p,a::w,p). Since W=systemOf(C), every
   original push into p arises from a lower-product clause and makes p forced.
   Apply the existing forced_reverse_pop_loop_noFiniteModel endpoint.
3. A negative test excludes every nonempty reverse-Pop self-loop. Such a loop
   decomposes as Balanced(p,r), pop(r,a,s), Pop(s,w,p). Postcompose the latter
   Pop with Balanced(p,r) to obtain Pop(s,w,r), making the growth test true.
   This rotation handles balanced epsilon segments before the first letter.
4. In a finite n-control system with no nonempty Pop self-loop, every Pop word
   has length < n. Inductively build a list of |w|+1 boundary controls: each
   member is reachable by a consumed prefix, and repeated membership would
   yield a nonempty self-loop. The list is duplicate-free, so its length is
   at most n. This is the isolated PopAcyclic helper obligation.
5. Step 4 supplies UniformReversePopBound(systemOf C), exactly the assumption
   of finiteEntails_iff_entails_of_uniform_reverse_pop. Normalize finite inputs
   using normalize_finite_entails_iff; use the unchanged arbitrary entailment
   correctness theorem in the no-growth case. In the growth case every finite
   query holds because no finite model exists.
6. Export an unconditional Boolean theorem and route --finite-trees through
   that actual Lean function. Any reported growth/vacuity flag must come from
   the checked classifier, not an independent unverified positive fallback.

This is forward from mature C085 semantics and backward from the executable
finish line. A failed path proof would require correcting the exact graph
classification argument, not broadening the semantics. The already reviewed
ordinary finite-tree theorem rules out an undecidability route for this exact
fragment; explicit-top semantics remain outside the argument.

## Worker interface and ownership

The helper writer owns only new `lean/Subtail/PopAcyclic.lean`, namespace
`Subtail.PopAcyclic`, with proposed declaration:

```lean
theorem pop_length_lt_of_no_nonempty_loop (M : StackSummary.System n)
    (hloop : ∀ p w, StackReachability.Pop M p w p → w = [])
    {p q : Fin n} {w : Word} (h : StackReachability.Pop M p w q) :
    w.length < n
```

The parent owns the new classifier/composition module and the interface.
Existing modules are read-only. The exact agreement and releases are recorded
in #58; integration is serialized under the #37 lease.

## Validation and acceptance

Independently review the ordinary implications, then read new declarations
back against the unchanged definitions. Build and kernel-replay both optional
modules, audit every named declaration including runtime dependencies, and
check all imported executable implementations. Compare actual Lean classifier
outputs against the separate predecessor-saturation oracle, including zero
controls, epsilon cycles and balanced excursions. Exercise original finite
expressions, zero variables, query-only names, growth vacuity, cold UNSAT and
finite negative cases. Preserve UNKNOWN under time/memory limits; rejection
of infinite graphs and existing C084 certificate semantics must remain exact.

Use source-pinned receipts, isolated Lake builds, the existing core checks,
and the research index. Tests supplement the all-input proof and do not
establish it. Preserve the original C085 ordinary receipt as historical
evidence rather than relabelling it as the new formal decision result.
