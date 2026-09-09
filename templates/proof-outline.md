# End-to-end research outline

Date / author:
Approach and existing claim/conjecture IDs:
Base commit:
Status: exploratory outline / ordinary proof / reviewed proof (choose one).

Keep this short and reuse it across related attempts. Exact definitions and
visible gaps matter more than length. This is not a requirement to formalize
an unfinished idea or to delay an inexpensive falsification test.

## Exact input and intended conclusion

State the finite input, constructors, tree semantics and quantifiers. Is the
conclusion a general decision, a restricted theorem, a counterexample, or an
encoding? Define witnesshood by reference to its exact canonical predicate.
For a restricted result, explain its proposed contribution to the general
problem and name the missing extension; do not assume composition.

## Objects and construction contracts

Define all symbols before use. For an automaton give the actual state set,
alphabet, transition function/relation, initial configuration and accepting
states or output condition. Define missing-transition behavior and the run
invariant. Explain effective construction and finiteness from the input; do
not hide arbitrary histories or trees inside a supposedly finite state.
Preserve shared assignments when multiple comparisons concern the same word.

## Route from start to finish

Write the complete proposed chain of implications in ordinary mathematics.
Label each link as recorded evidence, a proved step in this attempt, or a
named open obligation. An intuitive idea may motivate a gap but cannot
silently discharge it. State the exact theorem and assumption mapping for
any imported result. For a reduction give both implications and effectiveness;
for a decision procedure separate soundness, completeness and termination.

## Necessary target versus convenient strengthening

State the weakest result sufficient for the route. Identify any extra demands
such as preserving every candidate, all agreement profiles, or all accepted
words rather than some witness. A failure of the stronger statement is not a
failure of the weaker one. For transformations separately address acceptance,
selected equalities and cut states, full witnesshood including new forbidden
comparisons, and availability/coverage of the transformation at the global scale.

## Most discriminating falsification

Name the precise hypothesis, existing regressions, adversarial input family,
independent predicate, bounds and minimization invariants. Include overlapping
occurrences and boundary cases when in scope. An arbitrary accepted-word
counterexample need not refute a shortest-witness statement. Bounded failure
is UNKNOWN unless a separate completeness proof covers the entire search.

## Opposing route and next decision

What does success or failure suggest for the other decidability hypothesis?
Which observation would change the preferred route? For a proposed negative
encoding distinguish word equality from a transformation/computation gadget;
an obstruction only rules out its proved construction class.

## Review and formalization

List what has actually been independently reviewed, by whom or by which
independent algorithm, and what remains unaudited. Distinguish mathematical
review, software checks and Lean verification. Identify a specific uncertainty
or stable critical dependency before proposing new formalization; otherwise
leave it deferred while maintaining existing checks. End with the one next
mathematical obligation, not a claim that few remaining steps imply closeness.
