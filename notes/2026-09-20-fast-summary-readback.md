# Finite saturation and cached solver: source readback

Date: 2026-09-20. A010/A018, C081; coordination #55/#37.
Reviewed source: `cf125800a9c26cb4589d4eb0bd889d6a76b1a8e5`.
This is agent source review, not external human peer review.

## Division of review

The saturation author wrote only `StackSummaryFast.lean`. The parent integrator
read that module and the imported `FiniteSearch` membership, growth and
leastness arguments. The author then independently reviewed the two
parent-authored modules. The author did not independently review their own
saturation module. Both reviewers saw the submitted arguments; this was
mathematical readback and code review, not independent rediscovery.

The [reviewer's exact handoff](https://github.com/mhenglein/subtail/issues/55#issuecomment-5746936528)
records no correctness blocker and releases the read-only scope. The parent
ran builds, kernel checks and native probes separately; the reviewer did not.
The original C081 theorem and the original terminal argument were inherited
checked dependencies, not re-proved from first principles in this review.

## Saturation readback by the integrator

`close` preserves existing pairs and adds exactly reflexive, epsilon,
composition and matching push/balanced/pop consequences. `derivable_sound`
and `iter_sound` establish inclusion in the inductive `Balanced` relation.
`FiniteSearch.addNew` preserves absence of duplicates, and a changed round
strictly increases the list's length. All pairs lie in the explicit n*n
carrier. Therefore n*n+1 rounds must produce a closed relation; the proof also
covers n=0. `balanced_least` gives the converse inclusion, and the Boolean
equality follows. No bounded stack-height search occurs. The implementation
scans the carrier per round; it does not claim an optimal queue algorithm.

The parent inspected `saturate_eq_iter`, `closed_of_fixed`, `closed_or_grow`,
`closed_saturate`, both balanced-table inclusions and the final reference
Boolean equality. Runtime list operations and both Boolean-letter cases match
the propositions used in those proofs.

## Independent review of the parent modules

The separate reviewer checked these obligations and their supporting definitions:

- Finite graph reachability: `reach_iff_path`, `pathSet`, `mem_pathSet`,
  `pathMatrix`, `lookup_pathMatrix`.
- Cache orientation and correctness: `Cache`, `Correct`, `prepare`,
  `prepare_correct`. Forward and reverse balanced relations and the reverse
  control graph match their reference uses.
- Supplied-word reachability: `nextSet_eq`, `popSet_eq`, `mem_popSet`,
  `reachesCheck_eq`, `controlReachCheck_eq`. The fold uses the reference snoc
  identity. All cut pairs, including empty and diagonal cuts, are retained;
  remaining suffix equality is not weakened.
- Constraint semantics: `derivedCheck_eq`, `safeCheck_eq`, `satCheck_eq`,
  `separationCheck_eq`. Denial safety and unsatisfiable-premise vacuity are
  unchanged under a correct cache.
- Positive answers: `productRule_sound`, `positiveRule_sound`,
  `positiveClosure_sound`, `positiveCheck_sound`. Upper/lower product bounds
  compose through covariance; failure of the closure has no negative meaning.
- Negative answers and completeness: `separationExists_sound`,
  `afterPositive_correct`, `normalizedWithPaths_correct`,
  `normalizedEntailsCheck_correct`, `entailsCheck_correct`, `entailsCheck_eq`.
  Candidate paths need not be complete because the unconditional complete
  backend remains the fallback. Arbitrary-tree quantifiers are retained.

## Limits

`Cache` is runtime data, without an embedded proof field. A direct user may
construct an incorrect cache. Correctness theorems for cached operations
therefore require `Correct`; the production wrapper constructs its cache with
`prepare`, whose correctness is proved. This separation prevents classical
proof dependencies from entering the executable cache constructor.

The reviewer did not audit the Python benchmark driver, CLI edits, performance
claims, or countermodel extraction. The parent reviews and tests those
separately. The independent P-automaton comparisons supplement the all-input
Lean equalities; finite tests are not their proof. Neither review establishes
broad practical scalability or completes the regular-countermodel extractor.
