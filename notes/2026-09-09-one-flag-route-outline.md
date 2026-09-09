# Route outline: exact counting for a unique forbidden period

Base: 05b20ee73841d0e7105a44beb761e553a7081a8d. Date: 2026-09-09.
This is a conceptual attempt, not a claim that the full problem is solved.

## Final target

A total exact terminal BorderAvoid decision, transferred to normalized Problem
1.7 through the recorded semantic bridge. The first scoped target is every
terminal instance with one forbidden ordered state pair, not just bounded words.

## Conditional route

1. Normalize a single source by splitting target-free accepted paths and a
   safe path to the source followed by a suffix with no source revisit.
2. Prove a given target state can carry at most one proper period of any word
   accepted from that source. Terminality is critical.
3. Parametrize a period d by w=(uv)^e u, v nonempty, 1<=e<=k-1. Show this is
   a bijection between period incidences and the parametrized tuples.
4. Count period incidences using transition-monoid fibre generating functions.
   Each fibre has a rational ordinary length series with a common denominator.
5. With at most one incidence per candidate, subtract the bad count from the
   candidate count. Prove an effective numerator-degree bound, hence a finite
   complete zero test and an explicit bound on a shortest witness.
6. The arbitrary multi-target/multi-source extension remains open. Distinct
   violations can be counted more than once; subtraction alone is not sound.
   Investigate exact joint-incidence series or a disjoint violation selector.

## Discriminating checks

For each short candidate compare the number of directly detected periods with
the number of (u,v,e) representations. Compare length coefficients separately,
not merely solver YES/NO. Validate a counterexample with two target states
before proposing multi-target subtraction. Test one flag whose source is not
the initial state, multiple final states, empty words, Bad states, diagonal
flags and final-column flags.

## Opposing route

If joint-incidence counting cannot be kept effective, ask whether the exact
source/target interactions implement an undecidable shared-transformation
constraint. Nonrationality or failure of naive subtraction alone is not that
reduction. No extra substring constraints may be silently imported.

## Evidence standard

Exact integer counts, independent forward/reversed membership, and complete
small finite-language oracles. Resource caps remain UNKNOWN. An all-length
claim must rest on the generating-function argument, not test ranges.
