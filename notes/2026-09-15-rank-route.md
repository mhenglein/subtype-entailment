# Global border-rank route: precise construction and unresolved quotient

Date: 2026-09-15. Repository baseline: 47adf83c194aa941b525240f6470f3d77a69f81d.
Target: unrestricted binary terminal BorderAvoid, with arbitrary flags and Bad
states. Original arbitrary-tree subtype semantics are unchanged. No new claim
identifier is allocated, and no independent review or Lean proof is claimed.

## Intended complete route

1. Reverse a candidate and its run. At every scanned prefix, forbidden pairs
   occur exactly between its endpoint colour and the colours of its borders,
   including the empty and full borders. This is the existing exact reversal.
2. A terminal reverse run gives distinct colours along each failure-link chain.
   Its maximum border-tree depth is at most k-1 (empty prefix depth zero).
3. Prove that the first prefix of depth h ends at the first return of the first
   prefix of depth h-1. Thus every candidate has at most k-1 reference-growth
   levels. There is no bound on the lengths of the reference words.
4. For a FIXED reference word with its full run, KMP plus a reverse automaton
   state checks all possible extensions up to its first return exactly.
5. MISSING: replace the infinitely many possible grown reference words by an
   effectively finite existence-preserving set, or solve their joint choice
   without making that replacement. Only this step would complete the route.

## Discriminating candidate (not a theorem)

At each reference-growth level, retain only a shortest safe first-return
extension for each endpoint colour. Recursively try those representatives,
while using a complete fixed-reference graph to test whether the original
start is reachable without another return. Depth is bounded, but completeness
of this representative selection is UNPROVED. A failed search must be called
EXHAUSTED_HEURISTIC, never NO. Compare it against concrete known witnesses and
complete small or finite-language oracles. If it fails, preserve an exact small
counterexample and identify the shared word information that was lost.

## Why this is a global attempt

The rank decomposition applies to every accepted terminal word, not a graph
class defined by additional return closure or marker restrictions. Nevertheless
bounded hierarchy depth alone is not finite-state synthesis: each new reference
contains the old one and potentially unbounded new content. Neither the existing
source-capture theorem nor a generic word-equation solver automatically removes
this dependency. A failure of the proposed quotient refutes that quotient, not
the rank representation or unrestricted decidability.

## Opposing route

A genuine computation encoding must also respect the bounded border-chain
colours and common-reference dependencies. An unbounded family of distinguishable
references may obstruct this proposed constructive proof, but is not an
undecidability reduction. The existing copy/counting and recurrent-residual
examples remain mandatory boundary tests.

## Outcome of this cycle

Both finite word-summary quotients were falsified. A different graph-interface
summary repairs ONE unknown-reference elimination exactly; see the companion
proof. It does not establish closure for every remaining rank level. The full
unrestricted implication is therefore still an open obligation, not a theorem.
