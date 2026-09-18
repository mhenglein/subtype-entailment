# Exact first-return graph formalization route

Date: 2026-09-18. Base `adcc28455fbdd7fd6b60566c272e8d9e7a42335c`.
A018 supporting A017. User-authorized continuation; isolated proof branch.

Target: prove that the candidate's first-return local graph construction agrees
with literal coloured prefix graphs. Reuse TerminalRank and RankMilestones.
Do not replace literal prefix matching by the unproved surgery equations.

1. Define K edges by a finite maximum of extendable literal borders, and prove
   equivalence with longest-prefix/suffix matching after appending one letter.
2. Derive full-prefix fallback and proper-parent update; prove the old-graph
   generator computes every new failure target, with its first full hit at end.
3. Prove all old/interior/endpoint K and S/F edges, the wrap including a
   singleton extension, old-end recolouring and incoming-flag mask equations.
4. Read formal statements back against the original construction, compile with
   pinned Lean, replay through its kernel, inspect dependency axioms, and run
   native/literal regressions and the existing Lean suite before integration.

This is the graph dependency, not the uniform query preimage proof. The latter
still requires finite observer syntax, bounded diagrams, a shared interval word,
both compiler directions, iterated closure and a concrete executable global
bound. The arbitrary-tree transfer remains a separate formalization obligation.

Acceptable outcomes: checked exact graph theorem, a precisely scoped checked
part, or a counterexample identifying an invalid interface. Drafts are not
Lean-checked until their actual workflow succeeds. Preserve failed builds and
all existing global candidate statuses; do not add axioms to close a gap.
