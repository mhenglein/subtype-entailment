# Exact shared-word composition and decidable family validation

Date: 2026-09-06. Main base: `0318ff7b8750f64d72f0be87519782c1d91238de`.
Workstream: A017 / Agent 2. No additional agents were launched.

**Status:** written proofs, classical external decision-theorem dependency, and
executed finite checks. Not independently reviewed or Lean-checked. This is NOT
a solution of unrestricted Problem 1.7. It supplies an exact composition
language and a terminating *verification* problem for proposed families;
finding a complete finite family or an appropriate terminating saturation
remains unresolved. No literature-priority claim is made.

The prior five-state and twelve-state residual examples showed that isolated
suffix summaries lose shared word contents. This continuation keeps the shared
parameters, proves how to compose them, and separates a decidable universal
family check from the still-unresolved existential question. A separate
Post-correspondence argument rules out a completely generic iteration theorem
for the proposed representation language; it is not a reduction to BorderAvoid.

## 1. One equation captures every forbidden suffix agreement

Let I be an arbitrary partial binary DFA with initial state s, accepting set F,
Bad states, and ordered flags G. This section does NOT require terminal final
states. Let C_I be its regular language of defined accepted words avoiding Bad.
For states p,q, let L(p,q) be the regular language of defined paths p to q,
ignoring annotations. All variables below range over finite binary words,
including epsilon.

For any w in C_I,

    w is not a witness
    iff there exist x,d,z,t and (p,q) in G such that
       w = x d z,
       d z = z t,
       x in L(s,p), d in L(p,q).                        (1)

**Forward proof.** Let i<=j be a flagged agreeing pair. Put x=w[:i],
d=w[i:j], z=w[j:]. Agreement says z is a prefix of d z, so there is a
remaining word t with d z=z t. The run endpoints give the path constraints.

**Reverse proof.** Set i=|x| and j=|x|+|d|. The first equation gives the two
cuts in w, the second says that the suffix at j is a prefix of the suffix at i,
and the regular constraints identify the flagged states. Thus w violates G.

No length arithmetic is needed: |d|=|t| follows from the equation. In particular:

* d=epsilon handles diagonal comparisons, with t=epsilon;
* z=epsilon handles the empty final suffix, with t=d;
* |z|>|d| is an overlapping occurrence, not an excluded case;
* x=epsilon permits a source at the initial state.

For the terminal path accepting 000 with flag between its initial state and
its one-letter successor, d=0,z=00,t=0 is an overlapping violation. For a path
accepting 0 with a flag from initial to final, z=epsilon is the empty-suffix
violation. The equation handles both without extra cases.

Inadmissibility is separately captured by the regular constraint w not in C_I.
Therefore the entire non-witness language, including undefined or unsafe runs,
is a finite union of existential word-equation systems with regular constraints.
This is an exact representation, NOT a regular-language claim.

## 2. Shared-word relational templates compose exactly

A template has finitely many word variables, regular domains, a finite
conjunction of word equations, and tuples of input/output expressions formed
by concatenation of variables and constants. Its relation consists of the
input/output tuples induced by satisfying substitutions. Auxiliary variables
are existentially projected; a variable repeated in several expressions
always denotes the SAME word.

For R(input,interface) and S(interface,output):

1. Rename all variables of R and S into disjoint namespaces.
2. Conjoin their constraints.
3. Equate the corresponding interface expressions.
4. Retain R's inputs and S's outputs and existentially project auxiliaries.

The result is again a finite template. Its semantics is exactly

    (a,c) in compose(R,S)
      iff some b has (a,b) in R and (b,c) in S.          (2)

The forward implication reads b from the shared equal interface. The reverse
combines the two satisfying assignments after renaming; their common b makes
the interface equations true. Composition is consequently associative as a
relation, even though generated variable names and equation lists differ.
Renaming is essential: equally named private variables in the two inputs must
NOT be silently identified. Conversely, removing an interface equation loses
the shared-word condition and admits spurious combinations.

This construction keeps the prior copy benchmark as one relation:

    X in (10|11)*, N in (01)*,
    prefix = X 00 N, suffix = X 00.

Composition with a concatenation interface yields X00NX00, with one common X.
It does not yield X00NY00 with independently selected X,Y. The prior proof
establishes all these shared-X words as witnesses for its twelve-state
instance. The present composition theorem preserves that statement but does
not independently reprove every detail of that instance.

## 3. Universal validation of a supplied template is decidable

Let Phi(V) be the template's equations/regular constraints and W(V) its output
word. Consider the question

    Is EVERY word in {W(theta): Phi(theta)} a witness of I?                (3)

Its failure is precisely the following existential formula:

    exists V: Phi(V) and W(V) not in C_I
    OR
    exists V,x,d,z,t: Phi(V) and W(V) in C_I
       and W(V)=x d z and d z=z t
       and OR_{(p,q) in G} [x in L(s,p) and d in L(p,q)].                  (4)

Use a fresh variable equal to W(V) whenever regular constraints are required
on variables rather than expressions. Regular complement is effective over
the fixed binary alphabet. Finite disjunction means finitely many ordinary
existential systems. There is no new length constraint, arithmetic predicate,
substring primitive, or quantifier alternation in (4).

Solvability of word equations with regular constraints is decidable. Applying
that theorem to (4), then negating its answer, decides (3). Template emptiness
is another such existential check; perform it separately so that a vacuously
valid empty family is never mistaken for a positive witness certificate.

**External theorem used:** Diekert, Jez and Plandowski, *Finding All Solutions
of Equations in Free Groups and Monoids with Involution* (2014),
https://arxiv.org/abs/1405.5133v2. Their rational-constraint monoid result includes
ordinary word equations by restricting variables to the original non-inverse
alphabet. For an explicit discussion of ordinary word equations and regular
constraints, see Day et al., *A Closer Look at the Expressive Power of Logics
Based on Word Equations* (2023/2024),
https://doi.org/10.1007/s00224-023-10154-8, introduction and cited results.
The classical theorem is attributed, not claimed as a new algorithm here.

Equation (3) applies to arbitrary binary instances, including nonterminal
accepting states, arbitrary recurrence, and annotations at every position.
It does NOT require delimiter alignment or a bounded number of runs.

### The quantifier boundary

Universal family validation is NOT the following question:

    Is there a substitution theta with Phi(theta)
    for which W(theta) is a witness?                    (5)

Formula (5) requires absence of every possible violating cut for the chosen
substitution. Negating (4) universally validates ALL substitutions; it does not
select a good one from a mixed family. A bad member disproves (3), but says
nothing about whether another member witnesses (5).

For the five-state recurrent benchmark, the unrestricted candidate family
1^m0^z1^n0 contains both good and bad words. An independently verified bad
member is 11010; the good member 1010 remains. Neither the bad member nor the
failure of a proposed family certificate is an unrestricted NO verdict.

If a nonempty template passes (3), it is a sound reusable positive certificate.
Such templates include singletons, but this observation alone is only a
positive semiprocedure. No effective size bound on a sufficient template and
no complete negative procedure follow from this theorem.

## 4. An implemented exact backend for regular families

General word-equation solving is a substantial external algorithm. For a
supplied regular domain D and ARBITRARY binary I, a separate finite-monoid backend
solves D subseteq Witness(I) exactly without any SMT solver. This is useful
both operationally and as an independent test of the distinction in Section 3.

First, finite product reachability checks whether a D word has an undefined
I run, visits Bad, ends outside F, or visits a state p with G(p,p). Any such
member immediately refutes the universal assertion. If no domain word exists,
return valid-but-empty. Otherwise all remaining bad words have a proper
flagged agreement.

Intersect I with D, preserving safe paths, to form a K-state reachable product
M. This construction does not require terminal accepting states.
Keep a shortest head word reaching each product state. Complete M with a sink
and enumerate its finite transition monoid S, including the empty-word action.
For each action also retain a nonempty representative when one exists. This
last detail is necessary when a nonempty loop has the identity action.

### Periodic normal form of a violation

For a proper violation, d is nonempty in (1). Divide |z| by |d|. Since z is
a prefix of the infinite repetition of d, there are u,v and an integer e>=1
such that

    d=u v, v nonempty,
    z=(u v)^(e-1) u,
    w=x (u v)^e u.                                    (6)

Here |u|<|uv|; this is guaranteed by v being nonempty and needs no arithmetic
constraint in the construction. u may be empty.

For fixed head state p and words u,v, let Y be the transition action of uv
on the K-state safe product. Acceptance of x(uv)^e u asks whether the unary
orbit Y^e(p) belongs to the fixed set of states from which u accepts. If any
positive exponent succeeds, the least such exponent is at most K: a longer
first success would repeat a previous state in the deterministic orbit. The
absorbing undefined sink never succeeds and does not increase this bound.
Replacing e by that smaller positive exponent preserves the flagged states
after x and xuv and still supplies a real violation of the form (6).

When I additionally has terminal final states and k original states, every
actual violation has e<=k-1. The original run states after x, x d, ..., x d^e
must then be pairwise distinct. If two coincide, applying the later state's
remaining periodic suffix from the earlier copy reaches the same terminal
accepting state strictly before w ends, a contradiction. Terminality is only
an optional optimization, not a requirement for the backend.

The search enumerates a head endpoint, actions A of u and B of v, and
positive e<=K (or e<=k-1 for terminal I). It evaluates the repeated action B
after A, checks the flag
between the states after x and xuv, and checks finality after x(uv)^e u.
When the tests pass, instantiate u and v using the SAME chosen representatives
at every occurrence. The reconstructed word has the required equality and
correct automaton action, so the direct predicates verify a real bad member.

Conversely, every proper violation has (6). If necessary, first shorten its
exponent using the finite product orbit, as above. The enumerated actions of
u,v and the head state then occur. Replacing components by representatives keeps
the chosen flag, final state, defined path and D membership. Thus exhaustive
failure of this finite search proves that every D word is a witness.

This substitution is intentionally used to preserve ONE witnessed violation,
not to preserve the whole agreement profile or every left context. It does
not contradict the earlier transition-action collision counterexamples.

A shortest monoid representative has length at most |S|-1; a shortest nonempty
representative has length at most |S|. Hence a proper violating member, if
one exists after the regular boundary check, has a representative of length
at most

    K-1 + (2K+1)|S|.

For terminal I the sharper bound is K-1+(2k-1)|S|. These bounds concern proper
violations after the separate admissibility/diagonal check, not that earlier
regular check's counterexamples.

This is a counterexample bound for UNIVERSAL REGULAR-FAMILY VALIDATION, not a
small-witness bound for unrestricted existence. S is finite but may be large.
Caps on monoid states/evaluations return UNKNOWN. Setting them to None gives
the terminating finite algorithm. No polynomial running-time claim is made.

### The recurrent benchmark

For the five-state instance from the previous note, choose the infinite regular
family 1 0^+ 1 0. The backend proves every member is a witness using eleven
monoid elements, without bounding the number of zeros. For the entire regular
candidate language 1^+0^+1^+0, it returns the bad member 11010 while the instance
itself still has witnesses. These are exact answers to different family queries.

A nonterminal two-state parity example requires exponent two in (6), so the
terminal k-1 bound cannot simply be retained outside its hypothesis. The new
product-orbit bound finds the violating word 00. A one-state all-accepting
binary loop with no flags supplies a universally valid infinite nonterminal
family, including the empty word. Both are explicit regression fixtures.

## 5. Why unrestricted relational iteration is NOT automatically decidable

The representation of Section 2 is intentionally expressive. A general theorem
that all of its iterated reachability problems are decidable is false.

Given a binary Post correspondence instance with tiles (a_i,b_i), form one
template relation per tile:

    R_i : (X,Y) -> (X a_i, Y b_i),  X,Y in {0,1}*.

Starting at (epsilon,epsilon), a nonempty sequence i_1,...,i_n reaches

    (a_i1 ... a_in, b_i1 ... b_in).

It reaches the diagonal {(Z,Z)} exactly when that index sequence solves PCP.
Each step is an exceptionally simple shared-word template, and every FIXED
finite composition is just a system of word equations. Yet deciding whether
SOME nonempty composition reaches the diagonal would decide PCP and is
therefore undecidable.

The source undecidability theorem is classical. A primary proof reference is
Halava and Harju, *On the Steps of Emil Post: from Normal Systems to the
Correspondence Decision Problem* (2020),
https://doi.org/10.14232/actacyb.284625. This paragraph provides the reduction
into generic template iteration; it is not a claimed new result about PCP.

**No reduction from PCP to the special BorderAvoid instances is given here.**
Consequently this does NOT establish undecidability of Problem 1.7. It prevents
an incorrect positive proof that invokes generic template iteration as a
black box. A terminating saturation must exploit additional invariants of the
actual suffix-obligation transitions, not just closure under finite composition.

For a concrete two-step sanity check, tiles (0,01) and (10,0) lead from the
empty pair to (010,010); neither individual step is diagonal. Requiring a
nonempty sequence is essential, since the zero-step empty pair is always equal.

## 6. Executed implementation checks and limitations

Standard-library command:

    python3 experiments/check_shared_composition.py

Recorded seed: 2026090660. Result: `results/shared-composition.json`.

* 12,218 defined words on 120 randomly generated partial binary tables compare
  the exact equation representation with all forward agreement pairs, including
  nonterminal final states and arbitrary annotations.
* 15,240 regular-expression checks compare GNFA elimination with direct runs.
* 60 complete finite-domain relation compositions, 12 associativity cases, and
  an explicit accidental-name-capture case validate interface handling. A two-
  output, two-step example also checks the stated PCP-style composition gadget.
* 381 complete finite-language universal-safety oracles, with 1,178 candidate
  words: 97 valid families and 284 families with a verified bad member.
  320 domains are freely generated dictionaries; another 61 of 100 generation
  attempts yield nonempty dictionaries of accepted candidates. This is not an
  exhaustive census of arbitrary instances.
* All 256 three-state terminal transition tables, with the selected flag (0,1),
  receive finite-monoid checks: 215 universally safe candidate languages and 41
  with a returned bad member. All 780 accepted words through length seven are
  checked independently. Those short checks alone do not certify the universal
  results; the all-length argument is Section 4.
* Six exact canonical regular-model path checks use the existing terminal
  realization and semantic checker, at their prior audited/written status.
* 320 additional finite-language oracles permit arbitrary accepting states
  with outgoing transitions: 65 valid families, 255 bad-member families, and
  1,225 completely enumerated words. Two analytic infinite nonterminal cases
  exercise validity and the need for a repetition exponent exceeding k-1.
* An explicit monoid-cap guard returns UNKNOWN. Malformed inputs are rejected
  by validation; nonterminal accepting states are supported, not rejected.

Optional practical backend command:

    python3 experiments/check_shared_composition.py --with-smt

Result: `results/shared-composition-smt.json`. Generated queries are in
`results/shared-composition-queries/`. The backend is the installed native Z3 4.13.3.0, accessed without
an additional Python package. The query text contains only concatenation,
equality and regular membership (including effective regular complement).
No string-length, substring, or universal quantifier primitives are emitted.

The optional run correctly distinguishes a valid singleton, an invalid
singleton, and an empty family. It returns independently checked bad members
when unary/copy parameters are made independent. All 20 complete finite-family
oracle cases finish with the correct result. At a 1,500 ms per-query limit,
four unbounded positive-family examples remain UNKNOWN: the infinite regular
family, the shared unary family, the shared arbitrary-copy family, and a
nonflat shared-copy family whose source/target prefixes already disagree. The
finite-monoid backend independently resolves the first of these. The prior
written benchmark proof covers the unary and arbitrary-copy families; a
two-letter mismatch covers the protected nonflat fixture. The SMT run is NOT
reported as having verified any of these four cases.

SAT models are independently checked against all domains/equations and both
word predicates; returned cut decompositions are also checked. UNSAT retains
the backend trust boundary. The theoretical decidability statement refers to
a complete constrained-word-equation algorithm, not to Z3's heuristic string
engine. Microsoft's own documentation explicitly calls that engine incomplete:
https://microsoft.github.io/z3guide/docs/theories/Strings/.
No cross-engine consensus or independently checkable UNSAT proof is claimed.
Installing other Python solvers was attempted but the container lacked network
name resolution; no additional solver was installed or silently substituted.

No full repository suite, Lean build, or independent mathematical review is
claimed. The source matcher/forward and reverse word predicates are unchanged.
The original core regression is replayed separately, with its result checked
against the prior blob. The two-state nonterminal extension was added after
the first terminal-only run; the full deterministic suite was rerun against
the changed implementation rather than inheriting an earlier PASS. Timing-based optional UNKNOWN results are inherently
machine-dependent; the deterministic core result is the reproducibility anchor.

## 7. Exact remaining obligation

We now have:

* a shared-parameter representation with exact finite composition;
* a decidable all-input check that a PROPOSED family contains only witnesses;
* a complete finite-monoid implementation for regular families;
* an explicit reason not to assume generic unbounded relational iteration.

We do NOT have:

* an effective bound on sufficient family descriptions;
* a proof that the relations generated by arbitrary recurrent suffix targets
  stay in a terminating subclass;
* a complete negative certificate system for mixed families.

The best next discriminating lemma is a syntactic/semantic invariant of the
actual suffix-obligation transitions that excludes the PCP-style two-output
accumulation while remaining complete for all terminal inputs. Merely writing
equations, composing them correctly, or increasing the number of compositions
does not establish that invariant or termination.
