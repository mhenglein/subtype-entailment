# Adjacent machinery and prior-art boundaries

These works do not directly solve Problem 1.7. They delimit what can and cannot be claimed as new and identify imported-theorem obligations.

## Regular languages and borders

### Anderson–Loftus–Rampersad–Santean–Shallit (2008)

- **Problem family:** whether a DFA/NFA language contains bordered or unbordered words, whether infinitely many occur, and shortest-witness size.
- **Established relevance:** ordinary borderedness and unborderedness inside regular languages are algorithmic topics with known polynomial/quadratic witness phenomena.
- **Difference from Subtail:** a Subtail violation is indexed by two run cuts whose endpoint states must form a selected ordered pair `G`; the compared prefix/suffix is coupled to one accepting run and terminal source/target structure. This is not merely `L(A) ∩ Bordered ≠ empty`.
- **Safe claim boundary:** C077 must not be sold as the first quadratic bound for borders in automata. Its candidate novelty lies in the flagged, state-dependent last-target collapse and the exact `k^2+k-2` bound for that class.

## Word equations with constraints

### Diekert–Gutiérrez–Hagenah (2001) and later recompression work

- **Established result used by Subtail-style reductions:** existential word equations with rational/regular constraints are decidable; the free-group/free-monoid-with-involution formulation is PSPACE-complete.
- **What it can discharge:** satisfiability of a *supplied finite existential formula* or supplied symbolic scheme.
- **What it cannot discharge:** existence of a complete finite family of schemes; a universal/existential alternation; or a compiler that preserves one shared extension for an entire conjunction.
- **Audit rule for C067/C068/C071/C072/C075:** state the exact formula, variable sharing, regular constraints and size construction before importing PSPACE.

### Ganesh–Minnes–Solar-Lezama–Rinard (2013)

- **Boundary:** validity for positive forall-exists word equations is undecidable in general, while certain quantifier-free solved forms with length/regular constraints are decidable.
- **Relevance:** prevents replacing C080 or cap universality with “word equations are decidable.” Quantifier prefix and syntactic restrictions are decisive.
- **Non-implication:** general undecidability of a richer forall-exists language does not settle the restricted cap or terminal flagged-border fragment.

## Backreferences and pattern languages

- One-variable or one-use backreference formalisms can already have hard/undecidable universality variants.
- Similarity to “choose a block and repeat it” is only a warning. A transfer requires an exact encoding preserving Subtail's terminality, shared word, allowed cuts and acceptance.
- C069's nonsemilinear witness-length support should be framed as an exact phenomenon in a fixed flagged-border instance, not the first nonregularity/nonsemilinearity result involving repeated words.

## Factorization forests and finite algebra

### Simon/Kufleitner factorization-forest theorems

- Supply bounded-height factorizations once a finite semigroup morphism with the needed composition invariant is available.
- Do not by themselves produce a finite border-preserving quotient.
- Subtail's recorded collisions show that endpoint action or visited-state profiles alone lose shared-word information. Any use must first define a finite algebra whose multiplication preserves the existential witness property across newly created comparisons.

## Conjunctive regular path queries

### UC2RPQ boundedness and finite expansion

- Query boundedness asks whether recursive regular-path atoms can be replaced by a finite union of conjunctive queries, often with very large bounds.
- Conceptual overlap with C080: finite compilation of regular-path constraints and preservation of a conjunction.
- Crucial differences: generic graph databases versus KMP/prefix graphs; C080 compiles across a particular first-return graph extension; physical intervals share one generated word; colors encode terminal masks and next/end data.
- No inspected CRPQ theorem directly yields `Sat(P(B),Pre(phi)) iff exists one safe first-return C extending B with Sat(P(C),phi)`.
- **Search obligation:** look for inverse-image closure of CRPQs under finite-state graph transductions/interpretations and for preservation under one-entry graph extensions. Until an exact theorem is mapped, CRPQ work is analogy rather than dependency.

## FC[REG]-CQ universality

### Thompson–Freydenberger (2024)

- Universality/containment results for concatenation logic with regular constraints can encode invalid computations.
- Useful adversarial source because the quantifier shape resembles containment in an existential bad-language union.
- The formalism permits richer systems of factor equations than terminal BorderAvoid. A reduction needs a gadget using only one terminal copy structure and the exact flagged comparisons.
- It is neither a decision procedure nor an undecidability theorem for Subtail.

## Practical import checklist

For every external theorem used in a Subtail proof, record:

1. exact theorem number and version;
2. input alphabet and empty-word conventions;
3. variable sharing and number of occurrences;
4. regular/rational constraint representation;
5. quantifier prefix;
6. complexity measure and formula-construction size;
7. mapping from Subtail objects;
8. conclusion obtained;
9. any remaining coverage or termination obligation.
