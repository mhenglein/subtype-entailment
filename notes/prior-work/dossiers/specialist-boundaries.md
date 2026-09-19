# Specialist-journal results and an unresolved corrigendum

These are discoveries outside the direct NSSE title lineage. They provide concrete guardrails and potential techniques, not a completed transfer to Subtail. Source metadata is centralized in [the bibliography](../bibliography.md).

## PW-RS14 — Kybernetika: resets are not reversals

**Primary text:** [paper](https://www.kybernetika.cz/content/2014/1/66/paper.pdf). Definition 3.7 and Theorems 3.9/3.15 distinguish bounds on head reversals, modulo-counter reversals and resets. For this model, incrementing past the modulus boundary counts as a counter reversal. Theorem 3.9 gives decidable emptiness, infiniteness and disjointness when the stated bounds are all finite. Theorem 3.15 gives undecidability of the listed language problems for `(3,infinity,0)-REV-NBMCA(3)`: three counters, at most three head reversals, no resets, but no bound on counter reversals.

**Subtail analysis:** a proposed period machine cannot borrow the positive result merely because it chooses a bounded number of period parameters or never resets them. The missing invariant may be the number of wraps or returns, which can remain unbounded. Conversely, the negative theorem does not establish BorderAvoid undecidability: the automaton model's tape access, counters and acceptance must be encoded using the permitted terminal comparisons. That encoding has not been provided.

## PW-KS10 — DMTCS: regular but not effectively constructible

**Primary text:** [paper](https://dmtcs.episciences.org/523/pdf), Theorem 5.2. Equality languages of bounded-delay-2 morphisms are regular, but cannot in general be algorithmically obtained; PCP for these morphisms is undecidable. For PCP the relevant witness is a **nonempty** word; do not overlook the trivial empty equality word. The paper points to an older stronger biprefix result by Ruohonen; that citation is a lead, not a separately inspected theorem in this dossier.

**Subtail analysis:** 'there are finitely many equivalence classes' and 'there is a DFA' must be followed by an effective construction from the input, or a computable bound enabling enumeration. Existence alone is insufficient for a decision procedure. This does not refute an effective quotient for a strictly narrower, correctly specified Subtail family.

## PW-KS11 — Fundamenta Informaticae: distinguish two kinds of factorization

**Primary text:** [author PDF](https://amsaar.gitlab.io/articles/kasa11ibarra.pdf), Theorem 2.1. Unique decipherability is undecidable in the monoid of regular languages over a non-unary alphabet. The elements being multiplied are **languages**; the proof embeds a product of word monoids into that monoid.

**Subtail analysis:** this result is not about whether a particular word has two decompositions into factors from two finite sets. It is not the justification for the Priesnitz counterexample; that example is an elementary individual-word calculation. Before invoking this undecidability theorem, define exactly which language-valued objects are the generators and what equality of their products means. Ordinary prefix-free word-code arguments remain separate.

## PW-REGEX25 — IJFCS: corrigendum requiring full-text follow-up

**Identified record:** Szymon Łopaciuk, *Corrigendum: Inside the class of REGEX languages [6]*, 2025, [DOI](https://doi.org/10.1142/S0129054125920017). Metadata was recorded in the discovery issue; publisher full-text retrieval was unsuccessful. The actual repair has **not** been checked.

**Use now:** flag the original REGEX-language characterization as requiring version/erratum checking before import. Do not claim that every result about backreferences is invalid, or specify the repaired theorem from its title alone. The full correction, original formulation, treatment of undefined backreferences and downstream dependency review remain open.

## Follow-up citation edges, explicitly not completed audits

PW-KS10 -> the cited older Ruohonen biprefix result; PW-KS11 -> work on language-monoid decipherability and the RAIRO additive-monoid paper; PW-TF24 -> deterministic backreferences, factor-referencing characterizations and extended-regex succinctness. These are concrete next edges for discovery, not evidence of complete coverage of those journals or theorem families.
