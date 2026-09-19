# Prior work: agent entry point

This is the durable scholarship map for **Problem 1.7**, not a second claims ledger. It consolidates the September 18–19 literature investigation recorded in [issue #36](https://github.com/mhenglein/subtail/issues/36). The publication baseline is `df222241dc1a55ac6ee5da3cba3aedf662b3e285`. Read current [STATE](../../STATE.md) and [claims](../../research/claims.md) before relying on any scientific-status snapshot here.

**Scope:** semantic `{bottom, covariant binary product}` over arbitrary, possibly infinite trees. No top constructor does not mean no greatest infinite tree. Historical full-signature NSSE results need a transfer argument. See [the exact problem](../../research/problem.md).

**Evidence boundary:** this is a bounded, source-linked discovery and preservation pass. It is not an exhaustive bibliography, an independent human referee report, a completed novelty audit, or a proof of the general decision procedure. Missing literature is an open coverage question, not evidence of priority.

## Read in this order

| Need | Durable entry |
|---|---|
| Start or resume proof work without repeating known mistakes | [Agent handoff](agent-handoff.md) |
| Understand the direct historical problem lineage | [Core NSSE dossiers](nsse-lineage.md) |
| Find potentially reusable algorithms or hardness boundaries | [Adjacent machinery](adjacent-machinery.md) |
| Audit a proposed simplification before building on it | [Failure-mode catalogue](failure-modes.md) |
| Compare C067/C069/C077/C078/C079/C080 with previous work | [Novelty and transfer matrix](novelty-matrix.md) |
| Check source identity, version, status and inspection depth | [Bibliography](bibliography.md), [machine-readable register](sources.json) |
| Inspect the newly recovered thesis issue | [Priesnitz Chapter 11 audit](dossiers/priesnitz-2004.md) |
| Understand the withdrawn attempted solution | [Schubert dossier](dossiers/schubert-2021.md) |
| Inspect specialist-journal results | [Kybernetika, DMTCS, Fundamenta and corrigendum dossier](dossiers/specialist-boundaries.md) |
| See what was actually searched and what was not | [Search and coverage log](search-log.md) |
| Select a precise next investigation | [Open obligations](open-obligations.md) |

## What changed in this preservation pass

The substantive additions are a concrete counterexample to the *literal statement* of Priesnitz's Lemma 11.1, the exact location and object of Schubert's failed extension claim, and specialist results warning against bounded-reset and noneffective-regularity shortcuts. Their dossiers separate the source statement, local analysis, and what remains unproved.

The 2025 negated-containment and 2026 one-use-backreference papers were already present in older Subtail notes; they are restored to this central map, **not counted as new discoveries**. The bibliography also corrects the conflated 1997/1998 Henglein–Rehof titles, guessed CRPQ authors, and publication/version dates. The ordinary-unbordered comparator includes a **linear** witness bound, not only the previously emphasized quadratic border phenomena.

## Non-negotiable boundaries

- A supplied existential formula being decidable does not construct a complete finite family of formulas.
- Individually satisfiable requirements do not imply a single shared extension satisfying their conjunction.
- A regular language existing does not imply its automaton can be effectively constructed.
- A counterexample to a lemma does not by itself refute its paper's final theorem.
- A syntactic example outside an old restriction does not prove non-subsumption after equivalent encodings.
- The C080 reverse compiler result is already recorded on the inspected main. Forward coverage, the remaining quantitative/finishing work, semantic composition and independent review must not be declared complete here. The current ledger takes precedence over this snapshot.

## Maintenance

Use the stable `PW-*` source identifiers in this directory; they are bibliography keys, not new C/Q/A/E scientific claims. Run `python3 notes/prior-work/check_scholarship.py` after editing this directory and the repository's `python3 scripts/research_index.py --check` after organizational changes. The former checks documentation and a small finite regression, **not the mathematical correctness of cited papers or C080**.

Before adding a result, record its exact version, theorem/page locator, hypotheses, quantifiers, representation/size measure, transfer to Subtail, and remaining obligation. Keep failed retrievals and unchecked leads visible. Follow current [AGENTS.md](../../AGENTS.md), including issue-first ownership and serialized integration. No downloaded paper, credential, or extracted page image is included in this directory.
