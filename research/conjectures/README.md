# Conjecture registry

Use this directory for important open hypotheses that may coordinate multiple investigations.

Conjectures use stable IDs `Q001`, `Q002`, ... . Do not create a Q record for every passing thought; create one when the hypothesis is likely to be attacked, cited, refined, or depended on by more than one investigation.

Each record should contain:

```md
# Qxxx — Short name

Status: OPEN | REFUTED | PROVED | SUPERSEDED
Confidence: speculative | evidence | strong-evidence | near-proof
Introduced: YYYY-MM-DD
Related: Axxx, Cxxx, Exxx, #issue

## Claim

Exact quantified statement.

## Why it matters

What would follow if true or false?

## Evidence for

- ...

## Evidence against / boundary cases

- ...

## Attempts

- YYYY-MM-DD — Axxx — outcome and evidence link

## Dependencies

- ...

## Next discriminating test

The cheapest proof attempt, counterexample search, or experiment that would materially change confidence.
```

When a conjecture is proved or refuted, preserve the file and update its status. If it becomes a formal claim, add the corresponding C ID to `research/claims.md` and cross-link it here.