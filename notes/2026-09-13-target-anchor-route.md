# Terminal target anchoring via one negated containment

Date: 2026-09-13. Base: c4f7e56665828710b3bda77e32bb2904ad4006d6.
Target: a terminating unrestricted decision, not another polynomial witness bound.

Proposed steps before implementation:
1. Boundary-normalize one terminal final slice (Bad, diagonal flags, final-column flags).
2. For the class in which every proper repeated suffix beginning at a target is
   forbidden, prove that only the last target occurrence matters. Its suffix Y
   must not occur in the candidate word with its final symbol removed.
3. Split Y=Za and W=XZa. A last-target choice and final letter give independent
   regular constraints on X,Z and one condition NOT Contains(XZ,Za).
   Import the precise MFCS 2025 single-negated-containment theorem, not a theorem
   for arbitrary conjunctions or transducer constraints. No equation backend is
   assumed implemented.
4. Try to compile arbitrary flags into that class by maximally distinguishing
   transition colors subject to preserving last-aligned bad comparisons. A finite
   synchronized graph must exclude every unflagged colored match to a target.
   If that finite sufficient test passes, prove exact witness correspondence.
5. Test whether this certificate covers arbitrary inputs. A failed certificate
   is UNKNOWN, not NO. If completeness fails, save an explicit obstruction and
   keep the unconditional reduction theorem separate from global coverage.

Opposing route: arbitrary recurrent targets not covered by the finite-color
certificate remain possible sites for a computation encoding. No reduction from
unrestricted pattern containment or an undecidable word theory is imported.

Check empty words, undefined transitions, Bad, diagonal/final-column flags,
multiple finals, overlap at a last target, dead pairs, and every candidate word
in small exhaustive corpora. A finite regression does not prove a class theorem.

## Outcome of this attempt

Steps 2 and 4 have ordinary proofs and an implemented sufficient certificate.
A native terminal-period argument supersedes the proposed external backend for
this specific class: infinite productive last-target tail languages supply a
short witness, and finite languages have bounded-length tails with exact finite
pattern-avoidance products. The resulting bound is k^2+k-2. The formula in Step 3
remains an alternative exact formulation, not a dependency of the native solver.

Step 5 is false for the proposed static certificate. Both the known six-state
NO barrier and the positive (2,3) modular family remain UNKNOWN. Hence this
attempt discharges a certified recurrent class, not unrestricted completeness.
The fixed-word source-scheme lower bounds are neither reused as upper bounds
nor contradicted by a theorem whose hypotheses those instances fail.

Notation clarification: Step 3 used an informal haystack-first Contains. The
condition is precisely that needle Za is not a factor of haystack XZ. The cited
paper places the needle first; the implementation uses named fields.
