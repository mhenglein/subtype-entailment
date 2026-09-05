# Nonflat continuation: C035-C037 and E025

Base checkpoint: `5ee18c6`. Extends [C030-C034](TERMINAL.md).
**Unrestricted Problem 1.7 is not settled.** New statements have written
proofs and reproducible checks, not Lean formalization or priority claims.

| ID | Statement | Scope |
|---|---|---|
| C035 | A six-state, two-flag terminal instance has exact witness language `0 (0^r 1, r>=2)^+ 101`; every witness uses a nonflat edge support. | Refutes completeness of enumerating flat edge subautomata. Word-preserving realization uses 13 subtype variables through C030. Does not refute richer bounded skeletons. |
| C036 | Two agreeing suffix occurrences on a terminal accepted run cannot merge at any aligned position. Prefix-ordered suffix chains have height at most k. | Any finite alphabet. Terminal acceptance is essential; no bound on suffix lengths follows. |
| C037 | If the productive synchronized graph after the last flagged pair is acyclic, an effective H makes Witness equal Necessary(H,0) on each final slice. | Exact regular witness-language certificate for some nonflat instances. H bounds the shortest detected violation, not the successful budget B. Cyclic residuals remain UNKNOWN. |

[Full statements and proofs](../notes/2026-09-05-nonflat-overlap.md).
[Implementation](../experiments/terminal_overlap.py).

## E025

```sh
python3 experiments/check_nonflat_overlap.py
```

[Saved result](../results/nonflat-overlap.json): all 65,536 normalized
four-state cases (45,158 YES, 20,090 NO, 288 UNKNOWN for the new certificate);
600 additional seeded instances; 62,220 predicate comparisons; 8,191 word
checks for the obstruction; 521 exact canonical models; all 128 edge
restrictions, with every proper restriction proved empty.

The new certificate decides 2,136 nonflat cases in the four-state corpus.
Those cases were already decided by C034; they are cross-checks, not a new
small-state result. The all-state content is the conditional theorem C037.

## Next target

Study productive cycles of UNFLAGGED synchronized pairs, not merely nonflat
candidate graphs. Such cycles are where this certificate can lose its finite
detection bound. Their presence is not a negative answer. A finite effective
witness cover still needs a proof; selecting only flat edge restrictions is
now explicitly ruled out by C035.
