# C021: an exact budget-growth family

Date: 2026-09-04. **WRITTEN PROOF + REPRO; not Lean-checked.** Abstract BorderAvoid only; no subtype realization or literature-priority claim.

For integers m>=2 and 1<=t<m, take states q0,...,qm, start q0, final qm, no Bad states, and the sole flag G={(q0,qt)}. Set delta(qi,0)=q(i+1) for i<m, delta(qm,0)=qm, delta(qm,1)=q1; every other 1-transition is undefined.

Then:

```
B(I(m,t)) = m+t-1
unique shortest witness = 0^m 1 0^(m+t)
shortest length = 2m+t+1
full-boundary budget = m-1.
```

Taking t=m-1 and k=m+1 gives B=2k-4, shortest length 3k-3, and boundary budget k-2. The five-state example has B=6 and unique shortest word `000010000000`. This refutes B<=k, but not any arbitrary computable bound or any superlinear bound. State-minimality for refuting B<=k is not claimed.

## Universal lower bound

An accepted all-zero word violates G(q0,qt), so any witness contains a 1. Let p be its initial zero-run length and r its final zero-run length. Necessarily p>=m. After its last 1 the run is at q1; acceptance requires at least m-1 further zeros, so it passes qt. The suffix beginning at that visit is 0^(r-t+1). If r-t+1<=p, that suffix is a prefix of the whole word, contradicting the flag from q0. Thus r>=p+t>=m+t.

For any word ending in 0^r, every sufficient pair (L,D) has L+D>=r-1. If L>=r the assertion is immediate. If L<r, the reversed prefix 0^(L+1) repeats at shifts through r-L-1, so the sufficient occurrence condition forces D>=r-L-1. Consequently every witness has budget at least m+t-1. Its initial zeros, a 1, and final zeros also force length at least 2m+t+1.

## Matching witness and uniqueness

Let w=0^m 1 0^(m+t). The state q0 occurs only at position zero. The state qt occurs twice: before the 1, where its suffix begins with 0^(m-t)1 rather than 0^m1; and after the 1, where its suffix is 0^(m+1), longer than the initial zero run. Neither is a prefix of w, so no flagged agreement occurs. There are no diagonal or incoming-final flags. Thus w is a witness.

Its suffix 0^(m+t) occurs only at the end: it is longer than the initial zero block and is the entire final zero block. Hence Sufficient(w,m+t-1,0) holds. This attains both lower bounds. Equality in the length bound forces precisely m initial zeros, one 1, and m+t final zeros, proving uniqueness.

## Full-boundary baseline

The sole flag is neither diagonal nor into qm, so the full boundary language is simply the accepted-word language. Every accepted word w starts with at least m zeros, has length at least m, and ends with at least m-1 zeros. Suppose L+D<m-1. Then L<=m-2, so its suffix of length L+1 is 0^(L+1), and the same block occurs at the beginning of w. In the reversed word this gives a repeated initial block at shift |w|-L-1>=m-L-1>D, violating the sufficient condition. Thus every sufficient budget is at least m-1. The accepted word 0^m has budget exactly m-1 and attains this lower bound.

Proper borders therefore add exactly t budget units beyond the full-boundary relaxation.

## Evidence

Run `python3 experiments/check_budget_growth_family.py`. E016 checks all 28 pairs 2<=m<=8, 1<=t<m by complete fixed-budget graph searches and independently verifies returned words. It also enumerates to the shortest word for m<=5, making 70,680 forward/reversed comparisons. A 200,000-state cap per split is explicit; no required search reaches it. The all-parameter theorem rests on the proof above, not extrapolation.
