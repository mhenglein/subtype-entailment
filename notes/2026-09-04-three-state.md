# C022: exact BorderAvoid decision for at most three states

Date: 2026-09-04. **WRITTEN PROOF + REPRO; not Lean-checked.** The proof allows any finite alphabet; the census is binary. State counts refer to abstract automata, not subtype variables. No literature-priority claim.

## Theorem

For a well-formed instance with at most three states, witness existence, existence of a witness of length at most six, nonemptiness of Sufficient(2,0), and nonemptiness of Necessary(1,1) are equivalent. Both length six and budget two are sharp: C021 with m=2,t=1 has unique shortest witness `001000` and exact budget two. Over a binary alphabet the 127 words through length six therefore give a complete decision for this class, not for larger instances.

## Safe removal of an initial segment

If a run of w returns to its initial state s at position h, its suffix w[h:] is a witness whenever w is. Its run and every compared suffix are suffixes of the old run and word with unchanged states. No interior join is created. The same argument preserves Necessary(L,D): retained suffix lengths and position differences are unchanged. We may therefore remove everything through the last return to s. This does not justify deleting arbitrary internal loops.

## Boundary reduction

Fix an accepting state f and delete Bad union {q:G(q,q)} union {q:G(q,f)}. These are exactly diagonal/full and empty-border restrictions. Both witnesses and Necessary(1,1) must obey them. An excluded start or final gives an empty slice. If s=f, epsilon works. With at most two relevant safe states a reachable final has a simple path of length at most one, already a witness.

The remaining case has three distinct states s,u,f. No diagonal or incoming-f flag can affect a safe path. Flags into s become irrelevant after the initial-segment removal.

## The only hard form

If no witness of length at most two exists but f is reachable, a shortest boundary path has the form s --a--> u --b--> f. Distinct a,b would make ab a witness, and absence of G(s,u) would make aa a witness. Thus a=b, G(s,u), and s --a--> u --a--> f. This letter a is unique: an edge s --b--> u with b!=a would give ba, and an edge u --b--> f would give ab. Any edge directly from s to f would be even easier.

For b!=a, delta(s,b) is s or undefined, and delta(u,b) is s,u,or undefined. Once returns to s are removed, only u and f remain after the first letter.

## Three escape patterns

1. If f loops on b!=a, `aab` is a witness (run s,u,f,f). The only relevant proper target is u, whose suffix ab does not prefix aab. Its longest repeated suffix is zero.
2. If f loops on a and u loops on b!=a, `abaa` is a witness (run s,u,u,f,f). Suffixes baa and aa at u do not prefix abaa. No f precedes either u. Its longest repeated suffix is one.
3. If f loops on a and f --b--> u for b!=a, `aabaaa` is a witness (run s,u,f,u,f,f,f). The u suffixes abaaa and aaa do not prefix the word. The only earlier f before the second u reads b, while the target suffix starts with a, also defeating a possible G(f,u). Its longest repeated suffix is two.

All three avoid flags into s since s is not revisited, and all incoming-f/diagonal flags were handled by the slice. Each satisfies Sufficient(2,0).

## Completeness and a finite NO certificate

Suppose no escape pattern exists. Consider an accepting run after its last return to s. Its last edge cannot be u --a--> f: the final suffix a would agree with the initial a and violate G(s,u), already detected by L=1. Its last edge must therefore be a loop at f. The first escape pattern is absent, so the loop is on a.

With an a-loop at f, absence of patterns 2 and 3 means every non-a edge from u or f is undefined or returns to s. Such edges cannot occur in this run. The whole word is therefore a power of a. The comparison between its initial s and first u is then a flagged period-one agreement, already detected by D=1. Hence even Necessary(1,1) is empty.

This proves the complete equivalence, not just a finite-sample observation.

## Guarded larger-input front-end

For each final boundary slice, retain only states reachable from the start and able to reach that final. If at most three remain, the theorem decides the slice. Return YES when a small slice supplies a witness, NO only when all slices are proved empty, and UNKNOWN when a larger unresolved slice remains.

## E017 evidence

`python3 experiments/three_state_decision.py` checks all 4^6 partial binary transition tables and all 2^4 remaining flag sets on (0,1),(1,0),(2,0),(2,1), with start 0 and final 2. The boundary proof justifies this normal form.

Counts: boundary-empty 27,904; short witnesses 36,096; other-letter final loop 384; other-letter middle loop 96; final-to-middle return 64; other hard-form NO cases 992; total 65,536. Every positive word passes forward, reversed, and direct Sufficient(2,0) checks. Every negative independently exhausts Necessary(1,1), with largest graph 65 states and no cap exits. The six-letter front-end rejects inputs larger than three states unless applying the justified live-slice reduction.
