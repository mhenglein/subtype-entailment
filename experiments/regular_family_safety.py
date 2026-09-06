"""Complete universal witness check for a supplied REGULAR family, arbitrary I.

This answers whether every domain word is a witness, NOT whether some domain
word is a witness. A failing answer carries a concrete member and a violation.
Finite transition-monoid exhaustion proves a positive universal answer. Caps
are explicitly UNKNOWN. There is no SMT dependency.
"""
from collections import deque
from dataclasses import replace
from border_lab import Instance, witness, border_witness
from shared_word_templates import validate_instance


def _domain_path(D):
    todo=deque([D.start]); words={D.start:''}
    while todo:
        p=todo.popleft()
        if p in D.final:
            return words[p]
        for a,q in enumerate(D.delta[p]):
            if q>=0 and q not in words:
                words[q]=words[p]+str(a); todo.append(q)
    return None


def _check_caps(**caps):
    if any(x is not None and (type(x) is not int or x<1) for x in caps.values()):
        raise ValueError('Caps must be positive integers or None')


def check_regular_family(I,D,max_monoid=5000,max_trials=1000000):
    validate_instance(I); validate_instance(D)
    _check_caps(max_monoid=max_monoid,max_trials=max_trials)
    if D.flags or D.bad:
        raise ValueError('Domain must be an unannotated partial DFA')
    terminal=all(all(q<0 for q in I.delta[f]) for f in I.final)
    member=_domain_path(D)
    if member is None:
        return {'status':'REGULAR_FAMILY_VALID','inhabited':False,'reason':'Domain is empty'}
    # Complete regular check for candidate membership and flagged diagonals.
    # I component -1 remembers every undefined or unsafe prefix permanently.
    initial=(I.start if I.start not in I.bad else -1,D.start,
             (I.start,I.start) in I.flags)
    todo=deque([initial]); paths={initial:''}
    while todo:
        p,d,diag=todo.popleft(); word=paths[p,d,diag]
        if d in D.final and (p<0 or p not in I.final or diag):
            assert D.admissible(word) and not witness(I,word) and not border_witness(I,word)
            return {'status':'COUNTEREXAMPLE','word':word,
                    'reason':'A domain member is inadmissible or has a flagged diagonal',
                    'regular_product_states':len(paths)}
        for a,e in enumerate(D.delta[d]):
            if e<0: continue
            q=I.delta[p][a] if p>=0 else -1
            if q in I.bad: q=-1
            nxt=(q,e,diag or (q>=0 and (q,q) in I.flags))
            if nxt not in paths:
                paths[nxt]=word+str(a);todo.append(nxt)
    # Domain is candidate-safe and has no flagged diagonal. Build its safe
    # reachable product with I. Terminality is only an optional sharper bound.
    init=(I.start,D.start); pair_ids={init:0}; pairs=[init]; heads=['']; delta=[]
    for idx,(p,d) in enumerate(pairs):
        row=[]
        for a in (0,1):
            q,e=I.delta[p][a],D.delta[d][a]
            if q<0 or q in I.bad or e<0:
                row.append(-1);continue
            nxt=(q,e)
            if nxt not in pair_ids:
                pair_ids[nxt]=len(pairs);pairs.append(nxt);heads.append(heads[idx]+str(a))
            row.append(pair_ids[nxt])
        delta.append(tuple(row))
    K=len(pairs); sink=K
    table=[tuple(sink if q<0 else q for q in row) for row in delta]+[(sink,sink)]
    finals={idx for idx,(p,d) in enumerate(pairs) if p in I.final and d in D.final}
    identity=tuple(range(K+1)); reps={identity:''}; nonempty={}; queue=deque([identity])
    while queue:
        t=queue.popleft()
        for a in (0,1):
            u=tuple(table[t[q]][a] for q in range(K+1))
            word=reps[t]+str(a)
            if u not in nonempty: nonempty[u]=word
            if u not in reps:
                if max_monoid is not None and len(reps)>=max_monoid:
                    return {'status':'UNKNOWN','reason':'Transition-monoid cap',
                            'monoid_states':len(reps),'product_states':K}
                reps[u]=word;queue.append(u)
    # For a proper violation w=x y z, y!=epsilon and z prefix y z.
    # Exactly: y=u v, v!=epsilon, z=(u v)^(e-1)u, e>=1.
    # The product orbit permits e<=K; terminal I permits the sharper e<|I|.
    # Equal ACTIONS do not assert equal words: repeated u/v occurrences below
    # use the SAME representative, which preserves both algebra and equality.
    trials=0
    exponent_bound=len(I.delta)-1 if terminal else K
    for A,uw in reps.items():
        for B,vw in nonempty.items():
            Y=tuple(B[A[p]] for p in range(K+1))
            for p in range(K):
                q=Y[p]
                if q==sink or (pairs[p][0],pairs[q][0]) not in I.flags:
                    continue
                end=p
                for exponent in range(1,exponent_bound+1):
                    trials+=1
                    if max_trials is not None and trials>max_trials:
                        return {'status':'UNKNOWN','reason':'Monoid evaluation cap',
                                'monoid_states':len(reps),'product_states':K,'trials':trials}
                    end=Y[end]
                    f=A[end]
                    if f in finals:
                        word=heads[p]+(uw+vw)*exponent+uw
                        assert D.admissible(word) and I.admissible(word)
                        assert not witness(I,word) and not border_witness(I,word)
                        return {'status':'COUNTEREXAMPLE','word':word,
                                'factorization':{'head':heads[p],'u':uw,'v':vw,'exponent':exponent},
                                'flag':[pairs[p][0],pairs[q][0]],
                                'monoid_states':len(reps),'product_states':K,'trials':trials}
                    if end==sink: break
    assert witness(I,member) and border_witness(I,member)
    return {'status':'REGULAR_FAMILY_VALID','inhabited':True,'word':member,
            'monoid_states':len(reps),'product_states':K,'trials':trials,
            'counterexample_length_bound':max(K-1,0)+(2*exponent_bound+1)*len(reps),
            'exponent_bound':exponent_bound,
            'reason':'Complete transition-monoid and bounded-period evaluation exhausted',
            'scope':'Every word in THIS regular family is a witness; not unrestricted witness existence'}
