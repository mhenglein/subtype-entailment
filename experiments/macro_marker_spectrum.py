"""Exact separator spectrum for paired macro-token terminal slices.

This is the finite-alphabet last-aligned spectrum theorem instantiated on the
three-symbol macro alphabet {0,1,#}. Cost is 1 only on #.  It therefore ignores
physical zeroes inside paired data token 10 and is invariant under the
synchronous-separator encoding layer.
"""
from collections import deque

from border_lab import witness, border_witness
from macro_marker_tail import solve_macro
from marker_spectrum import _components
from target_frontier import Limits, parse_macro
from terminal_realization import validate


class SpectrumCap(RuntimeError): pass


def _cap(value,limit,message):
    if limit is not None and value > limit: raise SpectrumCap(message)


def _joint(macro):
    states=sorted(macro.delta); k=max(states)+1
    # parse_macro preserves original numeric state ids, so allocate singles by
    # the full numeric range and send absent/non-useful states to sink.
    pairs=[(p,q) for p in states for q in states if p!=q and p!=macro.final]
    ids={pair:k+i for i,pair in enumerate(pairs)}
    sink=k+len(pairs)
    generators=[]
    for a in range(3):
        g=[]
        for p in range(k):
            row=macro.delta.get(p)
            q=row[a] if row is not None else -1
            g.append(q if q>=0 else sink)
        for p,q in pairs:
            rp=macro.delta[p][a]; rq=macro.delta[q][a]
            dest=(rp,rq)
            if rp<0 or rq<0 or rp==macro.final or rp==rq or dest in macro.flags:
                g.append(sink)
            else:
                g.append(ids.get(dest,sink))
        g.append(sink)
        generators.append(tuple(g))
    return generators,ids,{i:p for p,i in ids.items()},sink,k


def _monoid(generators,limits):
    symbols='01#'; identity=tuple(range(len(generators[0])))
    actions=[identity]; ids={identity:0}; reps=['']; positive=[None]; edges=[]
    at=0
    while at<len(actions):
        row=[]
        for a,g in enumerate(generators):
            effect=tuple(g[q] for q in actions[at]); word=reps[at]+symbols[a]
            dest=ids.get(effect)
            if dest is None:
                _cap(len(actions)+1,limits.states,'Macro action-monoid cap')
                dest=len(actions); ids[effect]=dest; actions.append(effect)
                reps.append(word); positive.append(word)
            elif positive[dest] is None:
                positive[dest]=word
            row.append(dest)
        edges.append(tuple(row)); at+=1
    return actions,edges,reps,positive


def _path(edges,start,target,symbols='01#',allowed=None):
    parent={start:None}; todo=deque([start])
    while todo:
        p=todo.popleft()
        if p==target:
            out=[]
            while parent[p] is not None:
                p,a=parent[p]; out.append(symbols[a])
            return ''.join(reversed(out))
        for a,q in enumerate(edges[p]):
            if (allowed is None or q in allowed) and q not in parent:
                parent[q]=(p,a); todo.append(q)
    raise ValueError('No action path')


def _weighted(edges):
    costs=(0,0,1); comp=_components(edges); cause={}; todo=deque()
    for p,row in enumerate(edges):
        for a,q in enumerate(row):
            if costs[a] and comp[p]==comp[q] and p not in cause:
                cause[p]=(p,a,q); todo.append(p)
    while todo:
        p=todo.popleft()
        for q in edges[p]:
            if q not in cause:
                cause[q]=cause[p]; todo.append(q)
    maximum=[-1]*len(edges); longest=[None]*len(edges)
    if 0 not in cause:
        maximum[0]=0; longest[0]=''; todo=deque([0]); queued={0}
        while todo:
            p=todo.popleft(); queued.remove(p)
            for a,q in enumerate(edges[p]):
                if q not in cause and maximum[q] < maximum[p]+costs[a]:
                    maximum[q]=maximum[p]+costs[a]
                    longest[q]=longest[p]+'01#'[a]
                    if q not in queued: queued.add(q); todo.append(q)
    for p in cause: maximum[p]=None
    return maximum,longest,cause,comp


def _lasso(edges,reps,target,cause,comp):
    p,a,q=cause[target]; allowed={v for v,c in enumerate(comp) if c==comp[p]}
    return dict(prefix=reps[p],loop='01#'[a]+_path(edges,q,p,allowed=allowed),
                suffix=_path(edges,p,target))


def _run(macro,w):
    q=macro.start; run=[q]
    for ch in w:
        a='01#'.index(ch); q=macro.delta.get(q,(-1,-1,-1))[a]
        if q<0: return None
        run.append(q)
    return run


def last_aligned(macro,w,i,j):
    run=_run(macro,w)
    if run is None or run[-1]!=macro.final or not 0<=i<j<len(w): return False
    return ((run[i],run[j]) in macro.flags and w[i:].startswith(w[j:]) and
            all((run[i+t],run[j+t]) not in macro.flags for t in range(1,len(w)-j+1)))


def realize(cert,m=1):
    u,v=cert['u'],cert['v']
    if 'pump' in cert:
        p=cert['pump']; value=p['prefix']+p['loop']*m+p['suffix']
        if p['factor']=='u': u=value
        else: v=value
    x,e=cert['head'],cert['exponent']
    w=x+(u+v)*e+u
    return dict(w=w,i=len(x),j=len(x)+len(u)+len(v))


def spectrum_macro(macro,limits=Limits()):
    """Exact maximum # count in realizable last-aligned comparisons."""
    sources=sorted({p for p,q in macro.flags if p!=q and p!=macro.final and q!=macro.final})
    if not sources:
        return dict(status='FINITE',H=0,templates=0,monoid_states=0,checks=0,
                    maximum_certificate=None)
    checks=terms=H=0; best=None
    try:
        generators,pair_ix,pair_of,sink,kfull=_joint(macro)
        actions,edges,reps,positive=_monoid(generators,limits)
        maximum,longest,cause,comp=_weighted(edges)
        heads={macro.start:''}; todo=deque([macro.start])
        while todo:
            p=todo.popleft()
            for a,q in enumerate(macro.delta[p]):
                if q>=0 and q not in heads:
                    heads[q]=heads[p]+'01#'[a]; todo.append(q)
        K=len(macro.delta)
        for ai,A in enumerate(actions):
            for bi,B in enumerate(actions):
                if positive[bi] is None: continue
                for p in sources:
                    if p not in heads: continue
                    checks+=1; _cap(checks,limits.transitions,'Macro spectrum combination cap')
                    q=B[A[p]]
                    if (p,q) not in macro.flags or (p,q) not in pair_ix: continue
                    at=pair_ix[p,q]
                    for e in range(1,K):
                        end=A[at]
                        if end in pair_of and pair_of[end][1]==macro.final:
                            terms+=1
                            cert=dict(head=heads[p],u=reps[ai],v=positive[bi],exponent=e)
                            ma,mb=maximum[ai],maximum[bi]
                            if ma is None or (e>1 and mb is None):
                                factor,index=('u',ai) if ma is None else ('v',bi)
                                cert['pump']=dict(_lasso(edges,reps,index,cause,comp),factor=factor)
                                sample=realize(cert)
                                assert last_aligned(macro,**sample)
                                assert '#' in cert['pump']['loop']
                                return dict(status='UNBOUNDED',H=None,templates=terms,
                                            monoid_states=len(actions),checks=checks,
                                            pumping_certificate=cert)
                            value=e*ma+(e-1)*(mb if e>1 else 0)
                            if value>H or best is None:
                                H=value; cert['u']=longest[ai]
                                if e>1: cert['v']=longest[bi] or positive[bi]
                                sample=realize(cert)
                                assert last_aligned(macro,**sample)
                                assert sample['w'][sample['j']:].count('#')==H
                                best=cert
                        at=B[A[at]]
                        if at==sink: break
        return dict(status='FINITE',H=H,templates=terms,monoid_states=len(actions),
                    checks=checks,maximum_certificate=best)
    except SpectrumCap as error:
        return dict(status='UNKNOWN',reason=str(error),checks=checks,templates=terms)


def semantic_macro_decision(instance,limits=Limits()):
    """Exact when every paired terminal slice has finite macro-separator spectrum."""
    validate(instance)
    if witness(instance,''):
        return dict(status='YES',word='',slices=[])
    rows=[]; unresolved=False
    for final in sorted(instance.final):
        fmt,macro=parse_macro(instance,final,'paired')
        row=dict(final=final,format=fmt); rows.append(row)
        if fmt['status']=='EMPTY_SLICE': continue
        if macro is None:
            unresolved=True; row['analysis']=dict(status='UNKNOWN',reason='Not paired formatted'); continue
        analysis=spectrum_macro(macro,limits); row['analysis']=analysis
        if analysis['status']!='FINITE': unresolved=True; continue
        search=solve_macro(macro,analysis['H'],limits); row['search']=search
        if search['status']=='YES':
            assert witness(instance,search['word']) and border_witness(instance,search['word'])
            return dict(status='YES',word=search['word'],slices=rows)
        if search['status']!='NO': unresolved=True
    return dict(status='UNKNOWN' if unresolved else 'NO',slices=rows,
                reason='Unbounded/unformatted/capped slice' if unresolved else 'All finite macro spectra exhausted')
