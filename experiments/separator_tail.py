"""Shared-reference tail search over arbitrary data letters and one separator.

This combines the existing semantic-tail and synchronous-separator ideas. A
supplied H is an exact relaxation, NOT a universal bound. The nine-state
counterexample in flag_transport survives every H without flag relocation.
Only the original binary automaton is a subtype/BorderAvoid input; 01# is an
internal representation of the exact paired binary compiler.
"""
from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import Optional

from border_lab import Instance,witness,border_witness
from lastflag_spectrum import (ActionMonoid, _combined_machine, _terms, _heads,
                              boundary_slice, _validate, realize_template,
                              is_lastflag, ResourceLimit as MonoidLimit)

class ResourceLimit(RuntimeError):
    pass

@dataclass(frozen=True)
class Limits:
    states: Optional[int]=100000
    steps: Optional[int]=1000000
    descriptors: Optional[int]=100000
    schemas: Optional[int]=20000
    blocks: Optional[int]=8
    monoid: Optional[int]=20000
    combinations: Optional[int]=2000000
    def __post_init__(self):
        for name,value in self.__dict__.items():
            if value is not None and (type(value) is not int or value<1):
                raise ValueError(name+' must be a positive integer or None')

def cap(n,maximum,name):
    if maximum is not None and n>maximum:raise ResourceLimit(name+' cap')

def reach(graph,starts):
    seen=set(starts);todo=list(starts)
    for p in todo:
        for q in graph[p]:
            if q>=0 and q not in seen:seen.add(q);todo.append(q)
    return seen

def _validate_marker(I,marker):
    if not _validate(I):raise ValueError('Terminal accepting states are required')
    if marker not in I.alphabet or marker=='_':raise ValueError('Invalid marker')
    if '_' in I.alphabet:raise ValueError('Underscore is reserved for convolution padding')
    mi=I.alphabet.index(marker)
    if any(q in I.final and a!=mi for row in I.delta for a,q in enumerate(row)):
        raise ValueError('Every nonempty accepted word must enter final on the marker')

def tail_safe(I,word,marker,H):
    if type(H) is not int or H<0:raise ValueError('H must be nonnegative')
    if not I.admissible(word):return False
    c=I.run(word);n=len(word)
    if any((p,p) in I.flags or (p,c[-1]) in I.flags for p in c):return False
    return not any((c[i],c[j]) in I.flags and word[j:].count(marker)<=H
                   and word[i:].startswith(word[j:])
                   for i in range(n) for j in range(i+1,n))

def _plain(J):
    heads=_heads(J)
    return next((heads[f] for f in sorted(J.final) if f in heads),None)

def _pending(mask,eq,hits,r):
    out=0
    for j in range(1,r):
        if mask>>j&1 and eq>>j&1:
            if j==r-1:return None
            out|=1<<(j+1)
    if hits>>(r-1)&1:return None
    for j in range(r-1):
        if hits>>j&1:out|=1<<(j+1)
    return out

def _observe(q,eq,hits,done,refs,flags):
    if not done:
        for j,rj in enumerate(refs):
            if rj>=0 and eq>>j&1 and (q,rj) in flags:hits|=1<<j
    return hits

def _source_step(desc,columns,refs,pred,flags):
    out=set()
    for end,q,eq,hits,done in desc:
        choices=[('_',q,True)]
        if not done:choices.extend((a,p,False) for a,p in pred[q])
        for a,p,finished in choices:
            e=eq
            for j,b in enumerate(columns):
                if a!=b:e&=~(1<<j)
            h=_observe(p,e,hits,finished,refs,flags)
            out.add((end,p,e,h,finished))
    return frozenset(out)

def _observations(J,mi,desc,pred):
    reverse=[[p for _,p in row] for row in pred];closures={};out=set()
    for end,q,eq,hits,done in desc:
        if done:starts={q}
        else:
            assert eq==0
            if q not in closures:closures[q]=reach(reverse,[q])
            starts=closures[q]
        for start in starts:out.add((start,J.delta[end][mi],eq,hits,end))
    return out

def _prefix(J,cut,obs,equal,bit,r,allow,limits):
    def same(i,j):return i==j or bool(equal&bit[min(i,j),max(i,j)])
    reject=sum(1<<t for t in range(1,r) if all(same(h,t+h) for h in range(r-t)))
    edges={}
    for o in sorted(obs):edges.setdefault(o[0],[]).append(o)
    first=(J.start,0);parent={first:None};todo=deque([first])
    while todo:
        q,mask=state=todo.popleft()
        if q==cut and not mask&reject:
            out=[]
            while parent[state] is not None:state,o=parent[state];out.append(o)
            return list(reversed(out))
        if not allow:continue
        for o in edges.get(q,()):
            nm=_pending(mask,o[2],o[3],r)
            if nm is None:continue
            nxt=(o[1],nm)
            if nxt not in parent:
                cap(len(parent)+1,limits.states,'Prefix state')
                parent[nxt]=(state,o);todo.append(nxt)
    return None

def _reverse_path(pred,start,target):
    parent={start:None};todo=deque([start])
    while todo:
        p=todo.popleft()
        if p==target:
            # Traversal goes right-to-left; reconstruct in forward word order.
            out=[]
            while parent[p] is not None:p,a=parent[p];out.append(a)
            return ''.join(out)
        for a,q in pred[p]:
            if q not in parent:parent[q]=(p,a);todo.append(q)
    return None

def _recover(J,mi,schema,refs,desired,pred,limits):
    """Finite replay of the common-reference source set; no unary assumption."""
    start,target,eq,hits,end=desired
    traces=[]
    for (begin,stop,_),word in zip(schema,refs):
        trace=[begin]
        for a in word:trace.append(J.delta[trace[-1]][J.alphabet.index(a)])
        assert trace[-1]==stop
        traces.append(trace)
    r=len(refs);all_eq=(1<<r)-1
    coords=tuple(trace[-1] for trace in traces)
    first=(end,all_eq,_observe(end,all_eq,0,False,coords,J.flags),False)
    states={first:''};M=max(map(len,refs),default=0)
    for depth in range(1,M+2):
        columns=tuple(u[-depth] if depth<=len(u) else '_' for u in refs)
        coords=tuple(t[len(t)-1-depth] if depth<=len(t)-1 else -1 for t in traces)
        out={}
        for (q,e,h,done),word in sorted(states.items()):
            choices=[('_',q,True)]
            if not done:choices.extend((a,p,False) for a,p in pred[q])
            for a,p,finished in choices:
                ne=e
                for j,b in enumerate(columns):
                    if a!=b:ne&=~(1<<j)
                nh=_observe(p,ne,h,finished,coords,J.flags)
                key=(p,ne,nh,finished)
                out.setdefault(key,word if a=='_' else a+word)
        cap(len(out),limits.descriptors,'Source replay descriptor')
        states=out
    for (q,e,h,done),word in sorted(states.items()):
        if (e,h)!=(eq,hits):continue
        prefix='' if q==start else None
        if not done and prefix is None:prefix=_reverse_path(pred,q,start)
        if prefix is not None:
            result=prefix+word
            assert len(result)<=M+len(J.delta)
            # Independent reconstruction audit of the chosen observation.
            tr=[start]
            for a in result:tr.append(J.delta[tr[-1]][J.alphabet.index(a)])
            assert tr[-1]==end and J.delta[end][mi]==target
            actual_eq=sum(1<<j for j,u in enumerate(refs) if result==u)
            actual_hit=0
            for j,u in enumerate(refs):
                for t in range(min(len(result),len(u))+1):
                    if result[len(result)-t:]==u[len(u)-t:] and (tr[len(result)-t],traces[j][len(u)-t]) in J.flags:
                        actual_hit|=1<<j;break
            assert (actual_eq,actual_hit)==(eq,hits)
            return result
    raise AssertionError('A certified observation had no common-reference realization')

def solve_schema(J,marker,schema,allow,limits=Limits()):
    r=len(schema);mi=J.alphabet.index(marker)
    pairs=tuple((i,j) for i in range(r) for j in range(i+1,r))
    bit={p:1<<i for i,p in enumerate(pairs)}
    guard={p:sum(bit[p[0]+h,p[1]+h] for h in range(1,r-p[1])) for p in pairs}
    pred=[[] for _ in J.delta]
    for p,row in enumerate(J.delta):
        for ai,q in enumerate(row):
            if ai!=mi and q>=0:pred[q].append((J.alphabet[ai],p))
    ends=[p for p,row in enumerate(J.delta) if row[mi]>=0] if allow else []
    all_eq=(1<<len(pairs))-1;src_eq=(1<<r)-1
    def ref_hit(coords,eq,hits):
        for i,j in pairs:
            if min(coords[i],coords[j])>=0 and eq&bit[i,j] and (coords[i],coords[j]) in J.flags:
                hits|=bit[i,j]
        if any(hits&bit[p] and guard[p]==0 for p in pairs):return None
        return hits
    coords=tuple(end for _,end,_ in schema);hits=ref_hit(coords,all_eq,0)
    if hits is None:return dict(status='NO',states=0,steps=0)
    desc=frozenset((p,p,src_eq,_observe(p,src_eq,0,False,coords,J.flags),False) for p in ends)
    cap(len(desc),limits.descriptors,'Initial descriptor')
    first=(coords,all_eq,hits,desc);parent={first:None};todo=deque([first]);steps=0
    while todo:
        coords,eq,hits,desc=state=todo.popleft()
        if all(q<0 for q in coords):
            if any(hits&bit[p] and eq&guard[p]==guard[p] for p in pairs):continue
            prefix=_prefix(J,schema[0][0],_observations(J,mi,desc,pred),eq,bit,r,allow,limits)
            if prefix is None:continue
            cols=[];at=state
            while parent[at] is not None:at,col=parent[at];cols.append(col)
            refs=tuple(''.join(col[j] for col in cols if col[j]!='_') for j in range(r))
            earlier=tuple(_recover(J,mi,schema,refs,o,pred,limits) for o in prefix)
            return dict(status='YES',word=''.join(u+marker for u in earlier+refs),
                        states=len(parent),steps=steps,prefix_blocks=len(earlier),reference_blocks=r)
        options=[]
        for j,q in enumerate(coords):
            choices=[('_',-1)] if q<0 else list(pred[q])
            if q>=0 and q==schema[j][0]:choices.append(('_',-1))
            options.append(choices)
        for choice in product(*options):
            steps+=1;cap(steps,limits.steps,'Reference transition')
            columns=tuple(a for a,_ in choice);nc=tuple(p for _,p in choice);ne=eq
            for i,j in pairs:
                if columns[i]!=columns[j]:ne&=~bit[i,j]
            nh=ref_hit(nc,ne,hits)
            if nh is None:continue
            nd=_source_step(desc,columns,nc,pred,J.flags)
            cap(len(nd),limits.descriptors,'Source descriptor')
            nxt=(nc,ne,nh,nd)
            if nxt not in parent:
                cap(len(parent)+1,limits.states,'Reference state')
                parent[nxt]=(state,columns);todo.append(nxt)
    return dict(status='NO',states=len(parent),steps=steps)

def _schemas(J,marker,H,limits):
    mi=J.alphabet.index(marker)
    graph=[[q for a,q in enumerate(row) if a!=mi and q>=0] for row in J.delta]
    closures=[sorted(reach(graph,[p])) for p in range(len(graph))]
    f=next(iter(J.final));count=0
    for r in range(1,H+1):
        for cut in range(len(graph)) if r==H else [J.start]:
            todo=[(cut,())]
            while todo:
                at,scheme=todo.pop();count+=1;cap(count,limits.schemas,'Schema prefix')
                if at==f:
                    if len(scheme)==r:yield scheme,r==H
                    continue
                if len(scheme)>=r:continue
                for end in reversed(closures[at]):
                    after=J.delta[end][mi]
                    if after>=0:todo.append((after,scheme+((at,end,after),)))

def solve_slice(J,marker,H,limits=Limits()):
    if type(H) is not int or H<0:raise ValueError('H must be nonnegative')
    count=0
    try:
        if H==0 or J.start in J.final:
            word=_plain(J)
            return dict(status='NO',schemas=0) if word is None else dict(status='YES',word=word,schemas=0)
        cap(H,limits.blocks,'Requested marker bound')
        for schema,allow in _schemas(J,marker,H,limits):
            count+=1;answer=solve_schema(J,marker,schema,allow,limits)
            if answer['status']=='YES':
                assert tail_safe(J,answer['word'],marker,H)
                return dict(answer,schemas=count)
        return dict(status='NO',schemas=count)
    except ResourceLimit as error:return dict(status='UNKNOWN',reason=str(error),schemas=count)

def relaxed_decision(I,marker,H,limits=Limits()):
    _validate_marker(I,marker)
    if type(H) is not int or H<0:raise ValueError('H must be nonnegative')
    if witness(I,''):return dict(status='YES',word='',actual_witness=True,slices=[])
    rows=[];unknown=False
    for f in sorted(I.final):
        item=boundary_slice(I,f)
        if item is None:continue
        J,mapping=item;answer=solve_slice(J,marker,H,limits)
        rows.append(dict(final=f,mapping=mapping,result=answer))
        if answer['status']=='YES':
            word=answer['word'];actual=witness(I,word)
            assert tail_safe(I,word,marker,H) and actual==border_witness(I,word)
            return dict(status='YES',word=word,actual_witness=actual,slices=rows)
        unknown|=answer['status']=='UNKNOWN'
    return dict(status='UNKNOWN' if unknown else 'NO',slices=rows)


def _components(edges):
    """Iterative SCC calculation; generated action graphs are fully reachable."""
    back=[[] for _ in edges]
    for p,row in enumerate(edges):
        for q in row:back[q].append(p)
    seen=set();order=[]
    for root in range(len(edges)):
        if root in seen:continue
        seen.add(root);stack=[(root,0)]
        while stack:
            p,i=stack[-1]
            if i==len(edges[p]):order.append(p);stack.pop();continue
            q=edges[p][i];stack[-1]=(p,i+1)
            if q not in seen:seen.add(q);stack.append((q,0))
    comp=[-1]*len(edges);number=0
    for root in reversed(order):
        if comp[root]>=0:continue
        comp[root]=number;stack=[root]
        while stack:
            p=stack.pop()
            for q in back[p]:
                if comp[q]<0:comp[q]=number;stack.append(q)
        number+=1
    return comp


def _weighted_fibres(edges,alphabet,marker):
    """Exact maximum #marker per action fibre, or a positive-cycle cause."""
    mi=alphabet.index(marker);comp=_components(edges)
    cause={};todo=deque()
    for p,row in enumerate(edges):
        q=row[mi]
        if comp[p]==comp[q]:cause[p]=(p,mi,q);todo.append(p)
    while todo:
        p=todo.popleft()
        for q in edges[p]:
            if q not in cause:cause[q]=cause[p];todo.append(q)
    maximum=[-1]*len(edges);attain=[None]*len(edges)
    if 0 not in cause:
        maximum[0]=0;attain[0]='';todo=deque([0]);queued={0}
        while todo:
            p=todo.popleft();queued.remove(p)
            for ai,q in enumerate(edges[p]):
                candidate=maximum[p]+int(ai==mi)
                if q not in cause and candidate>maximum[q]:
                    maximum[q]=candidate;attain[q]=attain[p]+alphabet[ai]
                    if q not in queued:queued.add(q);todo.append(q)
    for p in cause:maximum[p]=None
    assert all(m is None or m>=0 for m in maximum)
    return maximum,attain,cause,comp


def _action_path(edges,alphabet,start,target,allowed=None):
    parent={start:None};todo=deque([start])
    while todo:
        p=todo.popleft()
        if p==target:
            out=[]
            while parent[p] is not None:p,a=parent[p];out.append(a)
            return ''.join(reversed(out))
        for a,q in zip(alphabet,edges[p]):
            if q not in parent and (allowed is None or q in allowed):
                parent[q]=(p,a);todo.append(q)
    raise AssertionError('No certified action path')


def spectrum_slice(J,marker,limits=Limits()):
    """Exact supremum of last-aligned separator counts on a normalized slice.

    This is the established weighted joint-action construction over the
    INTERNAL alphabet 01#, not a new universal good-witness bound.
    """
    _validate_marker(J,marker)
    if len(J.final)!=1 or J.bad:raise ValueError('A normalized single-final slice is required')
    f=next(iter(J.final))
    if any(p==q or q==f for p,q in J.flags):raise ValueError('Boundary exclusions are required')
    roots=[g for g in J.flags if f not in g and g[0]!=g[1]]
    counts={'checks':0,'templates':0};H=0;best=None
    if not roots:return dict(status='FINITE',H=0,monoid_states=0,**counts,maximum_certificate=None)
    try:
        gens,pi,po,sink=_combined_machine(J)
        mon=ActionMonoid.build(gens,J.alphabet,limits.monoid)
        maximum,attain,cause,comp=_weighted_fibres(mon.edges,J.alphabet,marker)
        heads=_heads(J)
        for p,ai,bi,e in _terms(J,mon,pi,po,sink,limits.combinations,counts):
            if p not in heads:continue
            cert=dict(head=heads[p],u=mon.representatives[ai],v=mon.positive[bi],exponent=e)
            ma,mb=maximum[ai],maximum[bi]
            if ma is None or (e>1 and mb is None):
                factor,idx=('u',ai) if ma is None else ('v',bi)
                at,letter,after=cause[idx]
                allowed={v for v,c in enumerate(comp) if c==comp[at]}
                pump=dict(prefix=mon.representatives[at],
                          loop=J.alphabet[letter]+_action_path(mon.edges,J.alphabet,after,at,allowed),
                          suffix=_action_path(mon.edges,J.alphabet,at,idx),factor=factor)
                cert['pump']=pump
                sample=realize_template(cert)
                assert is_lastflag(J,**sample) and marker in pump['loop']
                return dict(status='UNBOUNDED',monoid_states=len(mon.actions),**counts,
                            pumping_certificate=cert)
            value=e*ma+(e-1)*(mb if e>1 else 0)
            if value>H or best is None:
                H=value;cert['u']=attain[ai]
                if e>1:cert['v']=attain[bi] or mon.positive[bi]
                sample=realize_template(cert)
                assert is_lastflag(J,**sample)
                assert sample['word'][sample['j']:].count(marker)==H
                best=cert
        return dict(status='FINITE',H=H,monoid_states=len(mon.actions),**counts,
                    maximum_certificate=best)
    except (ResourceLimit,MonoidLimit) as error:
        return dict(status='UNKNOWN',reason=str(error),**counts)


def semantic_decision(I,marker,limits=Limits()):
    """Sound partial decision: bounded marked spectra make tail search exact.

    Any unbounded/capped slice prevents NO. An actual checked witness on
    another slice still permits YES. None caps give a finite structural test,
    not a total unrestricted witness decision.
    """
    _validate_marker(I,marker)
    if witness(I,''):return dict(status='YES',word='',slices=[])
    rows=[];unknown=False
    for f in sorted(I.final):
        normalized=boundary_slice(I,f)
        if normalized is None:continue
        J,mapping=normalized
        analysis=spectrum_slice(J,marker,limits)
        row=dict(final=f,mapping=mapping,analysis=analysis);rows.append(row)
        if analysis['status']!='FINITE':unknown=True;continue
        answer=solve_slice(J,marker,analysis['H'],limits);row['result']=answer
        if answer['status']=='YES':
            assert witness(I,answer['word']) and border_witness(I,answer['word'])
            return dict(status='YES',word=answer['word'],slices=rows)
        unknown|=answer['status']=='UNKNOWN'
    return dict(status='UNKNOWN' if unknown else 'NO',slices=rows)
