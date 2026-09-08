"""Exact fixed-H marker-tail relaxation for paired macro-token instances.

This lifts the September 8 semantic-tail pending monitor from unary raw data to
C053/C056's regular binary data blocks. Unlike target_frontier.solve_schema,
earlier source blocks may revisit every flag target and may traverse marker
cycles. For supplied H the computation is finite and exact for comparisons
whose target suffix contains at most H macro separators.

This is a certified relaxation, not an unrestricted BorderAvoid decision.
Resource exhaustion is UNKNOWN, never NO. See
notes/2026-09-08-macro-marker-tails.md.
"""
from collections import deque
from itertools import product

from border_lab import witness, border_witness
from target_frontier import (Limits, SearchCap, parse_macro, _pred,
    _source_observe, source_step, complete_observations, prefix_path,
    recover_block)
from terminal_realization import validate


def tail_schemas(macro,H,cap=None):
    if type(H) is not int or H<0: raise ValueError('H must be a nonnegative integer')
    data={p:[q for q in macro.delta[p][:2] if q>=0] for p in macro.delta}
    reach_data={}
    for root in macro.delta:
        seen,todo={root},[root]
        for p in todo:
            for q in data[p]:
                if q not in seen: seen.add(q); todo.append(q)
        reach_data[root]=seen
    seen_prefixes=0
    for r in range(1,H+1):
        cuts=sorted(macro.delta) if r==H else [macro.start]
        for cut in cuts:
            todo=[(cut,())]
            while todo:
                at,schema=todo.pop(); seen_prefixes+=1
                if cap is not None and seen_prefixes>cap: raise SearchCap('Macro marker-tail schema cap')
                if at==macro.final:
                    if len(schema)==r: yield schema,(r==H)
                    continue
                if len(schema)>=r: continue
                for end in sorted(reach_data[at],reverse=True):
                    after=macro.delta[end][2]
                    if after>=0: todo.append((after,schema+((at,end,after),)))


def solve_schema(macro,schema,allow_prefix,limits=Limits()):
    r=len(schema); pairs=tuple((i,j) for i in range(r) for j in range(i+1,r))
    bit={pair:1<<n for n,pair in enumerate(pairs)}
    all_ref_eq=(1<<len(pairs))-1; all_src_eq=(1<<r)-1
    pred=_pred(macro,set(macro.delta)); cut=schema[0][0]
    ends=[q for q in macro.delta if macro.delta[q][2]>=0] if allow_prefix else []
    guard={p:sum(bit[p[0]+h,p[1]+h] for h in range(1,r-p[1])) for p in pairs}

    def ref_observe(coords,eq,hits):
        for i,j in pairs:
            if coords[i]>=0 and coords[j]>=0 and eq&bit[i,j] and (coords[i],coords[j]) in macro.flags:
                hits|=bit[i,j]
        if any(hits&bit[p] and guard[p]==0 for p in pairs): return None
        return hits

    coords=tuple(end for _,end,_ in schema); rh=ref_observe(coords,all_ref_eq,0)
    if rh is None: return dict(status='NO',reason='Unavoidable empty-tail reference comparison',states=0,transitions=0)
    descriptors=frozenset((q,q,all_src_eq,_source_observe(q,all_src_eq,0,False,coords,macro.flags),False) for q in ends)
    if limits.descriptors is not None and len(descriptors)>limits.descriptors:
        return dict(status='UNKNOWN',reason='Initial descriptor cap',states=0,transitions=0)
    first=(coords,all_ref_eq,rh,descriptors); parent={first:None}; todo=deque([first]); steps=0
    maximum_descriptors=len(descriptors)
    while todo:
        coords,eq,hits,descriptors=state=todo.popleft()
        if all(q<0 for q in coords):
            if any(hits&bit[p] and (eq&guard[p])==guard[p] for p in pairs): continue
            if allow_prefix:
                observations=complete_observations(macro,descriptors,pred)
                try: path=prefix_path(macro,cut,observations,eq,bit,r,limits.states)
                except SearchCap as error:
                    return dict(status='UNKNOWN',reason=str(error),states=len(parent),transitions=steps)
                if path is None: continue
            else:
                if cut!=macro.start: continue
                path=[]
            cols=[]; cursor=state
            while parent[cursor] is not None:
                cursor,col=parent[cursor]; cols.append(col)
            cols.reverse()
            refs=tuple(''.join(col[j] for col in cols if col[j]!='_')[::-1] for j in range(r))
            prefix=[]
            for obs in path:
                u=recover_block(macro,schema,refs,obs,pred,limits.reconstruction)
                if u is None: return dict(status='UNKNOWN',reason='Witness reconstruction cap',states=len(parent),transitions=steps)
                prefix.append(u)
            return dict(status='YES',word=macro.expand(tuple(prefix)+refs),prefix_blocks=prefix,
                        reference_blocks=refs,reference_schema=schema,states=len(parent),transitions=steps,
                        max_descriptors=maximum_descriptors)
        options=[]
        for j,q in enumerate(coords):
            if q<0: options.append([('_',-1)])
            else:
                xs=list(pred[q])
                if q==schema[j][0]: xs.append(('_',-1))
                options.append(xs)
        for choices in product(*options):
            steps+=1
            if limits.transitions is not None and steps>limits.transitions:
                return dict(status='UNKNOWN',reason='Reference transition cap',states=len(parent),transitions=steps)
            column=tuple(a for a,_ in choices); nc=tuple(q for _,q in choices); ne=eq
            for i,j in pairs:
                if column[i]!=column[j]: ne&=~bit[i,j]
            nh=ref_observe(nc,ne,hits)
            if nh is None: continue
            nd=source_step(descriptors,column,nc,pred,macro.flags)
            maximum_descriptors=max(maximum_descriptors,len(nd))
            if limits.descriptors is not None and len(nd)>limits.descriptors:
                return dict(status='UNKNOWN',reason='Source descriptor cap',states=len(parent),transitions=steps)
            nxt=(nc,ne,nh,nd)
            if nxt not in parent:
                if limits.states is not None and len(parent)>=limits.states:
                    return dict(status='UNKNOWN',reason='Reference state cap',states=len(parent),transitions=steps)
                parent[nxt]=(state,column); todo.append(nxt)
    return dict(status='NO',reason='Finite macro tail graph exhausted',states=len(parent),transitions=steps,
                max_descriptors=maximum_descriptors)


def _boundary_word(macro,limit=None):
    """Find any macro-accepted word; H=0 imposes no proper comparisons."""
    parent={macro.start:None}; todo=deque([macro.start]); steps=0
    while todo:
        p=todo.popleft()
        if p==macro.final:
            symbols=[]; q=p
            while parent[q] is not None:
                q,a=parent[q]; symbols.append('01#'[a])
            text=''.join(reversed(symbols))
            if not text.endswith('#'): raise AssertionError('Formatted candidate must end in marker')
            blocks=tuple(text[:-1].split('#'))
            return macro.expand(blocks)
        for a,q in enumerate(macro.delta[p]):
            if q>=0 and q not in parent:
                steps+=1
                if limit is not None and steps>limit: raise SearchCap('H=0 reachability cap')
                parent[q]=(p,a); todo.append(q)
    return None


def solve_macro(macro,H,limits=Limits()):
    """Decide the supplied-H macro-marker relaxation exactly."""
    if type(H) is not int or H<0: raise ValueError('H must be a nonnegative integer')
    if macro.start==macro.final: return dict(status='YES',word='',schemas=0)
    if H==0:
        try: word=_boundary_word(macro,limits.transitions)
        except SearchCap as error: return dict(status='UNKNOWN',reason=str(error),schemas=0)
        return (dict(status='NO',reason='Boundary-safe macro slice empty',schemas=0) if word is None
                else dict(status='YES',word=word,schemas=0,reason='H=0 boundary-safe reachability'))
    total=0; unresolved=False
    try:
        for schema,allow in tail_schemas(macro,H,limits.schemas):
            total+=1; out=solve_schema(macro,schema,allow,limits)
            if out['status']=='YES': return dict(status='YES',word=out['word'],schemas=total,result=out)
            if out['status']!='NO': unresolved=True
    except SearchCap as error:
        return dict(status='UNKNOWN',reason=str(error),schemas=total)
    return dict(status='UNKNOWN' if unresolved else 'NO',schemas=total,
                reason='Capped schema' if unresolved else 'All fixed-H macro schemas exhausted')


def macro_tail_decision(instance,H,limits=Limits()):
    """Exact supplied-H relaxation on every paired-token terminal slice."""
    validate(instance)
    if witness(instance,''): return dict(status='YES',word='',slices=[])
    rows=[]; unresolved=False
    for final in sorted(instance.final):
        fmt,macro=parse_macro(instance,final,'paired'); row=dict(final=final,format=fmt); rows.append(row)
        if fmt['status']=='EMPTY_SLICE': continue
        if macro is None: unresolved=True; row['status']='UNKNOWN'; continue
        out=solve_macro(macro,H,limits); row['search']=out
        if out['status']=='YES':
            assert witness(instance,out['word']) and border_witness(instance,out['word'])
            return dict(status='YES',word=out['word'],slices=rows)
        if out['status']!='NO': unresolved=True
    return dict(status='UNKNOWN' if unresolved else 'NO',slices=rows,
                reason='Unformatted/capped slice' if unresolved else 'All fixed-H paired slices exhausted')
