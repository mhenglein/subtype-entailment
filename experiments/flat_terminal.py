"""Complete finite-skeleton reduction for flat terminal-final automata.

Flat means every productive cyclic SCC has exactly one internal labelled edge
per vertex. Edges leaving an SCC are unrestricted. All repetition counts stay
unbounded in Presburger formulas. A cap or unsupported SCC returns UNKNOWN;
NO is returned only after every schema in a proved complete cover is empty.
"""
from collections import deque
from border_lab import Instance, witness, border_witness
from terminal_realization import validate
from skeleton_presburger import Skeleton, Block


def _reachable(starts, graph):
    seen=set(starts); todo=list(starts)
    for q in todo:
        for r in graph[q]:
            if r not in seen: seen.add(r); todo.append(r)
    return seen


def _components(vertices, edges):
    # Finite reachability equivalence, intentionally simple and auditable.
    reach={q:_reachable([q],edges) for q in vertices}
    remain=set(vertices); components=[]; index={}
    while remain:
        q=min(remain)
        component=frozenset(r for r in remain if r in reach[q] and q in reach[r])
        for r in component: index[r]=len(components)
        components.append(component); remain-=component
    return components,index


def _compact(blocks):
    result=[]
    for b in blocks:
        if not b.word: continue
        if result and not result[-1].repeat and not b.repeat:
            result[-1]=Block(result[-1].word+b.word)
        else: result.append(b)
    return tuple(result)


def flat_schemas(instance, max_schemas=10000):
    """Return a complete cover, or a precise unsupported/resource verdict."""
    validate(instance)
    if any(any(r>=0 for r in instance.delta[f]) for f in instance.final):
        return dict(status='UNKNOWN',reason='Nonterminal accepting state')
    unsafe=instance.bad|frozenset(q for q,r in instance.flags if q==r)
    safe=set(range(len(instance.delta)))-unsafe
    if instance.start not in safe:
        return dict(status='COMPLETE',schemas=[],productive_states=0)
    graph={q:[] for q in safe}; backward={q:[] for q in safe}
    for q in safe:
        for r in instance.delta[q]:
            if r in safe: graph[q].append(r); backward[r].append(q)
    live=_reachable([instance.start],graph)&_reachable(safe&instance.final,backward)
    if instance.start not in live:
        return dict(status='COMPLETE',schemas=[],productive_states=len(live))
    edges={q:[r for r in graph[q] if r in live] for q in live}
    components,ids=_components(live,edges)
    cyclic={}
    for index,component in enumerate(components):
        is_cycle=len(component)>1 or any(r==q for q in component for r in edges[q])
        cyclic[index]=is_cycle
        if is_cycle:
            branching=[q for q in sorted(component)
                       if sum(r in component for r in instance.delta[q])!=1]
            if branching:
                return dict(status='UNKNOWN',reason='Nonflat productive SCC',
                            component=sorted(component),branching_states=branching)
    schemas=[]; pending=[(instance.start,())]
    while pending:
        q,blocks=pending.pop()
        component=components[ids[q]]
        if cyclic[ids[q]]:
            letters=[]; positions=[]; current=q
            while True:
                positions.append(current)
                a,r=next((a,r) for a,r in zip(instance.alphabet,instance.delta[current])
                         if r in component)
                letters.append(a); current=r
                if current==q: break
            assert len(positions)==len(component)
            cycle=''.join(letters)
            for offset,current in enumerate(positions):
                for a,r in zip(instance.alphabet,instance.delta[current]):
                    if r in live and r not in component:
                        pending.append((r,blocks+(Block(cycle,True),Block(cycle[:offset]+a))))
        elif q in instance.final:
            if len(schemas)>=max_schemas:
                return dict(status='UNKNOWN',reason='Schema cap',schemas=schemas)
            schemas.append(_compact(blocks))
        else:
            for a,r in zip(instance.alphabet,instance.delta[q]):
                if r in live: pending.append((r,blocks+(Block(a),)))
    return dict(status='COMPLETE',schemas=schemas,productive_states=len(live),
                cyclic_components=sum(cyclic.values()))


def decide_flat_terminal(instance, max_schemas=10000, timeout_ms=10000):
    cover=flat_schemas(instance,max_schemas)
    if cover['status']!='COMPLETE':
        return {k:v for k,v in cover.items() if k!='schemas'}
    results=[]
    for blocks in cover['schemas']:
        schema=Skeleton(instance,blocks)
        if not schema.names:
            word=schema.expand([])
            if witness(instance,word):
                assert border_witness(instance,word)
                return dict(status='YES',word=word,schemas_in_cover=len(cover['schemas']))
            result=dict(status='NO_IN_SKELETON',reason='Exact constant-word check')
        else:
            result=schema.solve(timeout_ms=timeout_ms)
            if result['status']=='YES':
                return dict(result,schemas_in_cover=len(cover['schemas']),
                            schema=[(b.word,b.repeat) for b in blocks])
        results.append(result)
    if any(r['status']!='NO_IN_SKELETON' for r in results):
        return dict(status='UNKNOWN',reason='At least one schema unresolved',results=results)
    return dict(status='NO',reason='Every schema in complete flat cover is empty',
                schemas_in_cover=len(cover['schemas']),results=results)
