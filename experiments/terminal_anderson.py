"""Anderson-style source-border certificates for terminal BorderAvoid.

This module implements a sound all-state NO certificate based on a written
adaptation of Anderson et al.'s 6n+1 bound for unbordered words.  The theorem
used here applies to one source state p when its flagged target set is forward
closed among live nonfinal states.  A resource cap returns UNKNOWN, never NO.
"""
from dataclasses import replace
from border_lab import Instance, witness, border_witness
from terminal_realization import validate


def _reach(starts, edges):
    seen=set(starts); todo=list(seen)
    for p in todo:
        for q in edges.get(p,()):
            if q not in seen:
                seen.add(q); todo.append(q)
    return seen


def source_slice(instance, source):
    """Candidate suffix graph from source to any terminal final, with no return.

    Existence of a global witness containing source implies existence of a
    witness suffix from source with no positive return to source: choose the
    last occurrence of source on that witness.  Thus deleting transitions into
    source is sound for an impossibility certificate.
    """
    validate(instance)
    k=len(instance.delta)
    finals=set(instance.final)
    if source in instance.bad or (source,source) in instance.flags:
        return None,set(),set(),dict(status='IMPOSSIBLE_BOUNDARY',reason='bad or diagonal-flagged source')
    # Any flag from source into a terminal final kills every suffix ending there.
    killed={f for f in finals if (source,f) in instance.flags}
    usable_finals=finals-killed
    if not usable_finals:
        return None,set(),set(),dict(status='IMPOSSIBLE_BOUNDARY',reason='all finals flagged from source')
    safe=set(range(k))-set(instance.bad)
    # Remove all positive returns to source.
    delta=[]
    for p,row in enumerate(instance.delta):
        delta.append(tuple(-1 if q==source else q for q in row))
    edges={p:[q for q in delta[p] if q in safe] for p in safe}
    rev={p:[] for p in safe}
    for p,qs in edges.items():
        for q in qs: rev[q].append(p)
    co=_reach(usable_finals,rev)
    live=_reach([source],edges)&co&safe
    usable_finals &= live
    if source not in live or not usable_finals:
        return None,set(),set(),dict(status='EMPTY_SLICE',reason='no safe no-return path to an unflagged final')
    ndelta=tuple(tuple(q if p in live and q in live else -1 for q in row)
                 for p,row in enumerate(delta))
    targets={q for p,q in instance.flags if p==source and q in live and q not in usable_finals}
    # Only the source's flags matter in the local certificate.
    local=Instance(ndelta,frozenset(usable_finals),
                   frozenset((source,q) for q in targets),
                   frozenset(set(range(k))-live),source,instance.alphabet)
    return local,live,targets,dict(status='OK')


def forward_closed_targets(local, live, targets):
    """Closure is needed only before terminal acceptance."""
    finals=set(local.final)
    for q in targets:
        for r in local.delta[q]:
            if r>=0 and r in live and r not in finals and r not in targets:
                return False,(q,r)
    return True,None


def _bounded_exact_search(local, bound, max_nodes=1000000):
    """Enumerate defined safe runs only, through the theorem's finite bound."""
    frontier=[('',local.start)]
    nodes=1
    for depth in range(bound+1):
        next_frontier=[]
        for w,q in frontier:
            if q in local.final and witness(local,w):
                assert border_witness(local,w)
                return dict(status='YES',word=w,nodes=nodes,depth=depth)
            if depth==bound or q in local.final:
                continue
            for ai,a in enumerate(local.alphabet):
                r=local.delta[q][ai]
                if r<0 or r in local.bad:
                    continue
                nodes+=1
                if nodes>max_nodes:
                    return dict(status='UNKNOWN',nodes=nodes,depth=depth,reason='bounded enumeration cap')
                next_frontier.append((w+a,r))
        frontier=next_frontier
    return dict(status='NO',nodes=nodes,depth=bound)


def source_border_certificate(instance, source, max_states=1000000):
    """Prove that no witness can contain source, when the theorem applies.

    Returns IMPOSSIBLE iff complete enumeration through 6n+1 finds no local
    source-clean word and the generalized theorem therefore rules out every
    longer one. POSSIBLE returns a local source-clean word (not necessarily a
    full witness of the original instance). NOT_APPLICABLE means target
    forward-closure fails. UNKNOWN is an explicit enumeration cap.
    """
    local,live,targets,base=source_slice(instance,source)
    if base['status'] in ('IMPOSSIBLE_BOUNDARY','EMPTY_SLICE'):
        return dict(status='IMPOSSIBLE',source=source,reason=base['reason'])
    ok,edge=forward_closed_targets(local,live,targets)
    if not ok:
        return dict(status='NOT_APPLICABLE',source=source,
                    reason='flagged target set is not forward closed',witness_edge=edge,
                    live_states=len(live),targets=sorted(targets))
    n=len(live)
    bound=6*n+1
    out=_bounded_exact_search(local,bound,max_nodes=max_states)
    common=dict(source=source,bound=bound,live_states=n,targets=sorted(targets),
                enumeration_nodes=out.get('nodes'))
    if out['status']=='NO':
        return dict(common,status='IMPOSSIBLE',reason='generalized 6n+1 source-border certificate')
    if out['status']=='YES':
        w=out['word']
        return dict(common,status='POSSIBLE',word=w,word_length=len(w),
                    full_witness=(witness(instance,w) if source==instance.start else None))
    return dict(common,status='UNKNOWN',reason='bounded enumeration cap')

def prune_impossible_sources(instance,max_rounds=None,max_states=300000):
    """Iteratively delete states proved impossible by source certificates.

    This is a sound pruning helper, not a complete decision procedure.
    """
    validate(instance)
    k=len(instance.delta); removed=set(); rounds=[]
    current=instance
    limit=k if max_rounds is None else max_rounds
    for _ in range(limit):
        newly=[]; rows=[]
        for p in range(k):
            if p in removed: continue
            cert=source_border_certificate(current,p,max_states=max_states)
            rows.append(cert)
            if cert['status']=='IMPOSSIBLE': newly.append(p)
        rounds.append(rows)
        if not newly: break
        removed.update(newly)
        bad=frozenset(set(current.bad)|set(newly))
        current=replace(current,bad=bad)
        if current.start in removed: break
    return dict(status='START_IMPOSSIBLE' if current.start in removed else 'PRUNED',
                removed=sorted(removed),rounds=rounds),current

def hybrid_terminal_decision(instance,max_source_nodes=1000000,max_overlap_states=300000):
    """Sound composition: source pruning followed by the C037 overlap decider."""
    from terminal_overlap import bounded_overlap_decision
    pruning,current=prune_impossible_sources(instance,max_states=max_source_nodes)
    if pruning['status']=='START_IMPOSSIBLE':
        return dict(status='NO',reason='start removed by source-border pruning',pruning=pruning)
    out=bounded_overlap_decision(current,max_states=max_overlap_states)
    if out['status']=='YES':
        w=out['word']
        assert witness(instance,w) and border_witness(instance,w)
        return dict(status='YES',word=w,pruning=pruning,overlap=out)
    if out['status']=='NO':
        return dict(status='NO',reason='all witnesses avoid pruned states and pruned instance is empty',pruning=pruning,overlap=out)
    return dict(status='UNKNOWN',pruning=pruning,overlap=out)
