"""Exact marker decisions when flagged targets have bounded marker tails.

Unlike marker_certificate.py, productive marker cycles are permitted BEFORE
all effective flag targets. A finite pending-context monitor pumps that prefix.
The guarded whole-block solver still handles each finite resulting schema.
No unrestricted target-localization theorem is asserted.
"""
from collections import deque
from dataclasses import replace
from border_lab import witness,border_witness
from terminal_realization import validate
from word_sync import BinaryDFA,encode_blocks,decode_blocks
from marker_certificate import boundary_slice,reach
from delimited_blocks import BlockSystem,solve_blocks


def target_tail_certificate(I,f,code='paired'):
    validate(I)
    if f not in I.final or code not in ('paired','unary'):
        raise ValueError('Valid final and marker code required')
    J,live=boundary_slice(I,f)
    if J is None:return dict(status='EMPTY_SLICE',final=f),None,None
    if I.start==f:return dict(status='EMPTY_WORD',final=f),J,None
    parser=(((2,1),(0,0),(3,4),(2,1),(4,4)) if code=='paired'
            else ((3,0),(3,0),(3,0),(3,0),(3,0)))
    seen={(J.start,0)};todo=list(seen)
    for q,phase in todo:
        if q==f and phase!=3:
            return dict(status='NOT_APPLICABLE',reason='Safe candidates escape token format',final=f),J,None
        for a,t in enumerate(J.delta[q]):
            if t>=0:
                nxt=t,parser[phase][a]
                if nxt not in seen:seen.add(nxt);todo.append(nxt)
    odd={q for q,p in seen if p in (1,2)} if code=='paired' else set()
    flags={(p,q) for p,q in J.flags if p in live and q in live and p!=f}
    if any(p in odd or q in odd for p,q in flags):
        return dict(status='NOT_APPLICABLE',reason='Unaligned relevant flag endpoint',final=f),J,None
    boundary={q for q,p in seen if p in (0,3)}
    macro={}
    for q in boundary:
        row=[]
        for token in (('10','11','00') if code=='paired' else (None,'1','0')):
            if token is None:row.append(-1);continue
            t=q
            for a in token:
                t=J.delta[t][int(a)]
                if t<0:break
            row.append(t if t in boundary else -1)
        macro[q]=tuple(row)
    graph={p:[q for q in row if q>=0] for p,row in macro.items()}
    reverse={p:[] for p in boundary}
    for p,qs in graph.items():
        for q in qs:reverse[q].append(p)
    productive=reach([J.start],graph)&reach([f],reverse)&boundary
    macro={p:tuple(q if q in productive else -1 for q in row) for p,row in macro.items() if p in productive}
    graph={p:[q for q in row if q>=0] for p,row in macro.items()}
    targets={q for p,q in flags if p in productive and q in productive and q!=f}
    common=dict(final=f,code=code,macro_states=len(productive),targets=sorted(targets))
    if not targets:
        return dict(common,status='NO_EFFECTIVE_FLAGS',target_height=0),J,macro
    relevant=reach(targets,graph)&productive
    distance={f:0}
    for iteration in range(len(relevant)):
        nxt=dict(distance)
        for p in relevant:
            for a,q in enumerate(macro[p]):
                if q in distance:
                    nxt[p]=max(nxt.get(p,-1),distance[q]+int(a==2))
        if nxt==distance:break
        if iteration==len(relevant)-1:
            return dict(common,status='NOT_APPLICABLE',reason='A flag target can reach a productive marker cycle'),J,None
        distance=nxt
    h=max(distance[q] for q in targets)
    assert 1<=h<=len(productive)-1
    prefix_bound=len(productive)*(1<<(h-1))
    return dict(common,status='CERTIFIED',target_height=h,
                prefix_monitor_states=prefix_bound,
                marker_bound=h+prefix_bound),J,macro


def _plain_path(J,macro,code):
    todo=deque([(J.start,'')]);seen={J.start}
    labels=('10','11','00') if code=='paired' else (None,'1','0')
    while todo:
        q,w=todo.popleft()
        if q in J.final:return w
        for a,t in enumerate(macro[q]):
            if t>=0 and t not in seen:
                seen.add(t);todo.append((t,w+labels[a]))
    return None


def target_tail_decision(I,max_prefixes=5000,max_states=200000,max_transitions=2000000):
    """Exact on certified target-local marker inputs, UNKNOWN outside/capped."""
    validate(I)
    if any(any(q>=0 for q in I.delta[f]) for f in I.final):
        return dict(status='UNKNOWN',reason='Terminal accepting states required')
    if max_prefixes is not None and (type(max_prefixes) is not int or max_prefixes<1):
        raise ValueError('Schema-prefix cap must be positive or None')
    diagnostics=[];unresolved=False;prefixes=0;schemas=0
    for f in sorted(I.final):
        cert,J,macro=target_tail_certificate(I,f)
        if cert['status']=='NOT_APPLICABLE':
            old=cert['reason'];cert,J,macro=target_tail_certificate(I,f,'unary');cert['paired_failure']=old
        row=dict(certificate=cert,schemas=0);diagnostics.append(row)
        status=cert['status']
        if status=='EMPTY_SLICE':continue
        if status in ('EMPTY_WORD','NO_EFFECTIVE_FLAGS'):
            w='' if status=='EMPTY_WORD' else _plain_path(J,macro,cert['code'])
            if w is not None:
                assert witness(I,w) and border_witness(I,w)
                return dict(status='YES',word=w,slices=diagnostics,schemas=schemas)
            continue
        if status!='CERTIFIED':unresolved=True;continue
        B=cert['marker_bound'];k=len(I.delta)
        data={p:[q for q in row[:2] if q>=0] for p,row in macro.items()}
        data_reach={p:reach([p],data) for p in macro}
        table=tuple(macro[p][:2] if p in macro else (-1,-1) for p in range(k))
        todo=deque([(J.start,())]);prefixes+=1
        while todo:
            begin,seq=todo.popleft()
            if len(seq)==B:continue
            for end in sorted(data_reach[begin]):
                target=macro[end][2]
                if target<0:continue
                new=seq+((begin,end,target),)
                if max_prefixes is not None and prefixes>=max_prefixes:
                    return dict(status='UNKNOWN',reason='Complete-cover prefix cap',prefixes=prefixes,schemas=schemas,slices=diagnostics)
                prefixes+=1
                if target!=f:
                    todo.append((target,new));continue
                ms=tuple(BinaryDFA(table,frozenset({q}),p) for p,q,_ in new)
                r=len(ms)
                flags=frozenset(((i,p),(j,q)) for i in range(r) for j in range(r)
                                for p,q in J.flags if p in macro and q in macro)
                ans=solve_blocks(BlockSystem(ms,flags),max_states,max_transitions)
                row['schemas']+=1;schemas+=1
                if ans['status']=='YES':
                    w=ans['word'] if cert['code']=='paired' else ''.join(u+'0' for u in ans['blocks'])
                    assert witness(I,w) and border_witness(I,w)
                    return dict(status='YES',word=w,blocks=ans['blocks'],slices=diagnostics,
                                schemas=schemas,prefixes=prefixes,convolution=ans)
                if ans['status']!='NO':unresolved=True
    return dict(status='UNKNOWN' if unresolved else 'NO',slices=diagnostics,
                schemas=schemas,prefixes=prefixes,
                reason='Uncertified/capped slice' if unresolved else 'All complete target-local covers are empty')


def pump_witness(I,w,h,code='paired'):
    """Erase repeated finite prefix-monitor states of ONE known witness.

    All flag targets visited before the final h blocks must be absent. The
    algorithm checks this supplied-word hypothesis and both word predicates.
    It preserves witnesshood, not necessarily the full agreement profile.
    """
    if type(h) is not int or h<1 or code not in ('paired','unary'):
        raise ValueError('Positive tail height and known code required')
    validate(I)
    if not witness(I,w) or not border_witness(I,w):raise ValueError('Supply a witness')
    if any(q>=0 for q in I.delta[I.run(w)[-1]]):
        raise ValueError('A terminal accepted witness is required')
    if not w:return dict(word=w,original_blocks=0,retained_blocks=0,deleted_blocks=0)
    if code=='paired':
        blocks=decode_blocks(w);unit=2
    else:
        blocks=tuple(w.split('0')[:-1]) if w.endswith('0') else None;unit=1
    if blocks is None:raise ValueError('Word does not parse in marker format')
    c=I.run(w)
    if code=='paired':
        odd={c[t] for t in range(1,len(w),2)}
        visited=set(c)
        if any(p in visited and q in visited and p!=c[-1] and (p in odd or q in odd)
               for p,q in I.flags):
            raise ValueError('Relevant flags must be at aligned token boundaries')
    if len(blocks)<=h:return dict(word=w,original_blocks=len(blocks),retained_blocks=len(blocks),deleted_blocks=0)
    starts=[];pos=0
    for b in blocks:starts.append(pos);pos+=unit*(len(b)+1)
    assert pos==len(w)
    tail_start=len(blocks)-h;refs=blocks[tail_start:]
    targets={q for p,q in I.flags if p in c and q!=c[-1]}
    for i in range(tail_start):
        if any(c[starts[i]+unit*t] in targets for t in range(len(blocks[i])+1)):
            raise ValueError('Some flag target is outside the protected tail')
    def signature(i):
        x=blocks[i];eq=hits=0
        for j,y in enumerate(refs):
            if x==y:eq|=1<<j
            for t in range(min(len(x),len(y))+1):
                if x[len(x)-t:]==y[len(y)-t:] and (c[starts[i]+unit*(len(x)-t)],
                     c[starts[tail_start+j]+unit*(len(y)-t)]) in I.flags:
                    hits|=1<<j;break
        return eq,hits
    def transition(pending,eq,hits=0):
        nxt=0
        for l in range(1,h):
            if pending>>(l-1)&1 and eq>>l&1:
                if l==h-1:raise AssertionError('A forbidden context completed')
                nxt|=1<<l
        if hits>>(h-1)&1:raise AssertionError('A final-block violation was observed')
        for j in range(h-1):
            if hits>>j&1:nxt|=1<<j
        return nxt
    retained=[];states=[(I.start,0)];positions={states[0]:0};pending=0
    for i in range(tail_start):
        eq,hits=signature(i);pending=transition(pending,eq,hits)
        q=c[starts[i]+unit*(len(blocks[i])+1)];state=(q,pending)
        if state in positions:
            at=positions[state]
            for old in states[at+1:]:del positions[old]
            retained=retained[:at];states=states[:at+1]
        else:
            retained.append(i);positions[state]=len(states);states.append(state)
    for i in range(tail_start,len(blocks)):
        eq=sum((1<<j) for j,b in enumerate(refs) if blocks[i]==b)
        pending=transition(pending,eq)
    assert pending==0
    kept=tuple(blocks[i] for i in retained)+refs
    out=encode_blocks(kept) if code=='paired' else ''.join(u+'0' for u in kept)
    assert witness(I,out) and border_witness(I,out)
    assert len(kept)<=h+len(I.delta)*(1<<(h-1))
    return dict(word=out,original_blocks=len(blocks),retained_blocks=len(kept),
                deleted_blocks=len(blocks)-len(kept),retained_prefix_indices=retained,
                monitor_states=len(states))
