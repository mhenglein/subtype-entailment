"""Finite symbolic promotion-preimage compiler; see the accompanying proof.

The COMPLETE finite enumerator and compiler have no concrete graph/word
argument. Default resource limits return UNKNOWN. Research status: proposed
unrestricted proof, not independently reviewed or Lean-verified.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from rank_preimage_core import (
    LABELS, Atom, Budget, Colour, Exhausted, FALSE, Graph, Map, Model,
    Observer, Query, TRUE, Test, conj, core_observer, fld, fresh,
    interval_observer, model, one_edge, path, radix_decode, radix_encode,
    slice_observer, table,
)


@dataclass(frozen=True)
class Piece:
    kind: str
    source: str
    target: str
    left_control: int
    right_control: int
    label: str = ''


@dataclass(frozen=True)
class Diagram:
    locations: tuple[tuple[str,str,str],...]  # query variable, core/fresh, name
    groups: tuple[tuple[str,...],...]         # ordered, coincident fresh marks
    states: tuple[int,...]                   # actual reverse state at each mark
    next_bits: tuple[str,...]
    first_bit: str
    old_end_colour: Colour
    pieces: tuple[tuple[Piece,...],...]
    intermediate_controls: tuple[tuple[int,int,int,int],...] = ()
    # atom index, piece index, internal group index, observer control


class InvalidDiagram(ValueError):
    pass


END='@end'
INITIAL='@failure'
FIRST='@first'
LAST='@last'


def compile_diagram(I, query: Query, D: Diagram) -> Query:
    """Syntactic compilation. NO graph/reference-word parameter is used.

    Any well-formed diagram is sound. The full finite enumerator below supplies
    the completeness bound; this function also supports replayed certificates.
    """
    if not D.groups or len(D.groups)!=len(D.states) or len(D.states)!=len(D.next_bits):
        raise InvalidDiagram('Malformed fresh marks')
    group={}
    for i,names in enumerate(D.groups):
        if not names: raise InvalidDiagram('Empty mark class')
        for name in names:
            if name in group: raise InvalidDiagram('Repeated mark')
            group[name]=i
    if group.get(FIRST)!=0 or group.get(LAST)!=len(D.groups)-1:
        raise InvalidDiagram('Missing endpoint marks')
    if D.first_bit not in '01' or len(D.first_bit)!=1:
        raise InvalidDiagram('Bad first bit')
    if D.next_bits[-1]!='' or any(b not in ('0','1') for b in D.next_bits[:-1]):
        raise InvalidDiagram('Only the last mark may be final')
    if not D.old_end_colour.end or D.old_end_colour.root or D.old_end_colour.next_bit!='':
        raise InvalidDiagram('Base endpoint colour')
    k=len(I.delta)
    if any(q<0 or q>=k for q in D.states): raise InvalidDiagram('Invalid original state')
    loc={v:(kind,name) for v,kind,name in D.locations}
    if set(loc)!=set(query.variables): raise InvalidDiagram('Missing variable location')
    if any(kind not in ('core','fresh') or (kind=='fresh' and name not in group)
           for kind,name in loc.values()): raise InvalidDiagram('Bad variable location')
    if len(D.pieces)!=len(query.atoms): raise InvalidDiagram('Missing path diagram')
    z=tuple('@origin:'+str(i) for i in range(len(D.groups)))
    variables={END,INITIAL,*z}|{name for kind,name in loc.values() if kind=='core'}
    tests=[(END,Test('colour',(D.old_end_colour,)))]
    equal=[(z[-1],END)]; unequal=[];atoms=[]
    coremap=Map('core',(D.first_bit,))
    control={(a,b,c):d for a,b,c,d in D.intermediate_controls}
    for j in range(len(z)-1):tests.append((z[j],fld('end',False)))
    def fm(g): return fresh(I,D.states[g],D.next_bits[g])
    def ftest(g,t): tests.append((z[g],Test('mapped',(fm(g),t))))
    def canonical(kind,name): return (kind,group[name] if kind=='fresh' else name)
    def endpoint(piece,side):
        kind=('core' if piece.kind=='core' else 'fresh' if piece.kind=='forward' else
              'core' if piece.kind=='enter' and side=='source' else
              'core' if piece.kind=='exit' and side=='target' else 'fresh')
        name=getattr(piece,side)
        if kind=='fresh' and name not in group: raise InvalidDiagram('Unmarked path endpoint')
        if kind=='core':variables.add(name)
        return canonical(kind,name)
    for v,t in query.tests:
        kind,name=loc[v]
        if kind=='core':tests.append((name,Test('mapped',(coremap,t))))
        else:ftest(group[name],t)
    for pairs,neg in ((query.equal,False),(query.unequal,True)):
        for v,w in pairs:
            a,b=loc[v],loc[w]
            if a[0]!=b[0]:
                if not neg:raise InvalidDiagram('Old/fresh equality')
            elif a[0]=='fresh':
                same=group[a[1]]==group[b[1]]
                if same==neg:raise InvalidDiagram('Fresh equality/disequality')
            else:(unequal if neg else equal).append((a[1],b[1]))
    # All source labels and the same first emission are fixed for every atom.
    p=D.states[0];q=D.old_end_colour.state;a=D.first_bit
    if I.delta[p][int(a)]!=q or p in I.bad or (p,p) in I.flags:
        raise InvalidDiagram('No safe first emission')
    atoms.append(Atom(one_edge('F'),END,INITIAL))
    atoms.append(Atom(one_edge('K'+a,right=conj(Test('clear',('forbidden',p)),
                 fld('end',len(z)==1))),INITIAL,z[0]))
    active=[[] for _ in range(max(0,len(z)-1))]
    for ai,(atom,pieces) in enumerate(zip(query.atoms,D.pieces)):
        o=atom.observer
        if not pieces:raise InvalidDiagram('Use an explicit empty core/forward piece')
        if endpoint(pieces[0],'source')!=canonical(*loc[atom.source]):
            raise InvalidDiagram('Path starts at wrong query variable')
        if endpoint(pieces[-1],'target')!=canonical(*loc[atom.target]):
            raise InvalidDiagram('Path ends at wrong query variable')
        if pieces[0].left_control not in o.initial or pieces[-1].right_control not in o.final:
            raise InvalidDiagram('Path does not accept')
        for left,right in zip(pieces,pieces[1:]):
            if endpoint(left,'target')!=endpoint(right,'source') or left.right_control!=right.left_control:
                raise InvalidDiagram('Path seams disagree')
        for pi,P in enumerate(pieces):
            u,v,lc,rc=P.source,P.target,P.left_control,P.right_control
            if not 0<=lc<o.size or not 0<=rc<o.size:raise InvalidDiagram('Observer control range')
            if P.kind=='core':
                atoms.append(Atom(core_observer(slice_observer(o,lc,rc),a),u,v))
            elif P.kind=='forward':
                i,j=group[u],group[v]
                if i>j:raise InvalidDiagram('Backward fresh interval')
                if i==j:
                    if lc!=rc:raise InvalidDiagram('Empty interval changes NFA control')
                    tests.append((z[i],Test('allows',(o,lc,fm(i)))))
                else:
                    cs=[lc]+[control[ai,pi,g] for g in range(i+1,j)]+[rc]
                    if any(x<0 or x>=o.size for x in cs):raise InvalidDiagram('Bad seam control')
                    for g in range(i,j):active[g].append((o,cs[g-i],cs[g-i+1]))
            elif P.kind in ('enter','wrap'):
                dest=group[v]
                if dest!=0:raise InvalidDiagram('All entries use first mark')
                if P.kind=='enter':
                    if P.label not in ('S','K'+a):raise InvalidDiagram('Incorrect entrance')
                    equal.append((u,END));left=Map('constant',(coremap.apply(D.old_end_colour),))
                else:
                    if group[u]!=len(z)-1 or P.label!='K'+a:raise InvalidDiagram('Incorrect wrap')
                    left=Map('constant',(fm(len(z)-1).apply(D.old_end_colour),))
                tests.append((z[0],Test('portal',(o,lc,rc,P.label,left,fm(0)))))
            elif P.kind=='exit':
                i=group[u]
                if P.label=='F':
                    equal.append((v,z[i]))
                    tests.append((z[i],Test('portal',(o,lc,rc,'F',fm(i),coremap))))
                elif P.label in ('K0','K1'):
                    avoid=a if i==len(z)-1 else D.next_bits[i]
                    if P.label=='K'+avoid:raise InvalidDiagram('A matching step is not a core exit')
                    lt=Test('allows',(o,lc,fm(i)));rt=Test('allows',(o,rc,coremap))
                    sem=(o,lc,rc,P.label,fm(i),coremap)
                    atoms.append(Atom(one_edge(P.label,lt,rt,sem),z[i],v))
                else:raise InvalidDiagram('Unknown exit edge')
            else:raise InvalidDiagram('Unknown path piece')
    for g,items in enumerate(active):
        obs=tuple(o for o,_,_ in items)
        left=(D.states[g],D.next_bits[g],tuple(c for _,c,_ in items))
        right=(D.states[g+1],D.next_bits[g+1],tuple(c for _,_,c in items))
        atoms.append(Atom(interval_observer(I,obs,left,right),z[g],z[g+1]))
    return Query(tuple(sorted(variables)),tuple(tests),tuple(equal),tuple(unequal),tuple(atoms))


def extract_diagram(I,B,C,query,solution):
    """Obtain a finite diagram certificate from literal successful paths.

    This extraction is ONLY a test/replay convenience. The generic syntactic
    enumerator does not know either B or C and is implemented separately below.
    """
    from rank_query_graphs import graph_from_reference, classify_edge
    base=graph_from_reference(I,B);m=len(B.word);n=len(C.word)
    def cname(x):return END if x==m else 'c:'+str(x)
    def fname(x):return 'f:'+str(x)
    def name(x):return cname(x) if x<=m else fname(x)
    loc=tuple((v,'core' if pos<=m else 'fresh',name(pos)) for v,pos in solution.assignment.items())
    marks={m+1,n}|{x for x in solution.assignment.values() if x>m}
    paths=[];literalpieces=[]
    for atom,(start_control,steps) in zip(query.atoms,solution.paths):
        groups=[]
        for edge in steps:
            u,q,e,v,p=edge;kind=classify_edge(m,n,(u,e,v))
            if groups and kind in ('core','forward') and groups[-1][0]==kind:
                groups[-1][1].append(edge)
            else:groups.append((kind,[edge]))
        if not groups:
            x=solution.assignment[atom.source]
            kind='core' if x<=m else 'forward'
            groups=[(kind,[])]
        out=[]
        for kind,es in groups:
            if es:u,q=es[0][:2];v,p=es[-1][3:]
            else:u=v=solution.assignment[atom.source];q=p=start_control
            if u>m:marks.add(u)
            if v>m:marks.add(v)
            out.append(Piece(kind,name(u),name(v),q,p,es[0][2] if kind not in ('core','forward') else ''))
        paths.append(tuple(out));literalpieces.append(groups)
    order=sorted(marks);index={x:i for i,x in enumerate(order)}
    classes=[]
    for x in order:
        ns=[fname(x)]
        if x==m+1:ns.append(FIRST)
        if x==n:ns.append(LAST)
        classes.append(tuple(ns))
    controls=[]
    for ai,groups in enumerate(literalpieces):
        for pi,(kind,es) in enumerate(groups):
            if kind!='forward' or not es:continue
            start,end=es[0][0],es[-1][3]
            stateat={es[0][0]:es[0][1]};stateat.update((e[3],e[4]) for e in es)
            for x in order:
                if start<x<end:controls.append((ai,pi,index[x],stateat[x]))
    return Diagram(loc,tuple(classes),tuple(C.labels[x] for x in order),
                   tuple(C.word[x] if x<n else '' for x in order),C.word[m],base.colours[m],
                   tuple(paths),tuple(controls))


@dataclass(frozen=True)
class Shape:
    kind: str
    source: str
    target: str
    label: str = ''


def ordered_partitions(items):
    """All weak linear orders of a finite set, with no concrete positions."""
    if not items:
        yield ();return
    x,*rest=items
    for groups in ordered_partitions(tuple(rest)):
        for j in range(len(groups)):
            yield groups[:j]+((x,*groups[j]),)+groups[j+1:]
        for j in range(len(groups)+1):
            yield groups[:j]+((x,),)+groups[j:]


def cartesian_ranges(sizes):
    """Unlike itertools.product(range(huge), ...), do not cache huge pools."""
    def rec(i,values):
        if i==len(sizes):
            yield values;return
        for q in range(sizes[i]):yield from rec(i+1,values+(q,))
    yield from rec(0,())


def path_shapes(atom_index,size,start,stop,first,budget):
    """All bounded portal shapes, without observer states or a base graph."""
    sk,s=start;tk,t=stop
    def excursions(begin,number):
        budget.tick()
        if tk=='fresh':yield (Shape('forward',begin,t),)
        x='@exitmark:%d:%d'%(atom_index,number)
        y='@exitcore:%d:%d'%(atom_index,number)
        for label in ('F','K0','K1'):
            pre=(Shape('forward',begin,x),Shape('exit',x,y,label))
            if tk=='core':yield pre+(Shape('core',y,t),)
            if number<size+1:
                for enter in ('S','K'+first):
                    mid=(Shape('core',y,END),Shape('enter',END,FIRST,enter))
                    for tail in excursions(FIRST,number+1):yield pre+mid+tail
        if number<size+1:
            pre=(Shape('forward',begin,LAST),Shape('wrap',LAST,FIRST,'K'+first))
            for tail in excursions(FIRST,number+1):yield pre+tail
    if sk=='core':
        if tk=='core':yield (Shape('core',s,t),)
        for enter in ('S','K'+first):
            pre=(Shape('core',s,END),Shape('enter',END,FIRST,enter))
            for tail in excursions(FIRST,1):yield pre+tail
    else:yield from excursions(s,1)


def _all_colours(k):
    for q in range(k):
        for mask in range(1<<k):
            for nxt in ('0','1',''):
                for root in (False,True):
                    for end in (False,True):yield Colour(q,mask,nxt,root,end)


def iter_diagrams(I,query,budget=None):
    """The COMPLETE finite syntactic enumerator promised by Lemma 4.

    It never inspects a graph, a word, its length, a search-depth cutoff or an
    independently selected reference. Branching is intentionally very large.
    """
    budget=budget or Budget();k=len(I.delta)
    qtests={v:conj(*(t for w,t in query.tests if w==v)) for v in query.variables}
    for first in '01':
        # Prune only role choices ruled out by the finite colour alphabet.
        possibilities={}
        for v in query.variables:
            options=[]
            for kind in ('core','fresh'):
                possible=False
                for c in _all_colours(k):
                    budget.tick()
                    d=Map('core',(first,)).apply(c) if kind=='core' else Colour(c.state,c.forbidden,c.next_bit,False,c.end)
                    if qtests[v].holds(d):possible=True;break
                if possible:options.append(kind)
            possibilities[v]=options
        for roles in product(*(possibilities[v] for v in query.variables)):
            budget.tick()
            loc={v:(kind,('o:' if kind=='core' else 'n:')+v) for v,kind in zip(query.variables,roles)}
            if any(loc[x][0]!=loc[y][0] for x,y in query.equal):continue
            def choose_shapes(i,selected):
                if i==len(query.atoms):yield selected;return
                a=query.atoms[i]
                for sh in path_shapes(i,a.observer.size,loc[a.source],loc[a.target],first,budget):
                    yield from choose_shapes(i+1,selected+(sh,))
            for shapes in choose_shapes(0,()):
                marks={FIRST,LAST}|{name for kind,name in loc.values() if kind=='fresh'}
                forwards=[]
                for sh in shapes:
                    for p in sh:
                        if p.kind=='forward':marks|={p.source,p.target};forwards.append((p.source,p.target))
                        elif p.kind=='enter':marks.add(p.target)
                        elif p.kind=='exit':marks.add(p.source)
                        elif p.kind=='wrap':marks|={p.source,p.target}
                bound=len(query.variables)+2+2*sum(a.observer.size+1 for a in query.atoms)
                if len(marks)>bound:raise AssertionError('Mark bound exceeded')
                for groups in ordered_partitions(tuple(sorted(marks))):
                    budget.tick();where={v:i for i,g in enumerate(groups) for v in g};n=len(groups)
                    if where[FIRST]!=0 or where[LAST]!=n-1:continue
                    if any(where[x]>where[y] for x,y in forwards):continue
                    if any(loc[x][0]=='fresh' and where[loc[x][1]]!=where[loc[y][1]] for x,y in query.equal):continue
                    if any(loc[x][0]=='fresh' and loc[y][0]=='fresh' and where[loc[x][1]]==where[loc[y][1]] for x,y in query.unequal):continue
                    # Piece-seam and internal-mark controls are all finite guesses.
                    control_slots=[]
                    for ai,(atom,sh) in enumerate(zip(query.atoms,shapes)):
                        for j in range(len(sh)+1):control_slots.append((ai,'seam',j,atom.observer.size))
                        for pi,P in enumerate(sh):
                            if P.kind=='forward':
                                for g in range(where[P.source]+1,where[P.target]):
                                    control_slots.append((ai,pi,g,atom.observer.size))
                    for values in cartesian_ranges(tuple(s[3] for s in control_slots)):
                        budget.tick();cs={s[:3]:v for s,v in zip(control_slots,values)}
                        if any(cs[ai,'seam',0] not in a.observer.initial or
                               cs[ai,'seam',len(shapes[ai])] not in a.observer.final
                               for ai,a in enumerate(query.atoms)):continue
                        ps=tuple(tuple(Piece(P.kind,P.source,P.target,cs[ai,'seam',j],
                                             cs[ai,'seam',j+1],P.label) for j,P in enumerate(sh))
                                 for ai,sh in enumerate(shapes))
                        extra=tuple((ai,pi,g,v) for (ai,pi,g),v in cs.items() if pi!='seam')
                        for states in cartesian_ranges((k,)*n):
                            budget.tick();p=states[0];q=I.delta[p][int(first)]
                            if q<0 or p in I.bad or q in I.bad or (p,p) in I.flags:continue
                            for bits in product(('0','1'),repeat=n-1):
                                nxt=bits+('',)
                                for mask in range(1<<k):
                                    budget.tick()
                                    if mask>>q&1:continue # safe B at its own last cut
                                    end=Colour(q,mask,'',False,True)
                                    yield Diagram(tuple((v,*loc[v]) for v in query.variables),groups,
                                                  states,nxt,first,end,ps,extra)


def preimages(I,query,budget=None):
    budget=budget or Budget()
    for D in iter_diagrams(I,query,budget):
        budget.tick()
        try:yield compile_diagram(I,query,D)
        except (InvalidDiagram,KeyError):continue


def finish_queries(I):
    k=len(I.delta)
    for q in range(k):
        o=Observer('finish',k,(q,),frozenset({I.start}),(I,))
        yield Query(('e','f','x'),(('e',conj(fld('end',True),fld('state',q))),),
                    atoms=(Atom(one_edge('F'),'e','f'),Atom(o,'f','x')))


def iter_rank_queries(I,promotions,budget):
    """A finite lazy union, independent of the queried initial graphs."""
    if promotions<0:raise ValueError('Nonnegative rank parameter required')
    yield from finish_queries(I)
    if promotions:
        for q in iter_rank_queries(I,promotions-1,budget):
            yield from preimages(I,q,budget)


def decide(I,max_work=100000,reconstruct_limit=100000):
    """Candidate unrestricted algorithm, conditional on the reviewed lemma.

    Explicit resource/host failures are UNKNOWN. The default cap is deliberately
    finite. With limits removed, the mathematical finite construction is used;
    no claim of practical performance or independent theorem verification.
    """
    from border_lab import witness,border_witness,words
    from rank_query_prefix import Reference,valid_reverse_prefix
    from rank_query_graphs import graph_from_reference
    k=len(I.delta);budget=Budget(max_work)
    if (not k or type(I.start) is not int or not 0<=I.start<k
        or any(len(row)!=2 or any(type(q) is not int or q < -1 or q>=k for q in row) for row in I.delta)
        or any(type(q) is not int or not 0<=q<k for q in I.final|I.bad)
        or any(len(pair)!=2 or any(type(q) is not int or not 0<=q<k for q in pair) for pair in I.flags)):
        raise ValueError('Malformed binary instance')
    if I.alphabet!='01' or any(t>=0 for f in I.final for t in I.delta[f]):
        raise ValueError('A nonempty binary terminal automaton is required')
    if witness(I,''):return dict(status='YES',word='',work=0)
    bases=[]
    for f in sorted(I.final):
        for p,row in enumerate(I.delta):
            for a,t in enumerate(row):
                if t!=f:continue
                B=Reference(str(a),(f,p))
                if valid_reverse_prefix(I,B.word,B.labels):bases.append(graph_from_reference(I,B))
    if not bases:return dict(status='NO',work=0,reason='No safe nonempty initial reference')
    try:
        for query in iter_rank_queries(I,max(0,k-2),budget):
            budget.tick()
            for G in bases:
                if model(G,query,budget) is not None:
                    # The existence decision is independent of reconstruction.
                    # Enumeration is justified ONLY after a positive formula.
                    seen=0;n=0
                    while True:
                        for bits in product('01',repeat=n):
                            seen+=1
                            if reconstruct_limit is not None and seen>reconstruct_limit:
                                return dict(status='UNKNOWN',word=None,work=budget.used,
                                            query_positive=True,reason='Explicit reconstruction cap')
                            w=''.join(bits)
                            if witness(I,w):
                                assert border_witness(I,w)
                                return dict(status='YES',word=w,work=budget.used)
                        n+=1
        return dict(status='NO',work=budget.used,reason='Entire finite query union exhausted')
    except (Exhausted,MemoryError,RecursionError,OverflowError) as e:
        return dict(status='UNKNOWN',work=budget.used,reason=type(e).__name__)


def reconstruct_reference(I,B,D,compiled,solution):
    """Replay a positive compiled branch into ONE actual shared reference."""
    from rank_query_prefix import Reference,valid_reverse_prefix
    from rank_query_graphs import first_return,graph_from_reference
    ext=[D.first_bit];states=[D.states[0]];positions=[len(B.word)+1]
    for atom,(initial,steps) in zip(compiled.atoms,solution.paths):
        if atom.observer.kind!='interval':continue
        sizes=atom.observer.data[2]
        for _,_,edge,_,p in steps:
            if edge not in ('K0','K1'):raise AssertionError('Generator edge')
            ext.append(edge[-1]);states.append(radix_decode(p,sizes)[0])
        positions.append(len(B.word)+len(ext))
    C=Reference(B.word+''.join(ext),B.labels+tuple(states))
    if not first_return(B.word,C.word) or not valid_reverse_prefix(I,C.word,C.labels):
        # Pure graph tests may omit a terminal r_0. Check the local generator
        # invariant separately there; terminal theorem callers require validity.
        from rank_query_graphs import local_extension
        local_extension(I,B,C,require_safe=False)
        for i,bit in enumerate(C.word):
            p,q=C.labels[i+1],C.labels[i]
            if I.delta[p][int(bit)]!=q:raise AssertionError('Broken reverse run')
        G=graph_from_reference(I,C)
        for i,c in enumerate(G.colours):
            if c.state in I.bad or c.forbidden>>c.state&1:raise AssertionError('Unsafe reference')
    groups={name:i for i,g in enumerate(D.groups) for name in g}
    assign={v:solution.assignment[name] if kind=='core' else positions[groups[name]]
            for v,kind,name in D.locations}
    return C,assign


def verify_assignment(G,Q,assignment,budget=None):
    budget=budget or Budget()
    if any(not t.holds(G.colours[assignment[v]]) for v,t in Q.tests):return False
    if any(assignment[x]!=assignment[y] for x,y in Q.equal):return False
    if any(assignment[x]==assignment[y] for x,y in Q.unequal):return False
    return all(path(G,a.observer,assignment[a.source],assignment[a.target],budget) is not None for a in Q.atoms)
