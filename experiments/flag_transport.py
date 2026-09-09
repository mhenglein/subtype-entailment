"""Proof-carrying relocation of flags and exact synchronized separator encoding.

Flags are moved only across a uniquely reversible common letter. The relation
of possible placements is finite, but it is NOT a complete witness solver.
See notes/2026-09-08-flag-transport-and-separator-obstruction.md.
Standard library; existing border predicates are unchanged.
"""
from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import Optional

from border_lab import Instance, witness, border_witness


def validate(I):
    k = len(I.delta)
    if k < 1 or I.alphabet != '01' or type(I.start) is not int or not 0 <= I.start < k:
        raise ValueError('A nonempty binary automaton with a valid start is required')
    if any(len(row) != 2 or any(type(q) is not int or not -1 <= q < k for q in row)
           for row in I.delta):
        raise ValueError('Invalid partial transition table')
    if any(type(q) is not int or not 0 <= q < k for q in I.final | I.bad):
        raise ValueError('Invalid final/Bad annotation')
    if any(len(g) != 2 or any(type(q) is not int or not 0 <= q < k for q in g)
           for g in I.flags):
        raise ValueError('Invalid flag')
    if any(any(q >= 0 for q in I.delta[f]) for f in I.final):
        raise ValueError('Accepting states must be terminal')


def _incoming(I):
    inc = [set() for _ in I.delta]
    for p,row in enumerate(I.delta):
        for a,q in enumerate(row):
            if q >= 0:
                inc[q].add((p,a))
    return inc


def transport_edges(I):
    """All independently checkable one-letter equivalences of proper flags.

    A returned edge (old,new,a) means a violation of old is equivalent to a
    violation of new, with both cuts advanced by one in the forward direction.
    Boundary cases into final are included on the new side. Diagonal flags
    are never relocated. No assumption that the start is visited only once.
    """
    validate(I)
    inc = _incoming(I)
    edges = []
    k = len(I.delta)
    for p in range(k):
        for q in range(k):
            if p == q or p in I.final or q in I.final:
                continue
            common = [a for a in range(2) if min(I.delta[p][a],I.delta[q][a]) >= 0]
            if len(common) != 1:
                continue
            a = common[0]
            r,s = I.delta[p][a],I.delta[q][a]
            if r == s or r == I.start or s == I.start:
                continue
            if inc[r] == {(p,a)} and inc[s] == {(q,a)}:
                edges.append(((p,q),(r,s),str(a)))
    return edges


def verify_transport(I, old, new, letter):
    """Check a local proof object from the table, not by testing sample words."""
    return (tuple(old),tuple(new),letter) in transport_edges(I)


def relocate(I, old, new):
    """One checked forward OR backward edge; unaffected flags are retained."""
    old,new = tuple(old),tuple(new)
    if old not in I.flags:
        raise ValueError('The source flag is absent')
    edges = transport_edges(I)
    if not any((a,b)==(old,new) or (b,a)==(old,new) for a,b,_ in edges):
        raise ValueError('No uniquely reversible common-letter transport')
    return Instance(I.delta,I.final,(I.flags-{old})|{new},I.bad,I.start,I.alphabet)


def relocation_orbits(I):
    """All equivalent pair placements, with a path of checked local rewrites."""
    edges = transport_edges(I)
    graph = {}
    for a,b,letter in edges:
        graph.setdefault(a,[]).append((b,letter,True))
        graph.setdefault(b,[]).append((a,letter,False))
    result = []
    for root in sorted(I.flags):
        paths = {root: []}
        todo = deque([root])
        while todo:
            at = todo.popleft()
            for nxt,letter,forward in graph.get(at,()):
                if nxt not in paths:
                    paths[nxt] = paths[at]+[dict(old=at,new=nxt,letter=letter,forward=forward)]
                    todo.append(nxt)
        result.append((root,paths))
    return result


def synchronous_colouring(I):
    """The existing minimal flag-synchronous colouring, independently implemented.

    Every transition into any final is marked. Equality is propagated along
    the full synchronized graph rooted at flags; this is a sufficient condition
    for exact encoding, not a claim that every pair path is realizable.
    """
    validate(I)
    edges = [(p,a) for p,row in enumerate(I.delta) for a,q in enumerate(row) if q >= 0]
    parent = {edge:edge for edge in edges}
    def find(e):
        root=e
        while parent[root] != root:
            root=parent[root]
        while parent[e] != e:
            nxt=parent[e];parent[e]=root;e=nxt
        return root
    def union(e,f):
        x,y=find(e),find(f)
        if x != y:parent[max(x,y)]=min(x,y)
    seen=set(I.flags); todo=deque(sorted(seen))
    while todo:
        p,q=todo.popleft()
        for a in range(2):
            r,s=I.delta[p][a],I.delta[q][a]
            if min(r,s)<0:continue
            union((p,a),(q,a))
            if (r,s) not in seen:
                seen.add((r,s));todo.append((r,s))
    forced={find((p,a)) for p,a in edges if I.delta[p][a] in I.final}
    marked=frozenset(edge for edge in edges if find(edge) in forced)
    return marked


def verify_colouring(I, marked):
    """Independent local synchrony and final-marker certificate check."""
    validate(I)
    marked=frozenset(tuple(e) for e in marked)
    valid={(p,a) for p,row in enumerate(I.delta) for a,q in enumerate(row) if q>=0}
    if not marked <= valid:return False
    if any((p,a) not in marked for p,a in valid if I.delta[p][a] in I.final):return False
    todo=deque(I.flags);seen=set(I.flags)
    while todo:
        p,q=todo.popleft()
        for a in range(2):
            r,s=I.delta[p][a],I.delta[q][a]
            if min(r,s)<0:continue
            if ((p,a) in marked) != ((q,a) in marked):return False
            if (r,s) not in seen:seen.add((r,s));todo.append((r,s))
    return True


def compile_logical(I, marked):
    """Logical form of the exact binary 1a[00] compiler.

    Alphabet 01# is an INTERNAL representation, not an added subtype
    constructor. Re-encode logical 0,1,# as 10,11,00 to obtain that binary
    compiler exactly. Flags remain on original states; helpers are unannotated.
    """
    if not verify_colouring(I,marked):
        raise ValueError('Invalid synchronous separator certificate')
    table=[[-1,-1,-1] for _ in I.delta]
    for p,row in enumerate(I.delta):
        for a,q in enumerate(row):
            if q<0:continue
            if (p,a) in marked:
                h=len(table);table.append([-1,-1,q]);table[p][a]=h
            else:table[p][a]=q
    return Instance(tuple(map(tuple,table)),I.final,I.flags,I.bad,I.start,'01#')


def encode_logical(I, word, marked):
    trace=I.run(word)
    if trace is None:raise ValueError('A defined original word is required')
    return ''.join(a+('#' if (trace[i],int(a)) in marked else '') for i,a in enumerate(word))


def decode_logical(I, logical, marked):
    word=logical.replace('#','')
    if encode_logical(I,word,marked)!=logical:
        raise ValueError('Invalid encoded run')
    return word


def _cycle_edges(I):
    reach=[]
    for p in range(len(I.delta)):
        seen={p};todo=[p]
        for q in todo:
            for r in I.delta[q]:
                if r>=0 and r not in seen:seen.add(r);todo.append(r)
        reach.append(seen)
    return {(p,a) for p,row in enumerate(I.delta) for a,q in enumerate(row)
            if q>=0 and p in reach[q]}


def best_relocation(I, max_variants=100000):
    """Finite annotation search, scored by cyclic marked edges; not a decider.

    All variants are witness-language equivalent. A cap reports UNKNOWN for
    optimality while retaining the valid best-so-far candidate. None removes
    the cap. No existence/completeness conclusion is inferred from this score.
    """
    if max_variants is not None and (type(max_variants) is not int or max_variants<1):
        raise ValueError('max_variants must be positive or None')
    orbits=relocation_orbits(I)
    cycles=_cycle_edges(I)
    best=None;count=0;seen=set();capped=False
    for choices in product(*(sorted(paths) for _,paths in orbits)):
        flags=frozenset(choices)
        if flags in seen:continue
        if max_variants is not None and count>=max_variants:
            capped=True;break
        seen.add(flags);count+=1
        J=Instance(I.delta,I.final,flags,I.bad,I.start,I.alphabet)
        marked=synchronous_colouring(J)
        score=(len(marked & cycles),len(marked),tuple(sorted(flags)))
        if best is None or score<best[0]:
            proofs=[dict(source=root,target=choice,steps=paths[choice])
                    for (root,paths),choice in zip(orbits,choices)]
            best=(score,J,marked,proofs)
    assert best is not None
    return dict(status='UNKNOWN' if capped else 'OPTIMAL_IN_TRANSPORT_ORBIT',
                variants=count,score=best[0],flags=sorted(best[1].flags),
                marked=sorted(best[2]),proofs=best[3]),best[1]


def nine_state_obstruction():
    """Trimmed code of the five-state trichotomy, with the > flag relocated."""
    return Instance(((6,5),(6,5),(-1,7),(8,7),(-1,-1),(1,-1),
                     (2,-1),(3,-1),(4,-1)),frozenset({4}),
                    frozenset({(0,2),(0,3),(5,6)}))


def obstruction_word(n,m):
    if type(n) is not int or type(m) is not int or n<0 or m<1:
        raise ValueError('n>=0 and m>=1 required')
    return '10'*n+'00'+'10'*m+'00'


def transport_tail_decision(I, H=1, max_variants=100000, limits=None):
    """Relocate, encode, and query the exact fixed-H separator relaxation.

    An actual witness or exhausted negative is definitive for I. A surviving
    non-witness remains UNKNOWN. This finite preprocessing search is not a
    theorem that some placement/H decides every input.
    """
    from separator_tail import relaxed_decision, Limits
    report,J=best_relocation(I,max_variants)
    marked=frozenset(map(tuple,report['marked']))
    K=compile_logical(J,marked)
    answer=relaxed_decision(K,'#',H,limits or Limits())
    result=dict(relocation=report,relaxation=answer,compiled_states=len(K.delta))
    if answer['status']=='NO':return dict(status='NO',**result)
    if answer['status']=='YES' and answer['actual_witness']:
        word=decode_logical(J,answer['word'],marked)
        assert witness(I,word) and border_witness(I,word)
        return dict(status='YES',word=word,**result)
    return dict(status='UNKNOWN',reason='Relaxation has an unverified survivor or resource cap',**result)


def eleven_state_nonflat_obstruction():
    """The six-state reset obstruction, encoded and with its > flag relocated.

    Cyclic support is genuinely nonflat. Its all-H counterexample and its
    repair use the SAME mechanism as the smaller nine-state fixture.
    """
    return Instance(((7,6),(7,6),(7,8),(7,9),(10,8),(-1,-1),
                     (1,-1),(2,-1),(3,-1),(4,-1),(5,-1)),frozenset({5}),
                    frozenset({(0,2),(0,3),(0,4),(6,7)}))
