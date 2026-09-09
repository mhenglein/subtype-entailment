"""Counter-update errors with two unary copies and arbitrary trailing context.

This is NOT a BorderAvoid compiler. The trailing context is precisely the
missing terminal-anchor gadget in the opposing research route.
"""
from dataclasses import dataclass
import re


@dataclass(frozen=True)
class Edge:
    source: int
    target: int
    changes: tuple
    tests: tuple = (None,None)  # None, 0 (zero), 1 (positive)

    def __post_init__(self):
        if (type(self.source) is not int or self.source<0 or
            type(self.target) is not int or self.target<0 or
            len(self.changes)!=2 or any(type(d) is not int or d not in (-1,0,1) for d in self.changes) or
            len(self.tests)!=2 or any(t not in (None,0,1) for t in self.tests)):
            raise ValueError('Invalid two-counter edge')


@dataclass(frozen=True)
class Machine:
    edges: tuple
    start: int
    final: frozenset


def encode(configurations, edge_ids):
    if not configurations or len(edge_ids)+1 != len(configurations):
        raise ValueError('Need one more configuration than edge ids')
    parts=[]
    for i,(q,a,b) in enumerate(configurations):
        if any(type(v) is not int or v<0 for v in (q,a,b)):
            raise ValueError('Nonnegative state and counters required')
        parts.append(f'S{q}:'+ '0'*(a+1)+','+'0'*(b+1))
        if i<len(edge_ids):parts.append(f'E{edge_ids[i]}')
    return '@'+';'.join(parts)+'!'


def in_regular_candidate(machine,configurations,edge_ids):
    """Finite-control syntax and zero tests, but deliberately not updates.

    Unary positivity/zero, initial/final control and edge consistency are all
    regular properties of the encoded history. Numeric update equality is not
    included here.
    """
    if not configurations or len(edge_ids)+1!=len(configurations):return False
    if configurations[0]!=(machine.start,0,0) or configurations[-1][0] not in machine.final:return False
    for (q,a,b),nxt,eid in zip(configurations,configurations[1:],edge_ids):
        if not 0<=eid<len(machine.edges):return False
        e=machine.edges[eid]
        if (q,nxt[0])!=(e.source,e.target):return False
        for v,change,test in zip((a,b),e.changes,e.tests):
            if v<0 or (test==0 and v!=0) or (test==1 and v==0):return False
            if v==0 and change==-1:return False
    return all(a>=0 and b>=0 for q,a,b in configurations)


def arithmetic_bad(machine,configurations,edge_ids):
    return any((na,nb)!=(a+machine.edges[eid].changes[0],b+machine.edges[eid].changes[1])
               for (q,a,b),(_,na,nb),eid in zip(configurations,configurations[1:],edge_ids))


def error_patterns(machine):
    """A finite union A X B X C, X in 0+, for all numeric update errors.

    Each returned regex has exactly one capture used exactly once. All other
    factors are regular. Restrict its input to the regular candidate language.
    """
    prior=r'@(?:S[0-9]+:0+,0+;E[0-9]+;)*'
    rest=r'(?:;E[0-9]+;S[0-9]+:0+,0+)*!'
    answer=[]
    for eid,e in enumerate(machine.edges):
        for counter,delta in enumerate(e.changes):
            A=prior+f'S{e.source}:'+(r'0+,' if counter else '')
            if counter==0:
                B=rf',0+;E{eid};S{e.target}:'
                C=r',0+'+rest
            else:
                B=rf';E{eid};S{e.target}:0+,'
                C=rest
            for direction in ('high','low'):
                k=delta+1 if direction=='high' else 1-delta
                extra='0'*k+r'0*'
                pattern=(A+r'(?P<x>0+)'+B+r'(?P=x)'+extra+C if direction=='high'
                         else A+r'(?P<x>0+)'+extra+B+r'(?P=x)'+C)
                answer.append(dict(edge=eid,counter=counter,direction=direction,
                                   pattern='^'+pattern+r'\Z',regex=re.compile('^'+pattern+r'\Z')))
    return answer
