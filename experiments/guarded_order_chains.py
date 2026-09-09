"""Exact proof-producing decision for modular, phase-blind unary stage chains.

A supplied r-stage spec denotes 0^n0 1 ... 0^n(r-1) 1. Every positive count
has a lower bound and one congruence. Flags distinguish entry versus interior
of a stage, not cycle phase. This is a complete class, NOT arbitrary BorderAvoid.
The order-Horn algorithm is self-contained; see the dated proof and route.
"""
from dataclasses import dataclass
from math import gcd, lcm
from typing import Optional

from border_lab import Instance


@dataclass(frozen=True)
class Domain:
    lower: int = 1
    residue: int = 0
    modulus: int = 1

    def __post_init__(self):
        if (type(self.lower) is not int or self.lower < 1 or
            type(self.modulus) is not int or self.modulus < 1 or
            type(self.residue) is not int or not 0 <= self.residue < self.modulus):
            raise ValueError('Positive lower/modulus and canonical residue required')


@dataclass(frozen=True)
class Chain:
    domains: tuple
    flags: frozenset = frozenset()

    def __post_init__(self):
        if not self.domains or any(not isinstance(d, Domain) for d in self.domains):
            raise ValueError('At least one Domain is required')
        r = len(self.domains)
        if any(len(g) != 2 or any(type(q) is not int or not 0 <= q <= 2*r for q in g)
               for g in self.flags):
            raise ValueError('Invalid entry/interior/final role flag')


def clauses(spec):
    """Literal exact flag-to-guard translation; indices are stage indices."""
    r = len(spec.domains)
    out = []
    for p, q in sorted(spec.flags):
        if p == q or q == 2*r:
            out.append(dict(flag=[p, q], guard=[], kind='false'))
            continue
        if p == 2*r or p//2 >= q//2:
            continue  # No proper agreement within one positive unary stage.
        i, j = p//2, q//2
        guard = [[i+h, j+h] for h in range(1, r-j)]
        if p % 2 == q % 2 == 0:
            out.append(dict(flag=[p,q], guard=guard, kind='ne', pair=[i,j]))
        elif p % 2 == q % 2 == 1:
            out.append(dict(flag=[p,q], guard=guard, kind='false'))
        else:
            pair = [j,i] if p % 2 == 0 else [i,j]
            out.append(dict(flag=[p,q], guard=guard, kind='le', pair=pair))
    return out


def _closure(r, edges):
    reach = [[i == j for j in range(r)] for i in range(r)]
    for i, j in edges:
        reach[i][j] = True
    for k in range(r):
        for i in range(r):
            if reach[i][k]:
                for j in range(r):
                    reach[i][j] |= reach[k][j]
    return reach


def _active(c, reach):
    return all(reach[i][j] and reach[j][i] for i,j in c['guard'])


def _domain_conflict(spec, reach):
    for i, a in enumerate(spec.domains):
        for j, b in enumerate(spec.domains[:i]):
            if (reach[i][j] and reach[j][i] and
                (a.residue-b.residue) % gcd(a.modulus,b.modulus)):
                return [j,i]
    return None


def _crt(a, m, b, n):
    g = gcd(m,n)
    if (b-a) % g:
        raise ValueError('Inconsistent congruences')
    mod = n//g
    t = 0 if mod == 1 else (((b-a)//g)*pow(m//g, -1, mod)) % mod
    period = m*mod
    return (a+m*t) % period, period


def _model(spec, reach):
    r = len(spec.domains)
    unseen = set(range(r)); groups = []
    while unseen:
        i = min(unseen)
        group = sorted(j for j in unseen if reach[i][j] and reach[j][i])
        groups.append(group); unseen.difference_update(group)
    # A deterministic topological ordering, assigning distinct values to all
    # different forced-equality classes. Thus no inactive guard becomes true.
    todo = set(range(len(groups))); ordered = []
    while todo:
        g = min(t for t in todo if not any(
            s != t and reach[groups[s][0]][groups[t][0]] for s in todo))
        todo.remove(g); ordered.append(groups[g])
    values = [None]*r
    previous = max(d.lower for d in spec.domains)-1
    for group in ordered:
        residue, modulus = 0, 1
        for i in group:
            d = spec.domains[i]
            residue,modulus = _crt(residue,modulus,d.residue,d.modulus)
        start = previous+1
        value = start+(residue-start) % modulus
        for i in group:
            values[i] = value
        previous = value
    return values


def check_values(spec, values):
    """Check the finite count certificate, without expanding a long word."""
    if len(values) != len(spec.domains):
        return False
    if any(type(v) is not int or v < d.lower or v % d.modulus != d.residue
           for v,d in zip(values,spec.domains)):
        return False
    for c in clauses(spec):
        if not all(values[i] == values[j] for i,j in c['guard']):
            continue
        if c['kind'] == 'false':
            return False
        i,j = c['pair']
        if c['kind'] == 'le' and values[i] > values[j]:
            return False
        if c['kind'] == 'ne' and values[i] == values[j]:
            return False
    return True


def solve(spec):
    """Uncapped complete decision for the explicitly supplied class.

    Every nonfinal productive round adds an inequality. At most r(r-1) such
    additions occur. Compact counts and finite proof steps avoid word expansion.
    """
    cs = clauses(spec); r = len(spec.domains)
    edges = set(); reach = _closure(r,edges); steps = []
    rounds = 0
    while True:
        rounds += 1
        changed = False
        for index,c in enumerate(cs):
            if not _active(c,reach):
                continue
            if c['kind'] == 'false':
                return dict(status='NO', steps=steps, conflict=dict(kind='clause',index=index), rounds=rounds)
            i,j = c['pair']
            if c['kind'] == 'ne':
                if reach[i][j] and reach[j][i]:
                    return dict(status='NO',steps=steps,conflict=dict(kind='clause',index=index),rounds=rounds)
            elif not reach[i][j]:
                edges.add((i,j)); steps.append(index)
                reach = _closure(r,edges); changed = True
                conflict = _domain_conflict(spec,reach)
                if conflict is not None:
                    return dict(status='NO',steps=steps,conflict=dict(kind='domain',pair=conflict),rounds=rounds)
        if not changed:
            values = _model(spec,reach)
            assert check_values(spec,values)
            P = lcm(*(d.modulus for d in spec.domains))
            B = max(d.lower for d in spec.domains)+r*P
            assert max(values) <= B
            return dict(status='YES',values=values,length=sum(values)+r,
                        steps=steps,rounds=rounds,count_bound=B)


def verify(spec, certificate):
    """Independent finite proof replay, using graph reachability per premise.

    Rejects malformed/out-of-order steps. A successful NO verification does not
    rerun the solver or enumerate candidate words.
    """
    if certificate.get('status') == 'YES':
        return check_values(spec,certificate.get('values',[]))
    if certificate.get('status') != 'NO':
        return False
    r=len(spec.domains);cs=clauses(spec);graph=[set() for _ in range(r)]
    def path(a,b):
        seen={a};todo=[a]
        for v in todo:
            for nxt in graph[v]:
                if nxt not in seen:
                    seen.add(nxt);todo.append(nxt)
        return b in seen
    def equal(a,b):
        return path(a,b) and path(b,a)
    for index in certificate.get('steps',[]):
        if type(index) is not int or not 0 <= index < len(cs):
            return False
        c=cs[index]
        if c['kind'] != 'le' or not all(equal(i,j) for i,j in c['guard']):
            return False
        i,j=c['pair'];graph[i].add(j)
    conflict=certificate.get('conflict',{})
    if conflict.get('kind') == 'domain':
        pair=conflict.get('pair',[])
        if len(pair)!=2 or any(type(i) is not int or not 0<=i<r for i in pair):
            return False
        i,j=pair;a,b=spec.domains[i],spec.domains[j]
        return equal(i,j) and bool((a.residue-b.residue)%gcd(a.modulus,b.modulus))
    if conflict.get('kind') == 'clause':
        index=conflict.get('index')
        if type(index) is not int or not 0<=index<len(cs):
            return False
        c=cs[index]
        if not all(equal(i,j) for i,j in c['guard']):
            return False
        return c['kind']=='false' or (c['kind']=='ne' and equal(*c['pair']))
    return False


def compile_chain(spec, max_states: Optional[int] = 100000):
    """Exact binary terminal DFA with role flags lifted to all cycle phases.

    A construction cap raises ValueError, never NO. Large count witnesses need
    not be expanded to decide the symbolic input.
    """
    size=1+sum(d.lower+d.modulus for d in spec.domains)
    if max_states is not None and (type(max_states) is not int or max_states<1):
        raise ValueError('max_states must be positive or None')
    if max_states is not None and size>max_states:
        raise ValueError('Compilation state cap')
    rows=[];roles=[];entries=[];ends=[]
    for stage,d in enumerate(spec.domains):
        entry=len(rows);entries.append(entry)
        # One entry, lower-1 transient positive counts, modulus cycle positions.
        positive=d.lower+d.modulus-1
        rows.extend([[-1,-1] for _ in range(positive+1)])
        roles.extend([2*stage]+[2*stage+1]*positive)
        for count in range(positive+1):
            rows[entry+count][0] = entry+count+1 if count<positive else entry+d.lower
            if count>=d.lower and count % d.modulus==d.residue:
                ends.append((entry+count,stage+1))
    final=len(rows);rows.append([-1,-1]);roles.append(2*len(spec.domains));entries.append(final)
    for state,stage in ends:
        rows[state][1]=entries[stage]
    flags=frozenset((p,q) for p,pr in enumerate(roles) for q,qr in enumerate(roles) if (pr,qr) in spec.flags)
    return Instance(tuple(map(tuple,rows)),frozenset({final}),flags),roles


def expand(values, max_length: Optional[int] = 1000000):
    length=sum(values)+len(values)
    if max_length is not None and length>max_length:
        raise ValueError('Word expansion cap')
    return ''.join('0'*v+'1' for v in values)
