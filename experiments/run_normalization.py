"""Profile-preserving normalization of homogeneous runs in terminal words.

No computable bound on the NUMBER of runs is supplied. This is not an
unrestricted witness-existence decider. Counts are binary integers; expansion
has a cap. See notes/2026-09-06-run-normalization.md for the written proof.
"""
from dataclasses import dataclass
from math import gcd
from terminal_realization import validate


def rle(word):
    if any(a not in '01' for a in word):
        raise ValueError('Expected binary word')
    out=[]
    for a in word:
        if out and out[-1][0]==a:
            out[-1]=(a,out[-1][1]+1)
        else:
            out.append((a,1))
    return tuple(out)


def expand(runs, max_length=1000000):
    runs=tuple(runs)
    if any(a not in '01' or type(n) is not int or n<1 for a,n in runs):
        raise ValueError('Expected positive binary runs')
    if max_length is not None and sum(n for _,n in runs)>max_length:
        raise ValueError('Explicit expansion cap')
    return ''.join(a*n for a,n in runs)


@dataclass(frozen=True)
class Unary:
    transitions: tuple
    paths: tuple
    entries: tuple
    periods: tuple
    global_period: int

    def power(self, p, n):
        if type(n) is not int or n<0:
            raise ValueError('Nonnegative integer exponent required')
        path=self.paths[p]; mu=self.entries[p]; period=self.periods[p]
        return path[n] if n<len(path) else path[mu+(n-mu)%period]

    def prefix_states(self, p, steps):
        """States after exponents 0 through steps inclusive."""
        if steps<0:return frozenset()
        return frozenset(self.paths[p][:min(steps+1,len(self.paths[p]))])


def unary(instance, letter):
    if letter not in ('0','1'):
        raise ValueError('A binary letter is required')
    k=len(instance.delta)
    trans=tuple(row[int(letter)] if row[int(letter)]>=0 else k for row in instance.delta)+(k,)
    paths=[]; entries=[]; periods=[]; P=1
    for start in range(k+1):
        path=[]; seen={}; q=start
        while q not in seen:
            seen[q]=len(path);path.append(q);q=trans[q]
        mu=seen[q]; per=len(path)-mu
        paths.append(tuple(path));entries.append(mu);periods.append(per)
        P=P*per//gcd(P,per)
    return Unary(trans,tuple(paths),tuple(entries),tuple(periods),P)


def count_map(values, threshold, period):
    """Shrink sorted gaps, retaining threshold comparisons and residues.

    For all x<=y in {0} union values: the difference is unchanged if <=H,
    remains >H otherwise, and is always unchanged modulo period.
    """
    values=tuple(values)
    if threshold<0 or period<1 or any(type(n) is not int or n<0 for n in values):
        raise ValueError('Invalid count-compression parameters')
    out={0:0}; old=new=0
    for n in sorted(set(values)-{0}):
        gap=n-old
        mapped=gap if gap<=threshold else threshold+1+(gap-threshold-1)%period
        new+=mapped; out[n]=new;old=n
    return out


def run_states(instance, runs, ops=None):
    """Run starts, final state, and exact visited-state set, without expansion."""
    validate(instance)
    ops=ops or tuple(unary(instance,a) for a in '01')
    q=instance.start; starts=[]; visited={q}; previous=None
    for a,n in runs:
        if a not in '01' or type(n) is not int or n<1 or a==previous:
            raise ValueError('Expected positive canonical alternating runs')
        starts.append(q); u=ops[int(a)]
        visited.update(u.prefix_states(q,n));q=u.power(q,n);previous=a
    return tuple(starts),q,frozenset(visited)


def profile_direct(instance, word):
    states=instance.run(word)
    if states is None: raise ValueError('Undefined run')
    return frozenset((states[i],states[j]) for j in range(len(word)+1)
                     for i in range(j+1) if word.startswith(word[j:],i))


def pair_tail_states(op, p, q, left_length, right_length):
    """State pairs before identical positive unary tails, t=1..min(lengths)."""
    low=min(left_length,right_length)
    p=op.power(p,left_length-low);q=op.power(q,right_length-low)
    out=set();seen=set()
    for _ in range(min(low,len(op.transitions)**2)):
        pair=(p,q)
        if pair in seen:break
        seen.add(pair);out.add(pair)
        p=op.transitions[p];q=op.transitions[q]
    return frozenset(out)


def profile_runs(instance, runs):
    """Exact full agreement profile of a terminal accepted RLE word.

    No count-dependent loop is used except the final run, whose length is
    strictly less than the original state count by terminal acceptance.
    """
    runs=tuple(runs)
    ops=tuple(unary(instance,a) for a in '01')
    starts,end,visited=run_states(instance,runs,ops)
    k=len(instance.delta)
    if k in visited or end not in instance.final or any(q>=0 for q in instance.delta[end]):
        raise ValueError('A defined accepted run ending at a terminal state is required')
    out={(q,q) for q in visited}|{(q,end) for q in visited}
    if not runs:return frozenset(out)
    last=len(runs)-1; final_a, final_n=runs[-1]
    assert final_n<k
    for j in range(last):
        a,nj=runs[j]
        for i in range(j):
            if runs[i][0]!=a:continue
            distance=last-j
            if any(runs[i+h][1]!=runs[j+h][1] for h in range(1,distance)):
                continue
            if runs[i+distance][1]<final_n:continue
            out.update(pair_tail_states(ops[int(a)],starts[i],starts[j],runs[i][1],nj))
    # Every positive target suffix inside the last run is a pure-letter word.
    op=ops[int(final_a)]
    for t in range(1,final_n+1):
        target=op.power(starts[last],final_n-t)
        for i,(a,n) in enumerate(runs):
            if a==final_a and n>=t:
                out.update((source,target) for source in op.prefix_states(starts[i],n-t))
    return frozenset(out)


def normalize(instance, runs):
    """A no-longer RLE word with the EXACT original agreement profile.

    Terminal acceptance, visited states, run starts, all flags and the number
    of maximal runs are preserved. This does not bound that number of runs.
    """
    runs=tuple(runs);validate(instance)
    k=len(instance.delta);ops=tuple(unary(instance,a) for a in '01')
    starts,end,visited=run_states(instance,runs,ops)
    if k in visited or end not in instance.final or any(q>=0 for q in instance.delta[end]):
        raise ValueError('A defined accepted terminal word is required')
    H=(k+1)**2
    periods=[1,1]
    for (a,_),start in zip(runs,starts):
        per=ops[int(a)].periods[start]
        periods[int(a)]=periods[int(a)]*per//gcd(periods[int(a)],per)
    maps=tuple(count_map([n for b,n in runs if b==a],H,periods[int(a)]) for a in '01')
    result=tuple((a,maps[int(a)][n]) for a,n in runs)
    new_starts,new_end,new_visited=run_states(instance,result,ops)
    assert (new_starts,new_end,new_visited)==(starts,end,visited)
    assert profile_runs(instance,result)==profile_runs(instance,runs)
    bound=len(runs)**2*(H+max(periods))
    assert sum(n for _,n in result)<=bound
    assert sum(n for _,n in result)<=sum(n for _,n in runs)
    return dict(runs=result,original_length=sum(n for _,n in runs),
                normalized_length=sum(n for _,n in result),run_count=len(runs),
                threshold=H,periods=tuple(periods),
                global_periods=tuple(op.global_period for op in ops),
                length_bound=bound,maps=maps)
