"""A finite exact search for witnesses with a SUPPLIED maximal-run bound.

NO_WITHIN_RUN_BOUND does not mean unrestricted NO. The normalization theorem
bounds counts, not the number of runs. Enumeration is intentionally capped.
The NP proof uses guessed binary counts and the symbolic verifier, not a
claim that this exhaustive implementation is polynomial time.
"""
from collections import deque
from border_lab import Instance, witness, border_witness
from terminal_realization import validate
from run_normalization import unary, profile_runs, run_states, expand


def verify_runs(instance, runs):
    try:
        runs=tuple(runs)
        starts,end,visited=run_states(instance,runs)
        if end not in instance.final or len(instance.delta) in visited:
            return False
        return not (visited & instance.bad or profile_runs(instance,runs) & instance.flags)
    except (ValueError, IndexError, TypeError):
        return False


def solve_run_bound(instance, max_runs, max_prefixes=200000, max_count_entries=1000000):
    """Decide the run-bounded question, never infer an unbounded negative."""
    validate(instance)
    if any(any(q>=0 for q in instance.delta[f]) for f in instance.final):
        return dict(status='UNKNOWN',reason='Terminal accepting states are required')
    if type(max_runs) is not int or max_runs<0:
        raise ValueError('max_runs must be a nonnegative integer')
    for cap in (max_prefixes,max_count_entries):
        if cap is not None and (type(cap) is not int or cap<1):
            raise ValueError('Caps must be positive integers or None')
    k=len(instance.delta);ops=tuple(unary(instance,a) for a in '01')
    H=(k+1)**2;P=max(op.global_period for op in ops)
    M=max_runs*(H+P)
    common=dict(run_bound=max_runs,count_bound=M,threshold=H,
                periods=tuple(op.global_period for op in ops))
    if verify_runs(instance,()):
        return dict(common,status='YES',runs=(),word='',prefixes=1)
    if max_runs==0:
        return dict(common,status='NO_WITHIN_RUN_BOUND',prefixes=1)
    unsafe=set(instance.bad)|{p for p,q in instance.flags if p==q}
    if instance.start in unsafe:
        return dict(common,status='NO_WITHIN_RUN_BOUND',prefixes=1)
    cache={}; entries=0
    def choices(start,a):
        nonlocal entries
        key=(start,a)
        if key in cache:return cache[key]
        rows=[];q=start
        for n in range(1,M+1):
            q=instance.delta[q][int(a)]
            if q<0 or q in unsafe:break
            entries+=1
            if max_count_entries is not None and entries>max_count_entries:
                raise OverflowError('Count-table cap')
            rows.append((n,q))
        cache[key]=rows
        return rows
    todo=deque([((),instance.start)]);seen=1
    try:
        while todo:
            runs,q=todo.popleft()
            if runs and q in instance.final and verify_runs(instance,runs):
                length=sum(n for _,n in runs)
                word=expand(runs) if length<=1000000 else None
                if word is not None:
                    assert witness(instance,word) and border_witness(instance,word)
                return dict(common,status='YES',runs=runs,word=word,prefixes=seen)
            if len(runs)==max_runs or q in instance.final:continue
            letters=('0','1') if not runs else (str(1-int(runs[-1][0])),)
            for a in letters:
                for n,t in choices(q,a):
                    if max_prefixes is not None and seen>=max_prefixes:
                        return dict(common,status='UNKNOWN',reason='Run-prefix cap',prefixes=seen)
                    todo.append((runs+((a,n),),t));seen+=1
    except OverflowError as error:
        return dict(common,status='UNKNOWN',reason=str(error),prefixes=seen)
    return dict(common,status='NO_WITHIN_RUN_BOUND',prefixes=seen,
                reason='Every normalized count vector through the supplied run bound is exhausted')


def compile_unary_sync(automata):
    """Reduce POSITIVE unary intersection to exact 2*r-run terminal witnesses.

    Input uses BinaryDFA conventions but only letter 1 may be defined.
    Empty-word intersection can be reduced by first prefixing 1 to every
    input language; the complexity statement uses positive unary intersection.
    """
    ms=tuple(automata)
    if len(ms)<2 or any(any(row[0]>=0 for row in m.delta) for m in ms):
        raise ValueError('At least two unary DFAs (only 1 transitions) required')
    D=[];entries=[];copies=[]
    for m in ms:
        entries.append(len(D));D.append([-1,-1])
        copies.append(tuple(range(len(D),len(D)+len(m.delta))))
        D.extend([[-1,-1] for _ in m.delta])
    f=len(D);D.append([-1,-1])
    for i,m in enumerate(ms):
        q=m.delta[m.start][1]
        if q>=0:D[entries[i]][1]=copies[i][q]
        exit=entries[i+1] if i+1<len(ms) else f
        for q,row in enumerate(m.delta):
            if row[1]>=0:D[copies[i][q]][1]=copies[i][row[1]]
            if q in m.final:D[copies[i][q]][0]=exit
    flags=set()
    for i in range(len(ms)-1):
        flags.update((entries[i],q) for q in copies[-1])
        flags.update((p,entries[-1]) for p in copies[i])
    return Instance(tuple(map(tuple,D)),frozenset({f}),frozenset(flags)),2*len(ms)
