"""Exact synthesis through ONE unknown reference promotion.

This decides completion with at most one new first-return milestone after a
supplied concrete reference. It is not a decision for arbitrary rank depth.
The finite summary is graph reachability across an explicitly fixed boundary,
not an ordinary word transition action or agreement-profile quotient.
"""
from collections import deque
from prefix_rank_layers import Reference,prefix_function,border_chain,valid_reverse_prefix,layer_graph
from border_lab import witness,border_witness


def close(rows):
    """Reflexive transitive closure; each row is an integer bit set."""
    R=list(rows)
    for i in range(len(R)):R[i]|=1<<i
    for j in range(len(R)):
        bit=1<<j
        for i in range(len(R)):
            if R[i]&bit:R[i]|=R[j]
    return tuple(R)


class PromotionSummary:
    def __init__(self,I,B):
        if not B.word or not valid_reverse_prefix(I,B.word,B.labels):
            raise ValueError('A locally safe concrete reference is required')
        self.I,self.B=I,B
        self.k,self.m=len(I.delta),len(B.word)
        self.pi=prefix_function(B.word)
        self.acc=self.k*(self.m+1)
        self.core=self.acc+1
        self.n=self.core+self.k
        self.incoming=[[[] for a in '01'] for _ in range(self.k)]
        for p,row in enumerate(I.delta):
            if p in I.bad:continue
            for a,q in enumerate(row):
                if q>=0:self.incoming[q][a].append(p)
        self.advance={}
        for j in range(self.m):
            for a in '01':
                t=j
                while t and B.word[t]!=a:t=self.pi[t]
                if B.word[t]==a:t+=1
                self.advance[j,a]=t
        rows=[0]*self.n
        for j in range(self.m+1):
            for q in range(self.k):
                i=self.at(q,j)
                if q==I.start:rows[i]|=1<<self.acc
                if j==self.m:continue # next pattern letter is not known yet
                for a in '01':
                    t=self.advance[j,a]
                    for p in self.incoming[q][int(a)]:
                        if self.allowed(p,border_chain(self.pi,t)):
                            rows[i]|=1<<self.at(p,t)
        self.initial=close(rows)

    def at(self,q,j):return j*self.k+q

    def allowed(self,p,chain,extra=None):
        if (p,p) in self.I.flags:return False
        if extra is not None and (p,extra) in self.I.flags:return False
        return not any((p,self.B.labels[t]) in self.I.flags for t in chain)

    def extend(self,R,failure,a,next_label,next_failure,initial=False):
        """Append one labelled PATTERN position; forget only retired frontier.

        R is reachability among fixed core and current frontier. Future mismatch
        edges point only into the core; future match edges go to the new frontier.
        Hence closure followed by projection is exact.
        """
        new=self.n
        rows=list(R)+[0]*self.k
        for q in range(self.k):
            old=self.at(q,self.m) if initial else self.core+q
            # This column becomes a PROPER pattern prefix only now.
            if q==self.I.start:rows[old]|=1<<self.acc
            for b in '01':
                if b==a:
                    chain=border_chain(self.pi,next_failure)
                    for p in self.incoming[q][int(b)]:
                        if self.allowed(p,chain,next_label):rows[old]|=1<<(new+p)
                else:
                    t=self.advance[failure,b]
                    chain=border_chain(self.pi,t)
                    for p in self.incoming[q][int(b)]:
                        if self.allowed(p,chain):rows[old]|=1<<self.at(p,t)
        # No accepting edge at the new frontier: a full pattern return
        # would be a further milestone, outside this completion layer.
        R=close(rows)
        keep=list(range(self.core))+list(range(new,new+self.k))
        out=[]
        for i in keep:
            mask=0
            for j,old in enumerate(keep):
                if R[i]>>old&1:mask|=1<<j
            out.append(mask)
        return tuple(out)

    def completable(self,R,endpoint):
        return bool(R[self.at(endpoint,self.m)]>>self.acc&1)


def solve_one_promotion(I,B,max_summaries=20000,max_work=2000000):
    """Complete at depth at most depth(B)+1; failure stays explicitly scoped."""
    S=PromotionSummary(I,B)
    finish=layer_graph(I,B,max_states=None,allow_return_completion=False)
    if finish['status']=='FOUND_WITNESS':
        return dict(status='FOUND_WITNESS',word=finish['word'],promotions=0,summaries=1,work=0)
    start=(B.labels[-1],S.pi[S.m],True,S.initial)
    todo=deque([start]);parent={start:None};work=0
    def recover(cur,step):
        seq=[step]
        while parent[cur] is not None:
            old,a=parent[cur];seq.append((a,cur[0]));cur=old
        seq.reverse()
        R=Reference(B.word+''.join(a for a,p in seq),B.labels+tuple(p for a,p in seq))
        assert valid_reverse_prefix(I,R.word,R.labels)
        return R
    while todo:
        cur=todo.popleft();q,h,initial,R=cur
        for a in '01':
            t=S.advance[h,a]
            for p in S.incoming[q][int(a)]:
                if not S.allowed(p,border_chain(S.pi,t)):continue
                work+=1
                if max_work is not None and work>max_work:
                    return dict(status='UNKNOWN',reason='Work cap',summaries=len(parent),work=work)
                T=S.extend(R,h,a,p,t,initial)
                if t==S.m:
                    if S.completable(T,p):
                        C=recover(cur,(a,p))
                        out=layer_graph(I,C,max_states=None,allow_return_completion=False)
                        assert out['status']=='FOUND_WITNESS', (C,out)
                        w=out['word'];assert witness(I,w) and border_witness(I,w)
                        return dict(status='FOUND_WITNESS',word=w,promotions=1,
                                    promoted_reference=C.word,reference_labels=C.labels,
                                    summaries=len(parent),work=work,
                                    boundary_vertices=S.n)
                else:
                    nxt=(p,t,False,T)
                    if nxt not in parent:
                        if max_summaries is not None and len(parent)>=max_summaries:
                            return dict(status='UNKNOWN',reason='Summary cap',summaries=len(parent),work=work)
                        parent[nxt]=(cur,a);todo.append(nxt)
    return dict(status='NO_WITHIN_ONE_PROMOTION',summaries=len(parent),work=work,
                boundary_vertices=S.n,meaning='Exact scoped negative, NOT unrestricted NO')


def solve_rank_two(I,max_summaries=20000,max_work=2000000):
    """Exact existence with maximum reversed border-chain depth at most TWO."""
    if any(any(q>=0 for q in I.delta[f]) for f in I.final):
        raise ValueError('Terminal final states required')
    if witness(I,''):return dict(status='FOUND_WITNESS',word='',branches=[])
    branches=[];unknown=False
    for f in sorted(I.final-I.bad):
        if (f,f) in I.flags:continue
        for p,row in enumerate(I.delta):
            for a,t in enumerate(row):
                if t!=f:continue
                B=Reference(str(a),(f,p))
                if not valid_reverse_prefix(I,B.word,B.labels):continue
                out=solve_one_promotion(I,B,max_summaries,max_work)
                branches.append(out)
                if out['status']=='FOUND_WITNESS':
                    return dict(status='FOUND_WITNESS',word=out['word'],branches=branches)
                if out['status']=='UNKNOWN':unknown=True
    return dict(status='UNKNOWN' if unknown else 'NO_WITHIN_RANK_TWO',branches=branches,
                meaning='No unrestricted negative conclusion unless an independent rank bound applies')
