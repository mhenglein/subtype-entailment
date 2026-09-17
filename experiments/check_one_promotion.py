"""Whole matching-graph checks and complete bounded-rank existence oracles."""
from collections import Counter
from itertools import product
from pathlib import Path
import json,random
from border_lab import Instance,witness,border_witness,words
from prefix_rank_layers import Reference,prefix_function,ranks_and_milestones,valid_reverse_prefix
from one_promotion import PromotionSummary,solve_one_promotion,solve_rank_two,close
from check_prefix_rank_layers import example_endpoint,example_rich
from modular_sync_family import make_family
ROOT=Path(__file__).resolve().parents[1]


def explicit_matching_graph(I,C,base_length):
    """No failure links: enumerate suffix equality at every transition.

    Return exact all-pairs reachability on the summary's retained interface.
    """
    k=len(I.delta);n=len(C.word);acc=k*(n+1)
    rows=[0]*(acc+1)
    at=lambda q,j:j*k+q
    for j in range(n+1):
        for q in range(k):
            src=at(q,j)
            if q==I.start and j<n:rows[src]|=1<<acc
            if j==n:continue
            for b in '01':
                text=C.word[:j]+b
                t=max(x for x in range(min(n,len(text))+1) if text.endswith(C.word[:x]))
                chain=[x for x in range(t+1) if C.word[:t].endswith(C.word[:x])]
                for p in range(k):
                    if p in I.bad or I.delta[p][int(b)]!=q:continue
                    if (p,p) in I.flags or any((p,C.labels[x]) in I.flags for x in chain):continue
                    rows[src]|=1<<at(p,t)
    # Independent DFS from each retained boundary; no transitive-closure code.
    kept=[at(q,j) for j in range(base_length+1) for q in range(k)]+[acc]+[at(q,n) for q in range(k)]
    out=[]
    for start in kept:
        seen={start};todo=[start]
        for u in todo:
            for v in range(len(rows)):
                if rows[u]>>v&1 and v not in seen:seen.add(v);todo.append(v)
        out.append(sum(1<<j for j,v in enumerate(kept) if v in seen))
    return tuple(out)


def all_dag_words(I):
    assert all(t<0 or t>q for q,row in enumerate(I.delta) for t in row)
    todo=[('',I.start)]
    while todo:
        w,q=todo.pop()
        if q in I.final:yield w
        for a,p in enumerate(I.delta[q]):
            if p>=0:todo.append((w+str(a),p))


def check():
    rng=random.Random(2026091520);C=Counter();verdict=Counter();graph_queries=0
    instances=[]
    for _ in range(180):
        k=rng.randrange(2,8)
        D=tuple(tuple(rng.choice([-1]+list(range(q+1,k))) for a in '01') for q in range(k-1))+((-1,-1),)
        F=frozenset({k-1})
        G=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.13)
        bad=frozenset(q for q in range(k) if rng.random()<.03)
        I=Instance(D,F,G,bad,rng.randrange(k));instances.append(I)
        expected=[]
        for w in all_dag_words(I):
            good=witness(I,w);assert good==border_witness(I,w)
            if good and max(ranks_and_milestones(w[::-1])[0])<=2:expected.append(w)
            C['complete_dag_candidates']+=1
        ans=solve_rank_two(I,max_summaries=None,max_work=None)
        assert (ans['status']=='FOUND_WITNESS')==bool(expected),(I,ans,expected)
        assert ans['status'] in ('FOUND_WITNESS','NO_WITHIN_RANK_TWO')
        verdict[ans['status']]+=1;C['complete_dag_oracles']+=1
    # Exact all-pairs graph summaries for actual references from generated paths.
    for _ in range(160):
        k=rng.randrange(3,7)
        D=tuple(tuple(rng.randrange(-1,k) for a in '01') for q in range(k-1))+((-1,-1),)
        I=Instance(D,frozenset({k-1}),frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.10))
        for w in words('01',7):
            if not witness(I,w) or not w:continue
            rho=w[::-1];labels=I.run(w)[::-1];_,ms=ranks_and_milestones(rho)
            for h in range(len(ms)-1):
                m,n=ms[h],ms[h+1]
                B=Reference(rho[:m],labels[:m+1]);S=PromotionSummary(I,B);R=S.initial
                fail=S.pi[m]
                for end in range(m+1,n+1):
                    a=rho[end-1];p=labels[end];nfail=S.advance[fail,a]
                    R=S.extend(R,fail,a,p,nfail,initial=(end==m+1))
                    P=Reference(rho[:end],labels[:end+1])
                    assert R==explicit_matching_graph(I,P,m),(I,B,P)
                    fail=nfail;C['full_summary_graph_equivalences']+=1
                    C['compared_boundary_pairs']+=len(R)**2
            if C['full_summary_graph_equivalences']>350:break
        if C['full_summary_graph_equivalences']>350:break
    fixtures=[]
    # A return at the end still increases rank; never accept it for free.
    for n in range(1,8):
        I=Instance(tuple((j+1,-1) for j in range(n))+((-1,-1),),frozenset({n}))
        out=solve_rank_two(I,max_summaries=None,max_work=None)
        assert (out['status']=='FOUND_WITNESS')==(n<=2),(n,out)
        C['terminal_hit_rank_regressions']+=1
    for name,I in [('endpoint_collision',example_endpoint()),('rich_collision',example_rich()),('equality_antichain',example_rich(True))]:
        out=solve_rank_two(I,max_summaries=None,max_work=None)
        assert out['status']=='FOUND_WITNESS'
        fixtures.append(dict(name=name,result=out));C['repaired_quotient_failures']+=1
    for ps in product(range(1,4),repeat=2):
        F=make_family(ps);out=solve_rank_two(F.instance,max_summaries=5000,max_work=50000)
        assert out['status']=='FOUND_WITNESS',(ps,out)
        assert witness(F.instance,out['word'])
        fixtures.append(dict(name='two_block_modular',periods=ps,result=out));C['infinite_modular_positive_oracles']+=1
    for ps in [(1,1,1),(1,1,2),(1,2,2)]:
        F=make_family(ps);out=solve_rank_two(F.instance,max_summaries=10000,max_work=100000)
        assert out['status']=='NO_WITHIN_RANK_TWO',(ps,out)
        w=('1'*F.common_period+'0')*len(ps)
        assert witness(F.instance,w) and max(ranks_and_milestones(w[::-1])[0])==3
        fixtures.append(dict(name='positive_but_rank_three',periods=ps,known_witness=w,result=out));C['rank_three_boundary_oracles']+=1
    I=example_rich();B=Reference('1',(5,2))
    assert solve_one_promotion(I,B,max_summaries=1)['status']=='UNKNOWN'
    assert solve_one_promotion(I,B,max_work=1)['status']=='UNKNOWN'
    C['intentional_caps']=2
    return dict(status='PASS',seed=2026091520,counts=dict(C),dag_verdicts=dict(verdict),fixtures=fixtures,
                scope='Exact one-promotion elimination and rank-at-most-two existence, not unrestricted existence',
                proof_status='Written graph-interface proof plus executed checks; no independent mathematical review or Lean')

if __name__=='__main__':
    if not __debug__:raise SystemExit('Assertions must be enabled')
    out=check();text=json.dumps(out,indent=2)+'\n'
    (ROOT/'results/one-promotion.json').write_text(text);print(text)
