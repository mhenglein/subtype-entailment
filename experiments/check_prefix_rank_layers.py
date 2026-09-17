"""Independent checks of the global rank representation and failed quotients.

No search-exhaustion result in this module is an unrestricted NO certificate.
"""
from collections import Counter, deque
from itertools import product
from pathlib import Path
import hashlib,json,random
from border_lab import Instance,words,witness,border_witness
from prefix_rank_layers import (Reference,prefix_function,border_chain,
    ranks_and_milestones,valid_reverse_prefix,layer_graph,shortest_endpoint_heuristic,
    enriched_heuristic,forward_action,reverse_profile,bounded_witness)
ROOT=Path(__file__).resolve().parents[1]


def literal_borders(w):
    return tuple(i for i in range(len(w),-1,-1) if w[:i]==w[len(w)-i:])


def equivalent_layer_languages(I,B):
    """Whole regular-language equivalence: KMP vs literal suffix-window monitor.

    Both consume labels (bit, predecessor state). This makes the reverse path
    explicit rather than treating nondeterministic state choices independently.
    Accepting outputs distinguish original-start completion and each growth end.
    """
    pi=prefix_function(B.word);m=len(B.word);k=len(I.delta)
    start1=(B.labels[-1],pi[m],False)
    start2=(B.labels[-1],B.word[-(m-1):] if m>1 else '',False)
    def km(state,a,p):
        if state is None:return None
        q,j,done=state
        if done or p in I.bad or I.delta[p][int(a)]!=q:return None
        t=j
        while t and B.word[t]!=a:t=pi[t]
        if B.word[t]==a:t+=1
        if (p,p) in I.flags or any((p,B.labels[b]) in I.flags for b in border_chain(pi,t)):
            return None
        return p,t,t==m
    def window(state,a,p):
        if state is None:return None
        q,old,done=state
        if done or p in I.bad or I.delta[p][int(a)]!=q:return None
        w=old+a
        matches=[b for b in range(m+1) if b<=len(w) and (w.endswith(B.word[:b]) if b else True)]
        if (p,p) in I.flags or any((p,B.labels[b]) in I.flags for b in matches):return None
        done=m in matches
        return p,(w[-(m-1):] if m>1 else ''),done
    def output(state):
        if state is None:return False,None
        return state[0]==I.start,(state[0] if state[-1] else None)
    seen={(start1,start2)};todo=list(seen)
    for a,b in todo:
        assert output(a)==output(b),(I,B,a,b)
        for bit in '01':
            for p in range(k):
                c=km(a,bit,p),window(b,bit,p)
                if c not in seen:seen.add(c);todo.append(c)
    return len(seen)


def profile_signature(I,B):
    return dict(endpoint=B.labels[-1],action=forward_action(I,B.word),
                visited=sorted(set(B.labels)),profile=sorted(reverse_profile(B.word,B.labels)))


def example_endpoint():
    return Instance(((2,-1),(3,1),(1,-1),(-1,-1)),frozenset({3}),frozenset({(0,2)}))


def example_rich(equality=False):
    flags={(0,1),(0,3),(4,3)} if not equality else {(0,1),(0,2),(4,3)}
    return Instance(((4,-1),(2,-1),(1,5),(1,-1),(4,3),(-1,-1)),frozenset({5}),frozenset(flags))


def comb_family(a,b):
    assert a>=2 and a%2==0 and b>=1
    I=Instance(((-1,1),(0,2),(3,1),(-1,-1)),frozenset({3}),frozenset({(1,0)}))
    rho='0'+'1'*a+('0'+'1'*(a-1))*b
    return I,rho


def main():
    C=Counter();rng=random.Random(2026091519)
    # Pure combinatorics, checked against literal border enumeration and first
    # repeated-substring positions. Does not rely on terminality.
    for w in words('01',14):
        pi=prefix_function(w);d,ms=ranks_and_milestones(w)
        for i in range(len(w)+1):
            assert border_chain(pi,i)==literal_borders(w[:i])
            C['literal_border_chains']+=1
        for h,n in enumerate(ms):
            if h==0:assert n==1
            else:
                m=ms[h-1]
                assert pi[n]==m
                assert w.find(w[:m],1)+m==n
            C['milestone_identities']+=1
        if ms:assert w.find(w[:ms[-1]],1)==-1
        C['binary_rank_words']+=1
    # All two-active-state binary tables, randomized annotations, plus larger
    # generated terminal automata. Compare the full reversed check with both
    # original predicates; inspect EVERY safe partial terminal-reaching path.
    instances=[]
    for row in product(range(-1,3),repeat=4):
        D=(row[:2],row[2:],(-1,-1))
        instances.append(Instance(D,frozenset({2}),frozenset((p,q) for p in range(3)
            for q in range(3) if rng.random()<.12),frozenset(q for q in range(3) if rng.random()<.03),rng.randrange(3)))
    for _ in range(140):
        k=rng.randrange(4,9)
        D=tuple(tuple(rng.randrange(-1,k) for a in '01') for q in range(k-1))+((-1,-1),)
        instances.append(Instance(D,frozenset({k-1}),frozenset((p,q) for p in range(k)
            for q in range(k) if rng.random()<.09),frozenset(q for q in range(k) if rng.random()<.03),rng.randrange(k)))
    refs=[]
    for I in instances:
        for w in words('01',8):
            run=I.run(w)
            expected=witness(I,w)
            assert expected==border_witness(I,w)
            if run is not None and run[-1] in I.final:
                rho=w[::-1];labels=run[::-1]
                assert expected==valid_reverse_prefix(I,rho,labels)
                pi=prefix_function(rho);d,ms=ranks_and_milestones(rho)
                assert max(d)<=len(I.delta)-1
                for i in range(len(rho)+1):
                    cs=[labels[j] for j in border_chain(pi,i)]
                    assert len(cs)==len(set(cs))
                if expected:
                    for n in ms:
                        R=Reference(rho[:n],labels[:n+1])
                        if len(refs)<180 and len(R.word)<=8:refs.append((I,R))
                C['terminal_rank_checks']+=1
            C['word_predicate_comparisons']+=1
    for I in (example_endpoint(),example_rich(),example_rich(True)):
        for b in range(1,5):
            w=('0'+'1'*b+'0') if I==example_endpoint() else ('1'+'0'*(2*b)+'1')
            q=2 if I==example_endpoint() else 4
            run=I.run(w) if q==I.start else None
            # Build the run from the named state, leaving the original start.
            L=[q]
            for a in w:
                p=I.delta[L[-1]][int(a)]
                assert p>=0;L.append(p)
            R=Reference(w[::-1],tuple(L[::-1]));assert valid_reverse_prefix(I,R.word,R.labels)
            refs.append((I,R))
    for I,R in refs:
        C['layer_equivalence_product_states']+=equivalent_layer_languages(I,R)
        C['complete_layer_equivalences']+=1
    # Exact all-length languages in the note; complete literal enumeration here.
    E=example_endpoint();J=example_rich();K=example_rich(True)
    for w in words('01',16):
        for I,equality in ((J,False),(K,True)):
            a=0
            while a<len(w) and w[a]=='0':a+=1
            z=w[a+1:-1] if a<len(w) and w[a]=='1' and w.endswith('1') else None
            candidate=a>=1 and z is not None and len(z)>=2 and len(z)%2==0 and set(z)<=set('0')
            assert I.admissible(w)==candidate,(I,w,a,z)
            good=candidate and ((a==len(z)) if equality else (a%2==0 and a<len(z)))
            assert witness(I,w)==border_witness(I,w)==good,(I,w,good)
            C['exact_family_word_checks']+=1
    # Full signatures agree, but exact continuation languages do not.
    rows=[];previous_signature=None
    for b in range(1,25):
        raw='1'+'0'*(2*b)+'1';labels=[4]
        for a in raw:labels.append(J.delta[labels[-1]][int(a)])
        B=Reference(raw,tuple(reversed(labels))) # palindrome base
        s=profile_signature(J,B)
        if previous_signature is not None:assert s==previous_signature
        previous_signature=s
        for a in range(1,2*b+5):
            w='0'*a+raw
            assert witness(J,w)==(a%2==0 and a<2*b)
            assert witness(K,w)==(a==2*b)
            C['parameterized_continuations']+=2
        if b<=4:rows.append(dict(b=b,reference=B.word,labels=B.labels,signature=s))
    endpoint=shortest_endpoint_heuristic(E)
    assert endpoint['status']=='EXHAUSTED_HEURISTIC' and witness(E,'0010')
    assert enriched_heuristic(E,'action')['status']=='FOUND_WITNESS'
    full=enriched_heuristic(J,'rich')
    assert full['status']=='EXHAUSTED_HEURISTIC' and witness(J,'00100001')
    assert all(not witness(J,w) for w in words('01',7))
    assert bounded_witness(J,8)['word']=='00100001'
    C['false_negative_regressions']=2
    assert enriched_heuristic(E,'rich',max_states=1)['status']=='UNKNOWN'
    C['intentional_caps']=1
    # Bounded failure depth does not imply bounded structural width.
    for a in range(2,18,2):
        for b in range(1,10):
            I,rho=comb_family(a,b);w=rho[::-1]
            assert witness(I,w) and border_witness(I,w)
            pi=prefix_function(rho);d,ms=ranks_and_milestones(rho)
            assert max(d)==2
            masters=set(range(1,a+1))
            blocks=[]
            for j in range(b):
                nodes=list(range(a+2+j*a,a+2+(j+1)*a))
                assert len(nodes)==a
                assert {pi[v] for v in nodes}==masters
                assert all(nodes[i+1]==nodes[i]+1 for i in range(a-1))
                blocks.append(nodes)
            assert not masters.intersection(set(sum(blocks,[])))
            assert len(set(sum(blocks,[])))==a*b
            C['complete_bipartite_minor_certificates']+=1
    I,_=comb_family(2,1)
    assert not witness(I,'1110110') and witness(I,'110')
    C['live_flag_width_fixture']=1
    blob=lambda p:hashlib.sha1(b'blob '+str(p.stat().st_size).encode()+b'\0'+p.read_bytes()).hexdigest()
    return dict(status='PASS',seed=2026091519,base='47adf83c194aa941b525240f6470f3d77a69f81d',
                counts=dict(C),endpoint_counterexample=dict(delta=E.delta,flags=sorted(E.flags),word='0010',result=endpoint),
                rich_counterexample=dict(delta=J.delta,flags=sorted(J.flags),word='00100001',result=full,reference_rows=rows),
                border_lab_blob=blob(ROOT/'experiments/border_lab.py'),
                scope='Exact unrestricted finite-depth representation and fixed-reference languages; tested representative quotients REFUTED. No unrestricted decision.',
                proof_status='Written proofs and finite implementation checks; no independent mathematical review or Lean')

if __name__=='__main__':
    if not __debug__:raise SystemExit('Assertions must be enabled')
    out=main();text=json.dumps(out,indent=2)+'\n'
    (ROOT/'results/prefix-rank-layers.json').write_text(text)
    print(text)
