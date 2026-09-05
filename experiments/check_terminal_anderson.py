import itertools,json,random
from pathlib import Path
from border_lab import Instance,witness,words
from terminal_anderson import source_border_certificate,prune_impossible_sources,hybrid_terminal_decision
from terminal_overlap import bounded_overlap_decision

PAIRS=((0,1),(0,2),(1,2),(2,1))

def census_unknowns():
    rows=dict(unknown=0,oracle_yes=0,oracle_no=0,start_impossible=0,
              start_impossible_oracle_no=0,false_impossible=0)
    examples=[]
    oracle_words=list(words('01',4))
    for tr in itertools.product((-1,1,2,3),repeat=6):
        delta=tuple(tuple(tr[2*p:2*p+2]) for p in range(3))+((-1,-1),)
        for mask in range(16):
            I=Instance(delta,frozenset({3}),frozenset(p for i,p in enumerate(PAIRS) if mask>>i&1))
            if bounded_overlap_decision(I)['status']!='UNKNOWN': continue
            rows['unknown']+=1
            oracle=any(witness(I,w) for w in oracle_words)
            rows['oracle_yes' if oracle else 'oracle_no']+=1
            cert=source_border_certificate(I,0,max_states=1000000)
            if cert['status']=='IMPOSSIBLE':
                rows['start_impossible']+=1
                if not oracle: rows['start_impossible_oracle_no']+=1
                else:
                    rows['false_impossible']+=1
                    if len(examples)<3: examples.append((I,cert))
    assert rows['false_impossible']==0
    return rows

def hybrid_census():
    counts=dict(overlap_unknown=0,YES=0,NO=0,UNKNOWN=0,false=0)
    oracle_words=list(words('01',4))
    for tr in itertools.product((-1,1,2,3),repeat=6):
        delta=tuple(tuple(tr[2*p:2*p+2]) for p in range(3))+((-1,-1),)
        for mask in range(16):
            I=Instance(delta,frozenset({3}),frozenset(p for i,p in enumerate(PAIRS) if mask>>i&1))
            if bounded_overlap_decision(I)['status']!='UNKNOWN':
                continue
            counts['overlap_unknown']+=1
            out=hybrid_terminal_decision(I,max_source_nodes=1000000,max_overlap_states=200000)
            counts[out['status']]+=1
            oracle=any(witness(I,w) for w in oracle_words)
            if out['status']!='UNKNOWN' and ((out['status']=='YES')!=oracle):
                counts['false']+=1;raise AssertionError(('hybrid mismatch',I,out,oracle))
    return counts

def random_soundness():
    rng=random.Random(202609051222)
    counts=dict(instances=0,certificates=0,impossible=0,possible=0,not_applicable=0,unknown=0,
                brute_words=0,false_impossible=0,pruned_starts=0)
    for _ in range(700):
        k=rng.randrange(2,8)
        finals=frozenset(p for p in range(k) if rng.random()<.22)
        delta=tuple((-1,-1) if p in finals else tuple(rng.randrange(-1,k) for _ in range(2)) for p in range(k))
        flags=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.12)
        bad=frozenset(p for p in range(k) if rng.random()<.03)
        I=Instance(delta,finals,flags,bad,rng.randrange(k))
        counts['instances']+=1
        cert=source_border_certificate(I,I.start,max_states=100000)
        counts['certificates']+=1; counts[cert['status'].lower()]+=1
        # Brute soundness only: a proved-impossible start must have no short witness.
        if cert['status']=='IMPOSSIBLE':
            for w in words('01',8):
                counts['brute_words']+=1
                if witness(I,w):
                    counts['false_impossible']+=1
                    raise AssertionError(('false impossible',I,cert,w))
        p,current=prune_impossible_sources(I,max_states=80000)
        if p['status']=='START_IMPOSSIBLE':
            counts['pruned_starts']+=1
            for w in words('01',7):
                counts['brute_words']+=1
                assert not witness(I,w)
    return counts

def fixtures():
    # One cyclic residual NO case from E025: ordinary last-flag criterion is UNKNOWN.
    I=Instance(((-1,1),(1,2),(2,3),(-1,-1)),frozenset({3}),frozenset({(0,1),(0,2)}))
    assert bounded_overlap_decision(I)['status']=='UNKNOWN'
    c=source_border_certificate(I,0)
    assert c['status']=='IMPOSSIBLE'
    # Positive variant: only one target flagged; forward closure fails, so no false NO.
    J=Instance(I.delta,I.final,frozenset({(0,1)}))
    c2=source_border_certificate(J,0)
    assert c2['status']=='NOT_APPLICABLE'
    assert witness(J,'1011')
    return dict(no_fixture=c,positive_guard=c2)

def main():
    out=dict(status='PASS',fixture=fixtures(),four_state_unknowns=census_unknowns(),hybrid_four_state=hybrid_census(),random=random_soundness(),
             theorem='Forward-closed source-border 6n+1 adaptation; written proof, not Lean checked',
             scope='Sound impossibility/pruning certificate; exact for source-only instances when applicable')
    p=Path(__file__).resolve().parents[1]/'results'/'terminal-anderson.json'
    p.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
