#!/usr/bin/env python3
"""Independent fixed-reference finishing oracle and native Lean differential.

No Python candidate/compiler imported. The oracle tracks ALL matching proper
prefixes as a set, rather than a longest-prefix/KMP cursor. Its finite graph is
exhausted, so NO here is exact for the supplied fixed-reference no-return
question, NOT for arbitrary witness existence. Python 3.10+, standard library.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import dataclass
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SEED = 2026091830

@dataclass(frozen=True)
class Instance:
    delta: tuple[tuple[int,int], ...]
    initial: int
    finals: frozenset[int]
    bad: frozenset[int] = frozenset()
    flags: frozenset[tuple[int,int]] = frozenset()

@dataclass(frozen=True)
class Reference:
    word: str
    labels: tuple[int,...]


def safe_reference(I: Instance, B: Reference) -> bool:
    if not B.word or len(B.labels) != len(B.word)+1 or B.labels[0] not in I.finals:
        return False
    if any(q in I.bad for q in B.labels): return False
    if any(I.delta[B.labels[j+1]][int(a)] != B.labels[j] for j,a in enumerate(B.word)):
        return False
    for j in range(len(B.word)+1):
        pref=B.word[:j]
        for h in range(j+1):
            if pref.endswith(B.word[:h]) and (B.labels[j], B.labels[h]) in I.flags:
                return False
    return True


def literal_witness(I: Instance, w: str) -> bool:
    q=I.initial; run=[q]
    for a in w:
        q=I.delta[q][int(a)]
        if q < 0:return False
        run.append(q)
    if q not in I.finals or any(p in I.bad for p in run):return False
    return not any((p,run[j]) in I.flags and w.startswith(w[j:],i)
                   for i,p in enumerate(run) for j in range(i,len(run)))


def no_return_oracle(I: Instance, B: Reference) -> dict:
    """Exhaust the finite set-of-matches x original-state graph, without caps."""
    m=len(B.word)
    if m==0: return dict(status='NO',states=0,extension=None)
    matches=tuple(h for h in range(m) if B.word.endswith(B.word[:h]))
    root=(matches,B.labels[-1]); todo=deque([root]); prior={root:None}
    while todo:
        current=todo.popleft(); matches,q=current
        if q==I.initial:
            ext=[]; node=current
            while prior[node] is not None:
                node,a=prior[node];ext.append(a)
            ext=''.join(reversed(ext))
            assert all(not (B.word+ext)[:j].endswith(B.word)
                       for j in range(m+1,m+len(ext)+1))
            if safe_reference(I,B):assert literal_witness(I,(B.word+ext)[::-1])
            return dict(status='YES',states=len(prior),extension=ext)
        for a in '01':
            nxt=tuple(sorted({0}|{h+1 for h in matches if B.word[h]==a}))
            if m in nxt: continue
            for p,row in enumerate(I.delta):
                if row[int(a)]!=q or p in I.bad or (p,p) in I.flags:continue
                if any((p,B.labels[h]) in I.flags for h in nxt):continue
                target=(nxt,p)
                if target not in prior:
                    prior[target]=(current,a);todo.append(target)
    return dict(status='NO',states=len(prior),extension=None)


def references(I: Instance, max_length: int):
    todo=[Reference('',(f,)) for f in sorted(I.finals)]
    out=[]
    while todo:
        B=todo.pop()
        if B.word and safe_reference(I,B):out.append(B)
        if len(B.word)==max_length:continue
        q=B.labels[-1]
        for a in '01':
            for p,row in enumerate(I.delta):
                if row[int(a)]==q:
                    C=Reference(B.word+a,B.labels+(p,))
                    if safe_reference(I,C):todo.append(C)
    return out


def corpus():
    rng=random.Random(SEED); cases=[]
    chain=Instance(((1,-1),(-1,2),(3,-1),(-1,-1)),0,frozenset({3}))
    # This one needs another promotion: accepted completion exists, Finish is NO.
    cases.append(('requires_another_return',chain,Reference('0',(3,2))))
    cases.append(('already_finished',chain,Reference('010',(3,2,1,0))))
    nonret=Instance(((1,-1),(-1,2),(-1,-1)),0,frozenset({2}))
    cases.append(('one_bit_finish',nonret,Reference('1',(2,1))))
    cases.append(('empty_reference',nonret,Reference('',(2,))))
    loop=Instance(((1,-1),(2,1),(-1,-1)),0,frozenset({2}))
    cases.append(('no_return_impossible',loop,Reference('0',(2,1))))
    toy=Instance(((0,0),),0,frozenset({0}))
    cases.append(('nonterminal_empty_finish',toy,Reference('00',(0,0,0))))
    # The same input graph, with each possible one-flag or Bad annotation.
    for p,q in product(range(3),repeat=2):
        I=Instance(nonret.delta,0,nonret.finals,flags=frozenset({(p,q)}))
        B=Reference('1',(2,1))
        if safe_reference(I,B): cases.append((f'flag_{p}_{q}',I,B))
    for bad in range(3):
        I=Instance(nonret.delta,0,nonret.finals,bad=frozenset({bad}))
        B=Reference('1',(2,1))
        if safe_reference(I,B):cases.append((f'bad_{bad}',I,B))
    for trial in range(700):
        if len(cases)>=180:break
        k=rng.randrange(2,6)
        delta=tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k-1))+((-1,-1),)
        flags=frozenset((p,q) for p,q in product(range(k),repeat=2) if rng.random()<.08)
        bad=frozenset(p for p in range(k-1) if rng.random()<.05)
        I=Instance(delta,0,frozenset({k-1}),bad,flags)
        bs=references(I,5);rng.shuffle(bs)
        for B in bs[:3]:
            cases.append((f'terminal_{trial}_{len(B.word)}_{len(cases)}',I,B))
            if len(cases)>=180:break
    assert len(cases)==180
    assert literal_witness(chain,'010')
    assert no_return_oracle(chain,cases[0][2])['status']=='NO'
    return cases


def lean_bool(b):return 'true' if b else 'false'
def lean_word(w):return '['+', '.join(lean_bool(a=='1') for a in w)+']'
def fin(q,k):return f'(⟨{q}, by decide⟩ : Fin {k})'
def lean_instance(I):
    k=len(I.delta)
    def opt(q):return 'none' if q<0 else 'some '+fin(q,k)
    delta='#v['+', '.join('('+opt(row[0])+', '+opt(row[1])+')' for row in I.delta)+']'
    bad='#v['+', '.join(lean_bool(q in I.bad) for q in range(k))+']'
    finals='#v['+', '.join(lean_bool(q in I.finals) for q in range(k))+']'
    flags='#v['+', '.join('#v['+', '.join(lean_bool((p,q) in I.flags) for q in range(k))+']' for p in range(k))+']'
    return f'{{ initial := {fin(I.initial,k)}, transitions := {delta}, bad := {bad}, final := {finals}, flags := {flags} }}'


def native(cases, answers, timeout):
    lines=['import Subtail.RankQueryFinishTrace','open Subtail Subtail.RankQuery',
           'set_option maxRecDepth 8192','set_option maxHeartbeats 20000000']
    for i,((name,I,B),ans) in enumerate(zip(cases,answers)):
        k=len(I.delta)
        labels='['+', '.join(fin(q,k) for q in B.labels)+']'
        lines += [f'def I{i} : Instance {k} := {lean_instance(I)}',
                  f'def B{i} : Reference {k} := {{ word := {lean_word(B.word)}, label := fun j => ({labels}).getD j {fin(B.labels[0],k)} }}']
    lines.append('def main : IO Unit := do')
    for i,((_,I,B),ans) in enumerate(zip(cases,answers)):
        wi='true'
        if ans['status']=='YES' and safe_reference(I,B):
            w=(B.word+ans['extension'])[::-1]
            wi=f'witnessCheck I{i} {lean_word(w)}'
        lines.append(f'  IO.println ("CHECK {i} " ++ toString (satCheck (prefixGraph I{i} B{i}) (finishQuery I{i})) ++ " " ++ toString ({wi}))')
    with tempfile.TemporaryDirectory(prefix='finishing-native-') as td:
        src=Path(td)/'FinishingNative.lean';src.write_text('\n'.join(lines)+'\n')
        proc=subprocess.run(['lake','env','lean','--run',str(src)],cwd=ROOT/'lean',
                            text=True,capture_output=True,timeout=timeout,check=True)
        rows=[x.split() for x in proc.stdout.splitlines() if x.startswith('CHECK ')]
        assert len(rows)==len(cases),proc.stdout+'\n'+proc.stderr
        for i,row in enumerate(rows):
            assert row==['CHECK',str(i),lean_bool(answers[i]['status']=='YES'),'true'], (i,row,answers[i])
    return len(rows)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',action='store_true')
    ap.add_argument('--timeout',type=int,default=180)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--full-output',type=Path)
    args=ap.parse_args()
    cases=corpus(); answers=[no_return_oracle(I,B) for _,I,B in cases]
    safe=[safe_reference(I,B) for _,I,B in cases]
    counts=Counter(a['status'] for a in answers)
    positive_safe=sum(s and a['status']=='YES' for s,a in zip(safe,answers))
    checked=native(cases,answers,args.timeout) if args.lean else 0
    rows=[]
    for (name,I,B),a in zip(cases,answers):
        rows.append(dict(name=name,k=len(I.delta),delta=I.delta,initial=I.initial,
                         finals=sorted(I.finals),bad=sorted(I.bad),flags=sorted(I.flags),
                         word=B.word,labels=B.labels,oracle=a,safe_reference=safe_reference(I,B)))
    digest=hashlib.sha256(json.dumps(rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    report=dict(status='PASS',seed=SEED,mode='native Lean + independent oracle' if args.lean else 'Python oracle only',
                counts=dict(cases=len(cases),safe_references=sum(safe),oracle_yes=counts['YES'],
                            oracle_no=counts['NO'],positive_witness_reconstructions=positive_safe,
                            native_query_comparisons=checked,native_witness_checks=positive_safe if args.lean else 0,
                            completely_explored_oracle_states=sum(a['states'] for a in answers if a['status']=='NO')),
                corpus_sha256=digest,
                required_return_regression=dict(accepted_word='010',base='0',base_labels=[3,2],finish=False,
                                               accepted_completion_exists=True),
                cases=rows,
                limits=['NO is complete only for this fixed-reference no-return finishing question.',
                        'Finite input corpus does not prove general completeness; Lean theorems do.',
                        'No compiler coverage, global witness bound or subtype decision is established.'])
    compact={k:v for k,v in report.items() if k!='cases'}
    txt=json.dumps(compact,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(txt)
    if args.full_output:
        args.full_output.parent.mkdir(parents=True,exist_ok=True)
        args.full_output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(txt,end='')

if __name__=='__main__':main()
