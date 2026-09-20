#!/usr/bin/env python3
"""Audit the selective Lean boundary and exercise the ordinary finite solver.

This does not turn Python graph classification or normalization into a Lean
proof. Every declaration's actual hypotheses remain part of the audit record.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess

from check_regular_certificate import DECL, command
import subtail

ROOT=Path(__file__).resolve().parents[1]
MODULE=ROOT/'lean/Subtail/FiniteTreeReduction.lean'


def audit(directory):
    source=MODULE.read_text()
    if re.search(r'\b(sorry|sorryAx|native_decide|implemented_by)\b|^\s*(axiom|opaque|noncomputable|private|unsafe)\s',source,re.M):
        raise RuntimeError('Unexpected incomplete, hidden or trusted declaration')
    expected={'Subtail.FiniteTreeReduction.'+name:kind for kind,name in DECL.findall(source)}
    required={'FiniteTree','BoundedReversePop','Hot','Reachable','ClosureBounded','ReachesHot',
              'closureBounded_iff_noHot','canonicalFinite_iff_noHot',
              'forced_reverse_pop_loop_noFiniteModel',
              'finiteEntails_iff_entails_of_uniform_reverse_pop','normalize_finite_entails_iff'}
    if not {'Subtail.FiniteTreeReduction.'+name for name in required} <= expected.keys():
        raise RuntimeError('Missing required closure declarations')
    file=directory/'Axioms.lean'
    file.write_text('import Subtail.FiniteTreeReduction\n'+
        ''.join('#print axioms '+name+'\n' for name in expected))
    output=command(['lake','env','lean',str(file)])
    rows=re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^]]*)\])",output)
    if len(rows)!=len(expected) or {name for name,_,_ in rows}!=expected.keys():
        raise RuntimeError('Incomplete declaration dependency report: '+output)
    reports={}
    for name,_,raw in rows:
        used={a.strip() for a in raw.split(',') if a.strip()}
        allowed={'propext','Quot.sound'} | ({'Classical.choice'} if expected[name]=='theorem' else set())
        if not used <= allowed:
            raise RuntimeError('Unexpected declaration dependencies: '+name+' '+repr(used))
        reports[name]={'kind':expected[name],'axioms':sorted(used)}
    return reports


def cli_cases():
    cases=[]
    def check(name,path,flags,expected,finite_height=None,verified=False):
        args=['python3','scripts/subtail.py',path,'--timeout','40',*flags]
        run=subprocess.run(args,cwd=ROOT,capture_output=True,text=True,timeout=50)
        result=json.loads(run.stdout)
        expected_exit=0 if expected in ('ENTAILED','NOT_ENTAILED') else 2 if expected=='UNKNOWN' else 1
        if result['status']!=expected or run.returncode!=expected_exit:
            raise RuntimeError(name+': '+run.stdout+run.stderr)
        if finite_height is not None and result.get('countermodel',{}).get('finite_height')!=finite_height:
            raise RuntimeError('Missing finite countermodel height: '+name)
        if verified and result.get('certificate_verification',{}).get('status')!='VERIFIED':
            raise RuntimeError('Missing actual kernel certificate proof: '+name)
        if name == 'contradiction' and result.get('growth_analysis',{}).get('finite_model_obstruction') is not False:
            raise RuntimeError('Contradiction fixture must exercise the no-growth arbitrary-unsatisfiable branch')
        cases.append({'name':name,'command':args,'status':'PASS','result':result})
    for name,expected,height in (('forced-infinite','ENTAILED',None),('contradiction','ENTAILED',None),
                                 ('reverse','NOT_ENTAILED',1),('ground','NOT_ENTAILED',0)):
        check(name,'examples/finite-trees/'+name+'.json',['--finite-trees','--verify-certificate'],
              expected,height,verified=height is not None)
    check('same-input-arbitrary','examples/finite-trees/forced-infinite.json',
          ['--verify-certificate'],'NOT_ENTAILED',verified=True)
    check('reject-infinite-model','examples/finite-trees/forced-infinite.json',
          ['--finite-trees','--check-model','examples/entailment/zero-spine-model.json'],'INVALID_MODEL')
    check('capped-growth','examples/finite-trees/ground.json',
          ['--finite-trees','--timeout','0.000001'],'UNKNOWN')
    return cases


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'tmp/finite-trees.json')
    args=parser.parse_args()
    target=args.output.resolve()
    target.parent.mkdir(parents=True,exist_ok=True)
    scratch=target.parent/(target.stem+'-scratch')
    scratch.mkdir(exist_ok=True)
    version=command(['lean','--version']).strip()
    if 'version 4.33.1,' not in version:
        raise RuntimeError('Use pinned Lean 4.33.1: '+version)
    command(['lake','build','+Subtail.FiniteTreeReduction','+Subtail.EntailmentFast','+Subtail.RegularTreeCertificate'])
    command(['lake','env','leanchecker','Subtail.FiniteTreeReduction'])
    declarations=audit(scratch)
    tests={}
    for pattern in ('test_finite_trees.py','test_subtail.py','test_regular_countermodel.py'):
        run=subprocess.run(['python3','-m','unittest','discover','-s','scripts','-p',pattern],
                           cwd=ROOT,capture_output=True,text=True,timeout=30)
        if run.returncode:
            raise RuntimeError(run.stdout+run.stderr)
        count=re.search(r'Ran (\d+) tests?',run.stderr)
        if count is None:
            raise RuntimeError('Missing test count')
        tests[pattern]={'status':'PASS','tests':int(count[1])}
    # The independent experiment has no Lean dependency.
    import sys
    sys.path.insert(0,str(ROOT))
    from experiments.check_finite_trees import run as experiment
    experiments=experiment()
    cases=cli_cases()
    paths=[MODULE,Path(__file__),ROOT/'scripts/check_regular_certificate.py',
           ROOT/'scripts/finite_trees.py',ROOT/'scripts/subtail.py',
           ROOT/'scripts/regular_countermodel.py',ROOT/'scripts/test_finite_trees.py',
           ROOT/'experiments/check_finite_trees.py',ROOT/'experiments/check_stack_summary.py']
    result={'status':'PASS','revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
            'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
            'host':platform.node(),'platform':platform.platform(),'toolchain':version,
            'build':'PASS','kernel_replay':'PASS','declarations':declarations,
            'python_tests':tests,'experiment':experiments,'cli_cases':cases,
            'trust':'Selective closure/semantic lemmas are Lean-checked. The complete finite-tree classifier, Python normalization and graph finiteness remain ordinary mathematics/Python.'}
    target.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(f'PASS: build/kernel, {len(declarations)} declaration closures, {len(cases)} actual CLI cases')


if __name__=='__main__':
    main()
