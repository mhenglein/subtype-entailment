#!/usr/bin/env python3
"""E054: matched capped native rerun of E052 using the gated C081 wrapper."""
from collections import Counter
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

import check_entailment_decision as reference
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from subtail import run_process


def source(fixture, lazy):
    text = reference.lean_source(fixture)
    if lazy:
        text = text.replace('import Subtail.EntailmentDecision', 'import Subtail.TerminalDecisionLazy')
        for name in ('rawNormalizedEntailsCheck', 'normalizedEntailsCheck', 'entailsCheck'):
            text = text.replace('Subtail.EntailmentDecision.' + name,
                                'Subtail.TerminalDecisionLazy.' + name + 'Lazy')
    return text


def evaluate(fixture, lazy, scratch, timeout):
    label = 'lazy' if lazy else 'original'
    path = (scratch / (fixture.name + '-' + label + '.lean')).resolve()
    path.write_text(source(fixture, lazy))
    result = run_process(['lake', 'env', 'lean', str(path)], ROOT / 'lean', timeout)
    output = result.pop('output', '')
    if result['status'] == 'PASS':
        markers = [line.strip() for line in output.splitlines() if line.startswith(reference.RESULT_MARKER)]
        if len(markers) != 1 or markers[0] not in (reference.RESULT_MARKER+'true', reference.RESULT_MARKER+'false'):
            result.update(status='FAIL', reason='missing_or_ambiguous_marker', output=output[-2000:])
        else:
            actual = markers[0].endswith('true')
            result['actual'] = actual
            if actual != fixture.expected:
                result.update(status='FAIL', reason='independent_expected_answer_mismatch')
    elif result.get('returncode', 0) > 0 and not any(
            s in output.lower() for s in ('memory', 'heartbeat', 'stack overflow', 'interrupted', 'resource')):
        result.update(status='FAIL', reason='unexpected_compile_or_process_error', output=output[-2000:])
    else:
        result['output_tail'] = output[-1000:]
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout',type=float,default=20.0)
    parser.add_argument('--compare-baseline',action='store_true',help='Rerun unchanged original under identical caps')
    parser.add_argument('--output',type=Path,default=ROOT/'tmp/entailment-lazy.json')
    parser.add_argument('--scratch',type=Path,default=ROOT/'tmp/entailment-lazy')
    args=parser.parse_args()
    if args.timeout<=0:parser.error('timeout must be positive')
    args.scratch.mkdir(parents=True,exist_ok=True)
    fixtures=reference.corpus();reference.validate_corpus(fixtures)
    rows=[]
    for fixture in fixtures:
        row={'name':fixture.name,'kind':fixture.kind,'expected':fixture.expected,
             'justification':fixture.justification}
        if args.compare_baseline:row['original']=evaluate(fixture,False,args.scratch,args.timeout)
        row['lazy']=evaluate(fixture,True,args.scratch,args.timeout)
        rows.append(row)
        print(f"{fixture.name}: lazy {row['lazy']['status']}" +
              (f"; original {row['original']['status']}" if 'original' in row else ''),flush=True)
    counts={name:dict(Counter(row[name]['status'] for row in rows))
            for name in (['original','lazy'] if args.compare_baseline else ['lazy'])}
    result={'checked_revision':reference.git_revision(),'status':'FAIL' if any(
        'FAIL' in c for c in counts.values()) else 'UNKNOWN' if any('UNKNOWN' in c for c in counts.values()) else 'PASS',
        'semantics':'All reported completed answers equal the independent E052 expectations; timeouts are UNKNOWN.',
        'host':platform.node(),'platform':platform.platform(),'python':platform.python_version(),
        'caps':{'wall_seconds_per_fixture':args.timeout,'cpu_seconds_per_fixture':args.timeout,
                'address_space_GiB_linux':16,'lean_threads':1,'lean_stack_KiB':32768},
        'counts':counts,'cases':rows,'source_sha256':{
          str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted((ROOT/'lean/Subtail').glob('*.lean'))}}
    for name in ['scripts/subtail.py','experiments/check_entailment_lazy.py','experiments/check_entailment_decision.py']:
        result['source_sha256'][name]=hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(counts,sort_keys=True),flush=True)
    # This diagnostic deliberately permits UNKNOWN; CI fails on actual disagreement/errors.
    return 1 if result['status']=='FAIL' else 0


if __name__=='__main__':raise SystemExit(main())
