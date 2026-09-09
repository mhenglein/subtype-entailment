"""Idempotent additive record integration; no Git operations or status promotion."""
import argparse
import json
from pathlib import Path

TAG='guarded-order-route-2026-09-09'
NOTE='notes/2026-09-09-guarded-order-and-terminal-anchor.md'
EVIDENCE=[NOTE,'research/ORDER_COVER_ROUTE.md','experiments/guarded_order_chains.py',
          'experiments/check_guarded_order_chains.py','results/guarded-order-chains.json',
          'experiments/trailing_copy_barrier.py','experiments/check_trailing_copy_barrier.py',
          'results/trailing-copy-barrier.json']


def integrate(root):
    for name in EVIDENCE:
        if not (root/name).is_file():raise ValueError('Missing evidence: '+name)
    writes={};path=root/'STATE.md';text=path.read_text()
    if TAG not in text:
        heading,rest=text.split('\n',1)
        writes[path]=heading+'\n\n## September 9: complete guarded-order chains; terminal anchoring remains open\n\n<!-- '+TAG+' -->\n'+(
            'The earlier finite three-stage census now has a uniform proof-producing '
            'decision for any supplied number of phase-blind unary stages, each '
            'with a positive lower bound and one congruence. Equality-guarded '
            'inequalities saturate finitely; strongly connected components force '
            'equal counts, and compatible arithmetic progressions supply distinct '
            'values for the remaining components. The solver returns compact '
            'witness vectors or independently replayable NO proofs. This is a '
            'complete restricted class, not a cover of arbitrary recurrent inputs.\n\n'
            'An opposing two-counter reduction is explicit for a nearby two-copy '
            'pattern-containment problem with arbitrary trailing context. It does '
            'NOT remove that context under terminal suffix-comparison semantics. '
            'The constructive coverage and opposing terminal-anchor implications '
            'remain open. [Proof, scope, evidence]('+NOTE+'); '
            '[end-to-end outline](research/ORDER_COVER_ROUTE.md). '
            'Written proofs with executed checks; independent review pending, '
            'not Lean-checked. Earlier work remains below unchanged.\n\n')+rest
    for aid in ('A011','A012','A016','A017'):
        path=root/'research'/'approaches'/(aid+'.md');text=path.read_text()
        if TAG not in text:
            writes[path]=text.rstrip()+'\n\n### 2026-09-09 — Guarded-order completeness and the terminal-anchor gap\n\n<!-- '+TAG+' -->\n'+(
                'Author: ChatGPT. Base `05b20ee73841d0e7105a44beb761e553a7081a8d`. '
                'The restricted modular phase-blind serial class now has a '
                'complete order/domain saturation proof for arbitrary supplied '
                'stage count, not only a finite census. The opposing attempt '
                'gives an explicit two-counter error reduction for patterns '
                'allowing trailing context; no transfer to original terminal '
                'comparisons is claimed. [End-to-end outline](../ORDER_COVER_ROUTE.md) '
                'names both remaining implications; '
                '[proof and exact evidence](../../'+NOTE+') records all limits.\n\n'
                'Commands: `python3 experiments/check_guarded_order_chains.py` '
                'and `python3 experiments/check_trailing_copy_barrier.py`. '
                'The unchanged core result is byte-identical. New theorem status '
                'is written proof plus independent-algorithm checks, pending '
                'mathematical review; no new Lean result or unrestricted '
                'decision. No worker ownership or existing status is changed.\n')
    path=root/'experiments'/'README.md';text=path.read_text()
    if TAG not in text:
        writes[path]=text.rstrip()+'\n\n## Guarded-order chains and trailing-copy boundary\n\n<!-- '+TAG+' -->\n'+(
            'Run `python3 experiments/check_guarded_order_chains.py` and '
            '`python3 experiments/check_trailing_copy_barrier.py`. '
            '[Proof and complete scopes](../'+NOTE+') and '
            '[route outline](../research/ORDER_COVER_ROUTE.md) distinguish '
            'the complete restricted backend from both unproved end-to-end '
            'transfers. Results: [guarded order](../results/guarded-order-chains.json) '
            'and [trailing copy](../results/trailing-copy-barrier.json). '
            'No new global IDs are allocated.\n')
    path=root/'research'/'approaches.json';data=json.loads(path.read_text());changed=False
    rows={row['id']:row for row in data['approaches']}
    for aid in ('A011','A012','A016','A017'):
        if aid not in rows:raise ValueError('Missing approach '+aid)
        for name in EVIDENCE:
            if name not in rows[aid]['evidence']:
                rows[aid]['evidence'].append(name);changed=True
    if changed:writes[path]=json.dumps(data,indent=2,ensure_ascii=False)+'\n'
    for path,text in writes.items():path.write_text(text,encoding='utf-8')
    return [str(p.relative_to(root)) for p in writes]


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
    args=parser.parse_args()
    print(json.dumps({'updated':integrate(args.root.resolve())},sort_keys=True))
