"""Run the full regular-family regression and write deterministic evidence.

The underlying checker records runtime diagnostics while it runs. This wrapper
normalizes the committed scientific artifact so repeated CI runs are byte-stable.
"""
import json
from pathlib import Path

from check_regular_family_orbits import run

ROOT = Path(__file__).resolve().parents[1]


def check():
    raw = run()
    counts = raw['counts']
    result = {
        'seed': raw['seed'],
        'base': 'consolidated-2026-09-08',
        'status': raw['status'],
        'counts': counts,
        'outcomes': raw['outcomes'],
        'examples': raw['examples'],
        'reduction_summary': {
            'instances': counts['complete_reduction_instances'],
            'complete_candidate_words': counts['reduction_complete_candidate_words'],
            'raw_word_checks': counts['reduction_raw_word_checks'],
        },
        'limits': raw['limits'],
    }
    path = ROOT / 'results' / 'regular-family-orbits.json'
    text = json.dumps(result, indent=2) + '\n'
    path.write_text(text)
    print(text, end='')
    return result


if __name__ == '__main__':
    check()
