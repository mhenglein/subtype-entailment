"""Verify the two recovered research bundles; optionally replay their tests.

Sources and proofs are retained byte-for-byte. The two large result JSON files
are stored compactly; canonical pretty-printing recovers their original blobs.
This integrity check is not mathematical proof review or Lean verification.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BLOBS = {
    'experiments/border_lab.py': '1144ae52379e0417772e79582269cacd91c5bc17',
    'experiments/calculus_limits.py': 'a434c11cc586fdb27bc481326f6d26e4a789d49a',
    'experiments/check_collective_research.py': '4fa7b64f601bb0fc4ff6e50bcef07179ad358f7f',
    'experiments/check_flag_transport.py': '660343c9f3fc7010834e3e671bf3fde54650b57b',
    'experiments/check_lastflag_spectrum.py': '58683534f5f2611449f5c9898d6f8093ee3eef12',
    'experiments/collective_transport.py': 'd16c5792c1758fc9763acb2cffaff68be9c5c235',
    'experiments/flag_transport.py': '983c340d579c13fb29662fb5288eefd063e7a9ea',
    'experiments/gap_equivalence.py': '6ffa7ab9f744afefc06a5979440fbc8203c2596f',
    'experiments/lastflag_spectrum.py': 'cc2eecf4b50176dc1e128cd0238943c636fd9dd9',
    'experiments/power_transport.py': '18328969cdfc4b9fdad90348a061e86babceecb1',
    'experiments/run_experiments.py': 'a2ea20afe716774ab34be4b19025f5ad7c6fa037',
    'experiments/search_calculus.py': '803bc6fc9c436680c531ac64ac1a13d99641871e',
    'experiments/separator_tail.py': 'a68d8b09d3e4ba49352319bc96cddd47c6d1c86a',
    'notes/2026-09-08-collective-and-cross-gap-transport.md': 'a3ab2facbfcf8dd524bec97e10193bb008d06607',
    'notes/2026-09-08-flag-transport-and-separator-obstruction.md': '595be8357ab13cda1ae3fb8ff11fa21bbf88ca05',
    'research/COLLECTIVE_GAP_INFERENCE.md': '64b01df2634208e0d1a1f68904b26480d3fac5d0',
    'research/FLAG_TRANSPORT.md': '20d9416eb39bc9f5d4f4fc4e7b3be1ee43551842',
}
RESULTS = {
    'results/flag-transport.json': '7322020482b193eaa1259b01917e6f4c2b2170fc',
    'results/collective-gap-research.json': '56ac73257de00c02ee8457b29111428754769adf',
}


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def verify():
    for path, expected in BLOBS.items():
        if blob((ROOT / path).read_bytes()) != expected:
            raise ValueError('Recovered source/proof differs: ' + path)
    for path, expected in RESULTS.items():
        value = json.loads((ROOT / path).read_text(encoding='utf-8'))
        canonical = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
        if blob(canonical) != expected:
            raise ValueError('Recovered evidence differs: ' + path)
    return {'source_and_proof_files': len(BLOBS), 'canonical_result_files': len(RESULTS)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', action='store_true')
    args = parser.parse_args()
    counts = verify()
    if args.replay:
        for name in ('check_flag_transport.py', 'check_collective_research.py',
                     'run_experiments.py', 'check_lastflag_spectrum.py'):
            subprocess.run([sys.executable, str(ROOT / 'experiments' / name)],
                           cwd=ROOT, check=True)
        counts = verify()
        # Restore the compact, deterministic repository serialization.
        for path in RESULTS:
            target = ROOT / path
            value = json.loads(target.read_text(encoding='utf-8'))
            target.write_text(json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n',
                              encoding='utf-8')
    print(json.dumps(dict(status='PASS', replay=args.replay, **counts), sort_keys=True))


if __name__ == '__main__':
    main()
