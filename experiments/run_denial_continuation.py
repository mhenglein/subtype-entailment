"""Replay the new denial-aware checks using only Python's standard library."""
from pathlib import Path
import subprocess
import sys

if __name__ == '__main__':
    directory=Path(__file__).resolve().parent
    for name in ('check_unrestricted_continuation.py','check_infinite_extensions.py'):
        subprocess.run([sys.executable,str(directory/name)],check=True,cwd=directory.parent)
    print('Denial-aware checks passed. Written proofs are not Lean-checked.')
