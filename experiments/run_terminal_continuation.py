"""Run the September 5 terminal research checks.

Core checks use only Python's standard library. Pass --with-smt to additionally
run arithmetic tests using an installed Z3 shared library (tested: 4.13.3.0).
"""
import argparse
from pathlib import Path
import subprocess
import sys


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--with-smt',action='store_true')
    args=parser.parse_args()
    directory=Path(__file__).resolve().parent
    names=['check_terminal_realization.py','check_terminal_nonregular.py',
           'check_four_state_terminal.py']
    if args.with_smt:names.append('check_terminal_arithmetic.py')
    for name in names:subprocess.run([sys.executable,str(directory/name)],check=True)

if __name__=='__main__':main()
