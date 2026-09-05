"""Exact Presburger encoding of a fixed repeated-word skeleton.

A block is (word, repeat): repeat=False is a literal; repeat=True gives a
fresh nonnegative exponent. Words and DFA are fixed, exponents unbounded.
Optional Z3 supplies computation, never the mathematical completeness proof.
Timeouts, unavailable backends, malformed answers, or witness validation errors
produce UNKNOWN. No result here decides words outside the supplied skeleton.
"""
from dataclasses import dataclass
from pathlib import Path
from math import gcd
import re
import subprocess
import sys
from border_lab import witness, border_witness


def smt_int(n):
    return str(n) if n >= 0 else f'(- {-n})'


def disj(items):
    items = list(items)
    return 'false' if not items else items[0] if len(items) == 1 else '(or ' + ' '.join(items) + ')'


def conj(items):
    items = list(items)
    return 'true' if not items else items[0] if len(items) == 1 else '(and ' + ' '.join(items) + ')'


def choose(choices, default):
    for condition, value in reversed(list(choices)):
        if str(value) != default:
            default = f'(ite {condition} {value} {default})'
    return default


@dataclass(frozen=True)
class Block:
    word: str
    repeat: bool = False


class Skeleton:
    """Construct formulas without any multiplication between variables."""
    def __init__(self, instance, blocks):
        self.I = instance
        self.blocks = tuple(b if isinstance(b, Block) else Block(*b) for b in blocks)
        k = len(instance.delta)
        if not k or not 0 <= instance.start < k:
            raise ValueError('A nonempty, well-formed instance is required')
        if not instance.alphabet or len(set(instance.alphabet)) != len(instance.alphabet):
            raise ValueError('Alphabet letters must be distinct')
        if any(len(row) != len(instance.alphabet) or any(q < -1 or q >= k for q in row)
               for row in instance.delta):
            raise ValueError('Malformed transition table')
        if any(not 0 <= q < k for q in instance.final | instance.bad):
            raise ValueError('Malformed annotations')
        if any(not 0 <= q < k or not 0 <= r < k for q, r in instance.flags):
            raise ValueError('Malformed flag relation')
        if any(b.repeat and not b.word for b in self.blocks):
            raise ValueError('A repeated block must be nonempty')
        if any(set(b.word) - set(instance.alphabet) for b in self.blocks):
            raise ValueError('A block contains letters outside the alphabet')
        self.names = tuple(f'n{i}' for i in range(sum(b.repeat for b in self.blocks)))
        self.definitions = []
        self.segments = []
        self._compile()

    def _define(self, name, args, sort, body):
        self.definitions.append(f'(define-fun {name} ({args}) {sort} {body})')

    def _advance(self, state, word):
        k = len(self.I.delta)
        for a in word:
            state = k if state == k else self.I.delta[state][self.I.alphabet.index(a)]
            if state < 0:
                state = k
        return state

    def _compile(self):
        k = len(self.I.delta)
        offsets = ['0']; starts = [str(self.I.start)]
        entries = []; count_index = 0
        known = self.I.start
        for bidx, block in enumerate(self.blocks):
            u = block.word; length = len(u)
            if block.repeat:
                count = self.names[count_index]; count_index += 1
            else:
                count = '1'
            pos = f'o{bidx}'; end = f'o{bidx + 1}'
            if bidx == 0:
                self._define(pos, '', 'Int', '0')
            self._define(end, '', 'Int', f'(+ {pos} (* {length} {count}))')
            if bidx == 0:
                self._define('q0', '', 'Int', str(self.I.start))
            if not length:
                self._define(f'q{bidx + 1}', '', 'Int', f'q{bidx}')
                continue
            self.segments.append((pos, end, u))
            # The orbit of one state's action under u has at most k+1 nodes.
            transition = [self._advance(q, u) for q in range(k + 1)]
            powers = []
            for q in range(k + 1):
                sequence = []; seen = {}; current = q
                while current not in seen:
                    seen[current] = len(sequence); sequence.append(current)
                    current = transition[current]
                mu = seen[current]; period = len(sequence) - mu
                cases = [(f'(= e {t})', str(r)) for t, r in enumerate(sequence[:mu])]
                cycle = choose([(f'(= (mod (- e {mu}) {period}) {t})', str(r))
                                for t, r in enumerate(sequence[mu:])], str(k))
                powers.append((f'(= q {q})', choose(cases, cycle)))
            self._define(f'power{bidx}', '(q Int) (e Int)', 'Int', choose(powers, str(k)))
            stable = known is not None and (not block.repeat or self._advance(known,u)==known)
            end_known = self._advance(known,u) if stable else None
            self._define(f'q{bidx + 1}', '', 'Int',
                         str(end_known) if stable else f'(power{bidx} q{bidx} {count})')
            for phase in range(length):
                values = [(f'(= q {q})', str(self._advance(q, u[:phase])))
                          for q in range(k + 1)]
                self._define(f'part{bidx}_{phase}', '(q Int)', 'Int', choose(values, str(k)))
            local = f'(- x {pos})'
            copies = f'(div {local} {length})'; phase = f'(mod {local} {length})'
            base = f'(power{bidx} q{bidx} {copies})'
            state = choose([(f'(= {phase} {j})',
                             str(self._advance(known,u[:j])) if stable else f'(part{bidx}_{j} {base})')
                            for j in range(length)], str(k))
            known = end_known
            char = choose([(f'(= {phase} {j})', str(self.I.alphabet.index(a)))
                           for j, a in enumerate(u)], str(-1))
            interval = f'(and (<= {pos} x) (< x {end}))'
            entries.append((interval, state, char))
        N = f'o{len(self.blocks)}' if self.blocks else '0'
        final = f'q{len(self.blocks)}' if self.blocks else str(self.I.start)
        self._define('N', '', 'Int', N)
        self._define('state', '(x Int)', 'Int',
                     choose([(f'(= x N)', final)] + [(c, s) for c, s, _ in entries], str(k)))
        self._define('letter', '(x Int)', 'Int', choose([(c, a) for c, _, a in entries], '(- 1)'))
        self._define('flagged', '(i Int) (j Int)', 'Bool',
                     disj(f'(and (= (state i) {q}) (= (state j) {r}))'
                          for q, r in sorted(self.I.flags)))
        admissible = conj([
            disj(f'(= (state N) {q})' for q in sorted(self.I.final)),
            '(forall ((v Int)) (=> (and (<= 0 v) (<= v N)) ' +
            conj([f'(< (state v) {k})'] + [f'(not (= (state v) {q}))' for q in sorted(self.I.bad)]) + '))'])
        # Remove the offset quantifier exactly. Within two fixed blocks,
        # characters repeat with period lcm(len(u),len(v)). For every offset
        # residue t, the first eligible h is lo + ((t-lo) mod period).
        def extremum(values, largest):
            out = values[0]
            for value in values[1:]:
                out = f'(ite ({">" if largest else "<"} {value} {out}) {value} {out})'
            return out
        mismatches=[]
        for bp,(op,ep,u) in enumerate(self.segments):
            for bq,(oq,eq,v) in enumerate(self.segments):
                if len(set(u+v))==1:
                    continue
                lo=extremum(['0',f'(- {op} i)',f'(- {oq} j)'],True)
                hi=extremum(['(- N j)',f'(- {ep} i)',f'(- {eq} j)'],False)
                low_name=f'lo{bp}_{bq}'; high_name=f'hi{bp}_{bq}'
                self._define(low_name,'(i Int) (j Int)','Int',lo)
                self._define(high_name,'(i Int) (j Int)','Int',hi)
                lo=f'({low_name} i j)'; hi=f'({high_name} i j)'
                period=len(u)*len(v)//gcd(len(u),len(v))
                residues=[]
                for t in range(period):
                    def char(word,origin,position):
                        if len(set(word))==1:
                            return str(self.I.alphabet.index(word[0]))
                        phase=f'(mod (- (+ {position} {t}) {origin}) {len(word)})'
                        return choose([(f'(= {phase} {a})',str(self.I.alphabet.index(c)))
                                       for a,c in enumerate(word)], '(- 1)')
                    left=char(u,op,'i'); right=char(v,oq,'j')
                    if left==right: continue
                    first=f'(+ {lo} (mod (- {t} {lo}) {period}))'
                    residues.append(conj([f'(< {first} {hi})',f'(not (= {left} {right}))']))
                mismatches.append(disj(residues))
        self._define('has_mismatch','(i Int) (j Int)','Bool',disj(mismatches))
        mismatch = '(has_mismatch i j)'
        obligations = '(forall ((i Int) (j Int)) (=> ' \
                      '(and (<= 0 i) (<= i j) (<= j N) (flagged i j)) ' + mismatch + '))'
        self.formula = conj([admissible, obligations])

    def script(self, values=None, extra=None, timeout_ms=10000, engine="qe2"):
        out = ['(set-option :print-success false)', '(set-option :produce-models true)',
               f'(set-option :timeout {int(timeout_ms)})', '(set-logic LIA)']
        for name in self.names:
            out.append(f'(declare-const {name} Int)'); out.append(f'(assert (>= {name} 0))')
        out += self.definitions
        out.append('(assert ' + self.formula + ')')
        if values is not None:
            if len(values) != len(self.names) or any(v < 0 for v in values):
                raise ValueError('One nonnegative value is required per exponent')
            out += [f'(assert (= {name} {value}))' for name, value in zip(self.names, values)]
        if extra:
            out.append('(assert ' + extra + ')')
        if engine not in ('qe2', 'smt'):
            raise ValueError('Unsupported solver engine')
        out.append('(check-sat)' if engine == 'smt' else
                   '(check-sat-using (then simplify qe2 smt))')
        return '\n'.join(out) + '\n'

    def expand(self, values, limit=1000000):
        if len(values) != len(self.names) or any(v < 0 for v in values):
            raise ValueError('Invalid exponent vector')
        counts = iter(values); parts = []; total = 0
        for b in self.blocks:
            count = next(counts) if b.repeat else 1
            total += count * len(b.word)
            if total > limit:
                raise ValueError('Expanded word exceeds validation limit')
            parts.append(b.word * count)
        return ''.join(parts)

    def solve(self, values=None, extra=None, timeout_ms=10000, confirm_unsat=True):
        script = self.script(values, extra, timeout_ms, engine='smt')
        runner = Path(__file__).with_name('_z3_native.py')
        command = [sys.executable, str(runner)]
        if self.names:
            command.append(','.join(self.names))
        try:
            result = subprocess.run(command, input=script, text=True, capture_output=True,
                                    timeout=timeout_ms / 1000 + 2)
        except subprocess.TimeoutExpired:
            return {'status': 'UNKNOWN', 'reason': 'backend wall-time limit'}
        output = result.stdout
        if result.returncode or '(error' in output:
            return {'status': 'UNKNOWN', 'reason': 'backend error', 'output': output + result.stderr}
        lines = [x.strip() for x in output.splitlines()]
        version = next((x[2:] for x in lines if x.startswith('; Z3 version')), None)
        if 'unsat' in lines:
            if confirm_unsat:
                # Two different solver entry points must agree on a negative
                # answer. This is a safeguard, not an independent proof kernel.
                try:
                    check = subprocess.run(command,
                        input=self.script(values, extra, timeout_ms, engine='qe2'),
                        text=True, capture_output=True, timeout=timeout_ms / 1000 + 2)
                except subprocess.TimeoutExpired:
                    return {'status': 'UNKNOWN', 'reason': 'negative confirmation timeout'}
                if check.returncode or 'unsat' not in check.stdout.splitlines():
                    return {'status': 'UNKNOWN', 'reason': 'negative answer not confirmed',
                            'output': check.stdout + check.stderr}
            return {'status': 'NO_IN_SKELETON', 'backend': version,
                    'negative_confirmation': 'qe2' if confirm_unsat else 'disabled'}
        if 'sat' not in lines:
            return {'status': 'UNKNOWN', 'reason': 'backend returned no exact verdict', 'output': output}
        found = dict((name, int(value)) for name, value in re.findall(r'\((n\d+)\s+(\d+)\)', output))
        if any(n not in found for n in self.names):
            return {'status': 'UNKNOWN', 'reason': 'missing exponent model', 'output': output}
        vector = [found[name] for name in self.names]
        try:
            word = self.expand(vector)
        except ValueError as error:
            return {'status': 'UNKNOWN', 'reason': str(error), 'exponents': vector}
        if not witness(self.I, word) or not border_witness(self.I, word):
            return {'status': 'UNKNOWN', 'reason': 'independent witness validation failed',
                    'exponents': vector, 'word': word}
        return {'status': 'YES', 'word': word, 'exponents': vector, 'backend': version}
