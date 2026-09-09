"""Terminal source capture: word equations with explicit regular constraints.

The mathematical reduction is exact. Optional SMT execution is a separate,
potentially incomplete backend; no timeout or UNKNOWN is a negative answer.
See notes/2026-09-09-source-capture-word-equations.md. Standard library only.
"""
from dataclasses import dataclass
from typing import FrozenSet, Optional, Tuple
import json

from border_lab import Instance


@dataclass(frozen=True)
class DFA:
    """Partial DFA; -1 rejects. Accepts the empty word iff start is final."""
    delta: Tuple[Tuple[int, ...], ...]
    start: int
    final: FrozenSet[int]
    alphabet: str = '01'

    def endpoint(self, word: str) -> Optional[int]:
        q = self.start
        for a in word:
            if a not in self.alphabet:
                return None
            q = self.delta[q][self.alphabet.index(a)]
            if q < 0:
                return None
        return q

    def accepts(self, word: str) -> bool:
        return self.endpoint(word) in self.final


def validate_terminal(I: Instance) -> None:
    k = len(I.delta)
    if not k or I.alphabet != '01':
        raise ValueError('A nonempty binary state table is required')
    if not 0 <= I.start < k:
        raise ValueError('Invalid initial state')
    if any(len(row) != 2 or any(not -1 <= q < k for q in row) for row in I.delta):
        raise ValueError('Invalid transition table')
    if any(not 0 <= q < k for q in I.final | I.bad):
        raise ValueError('Invalid final or Bad state')
    if any(not 0 <= p < k or not 0 <= q < k for p, q in I.flags):
        raise ValueError('Invalid flag endpoint')
    if any(any(q >= 0 for q in I.delta[f]) for f in I.final):
        raise ValueError('All accepting states must be terminal')


def path_dfa(I: Instance, start: int, finals, forbidden=frozenset(),
             no_return: Optional[int] = None, stop: Optional[int] = None) -> DFA:
    """Safe paths, with optional forbidden states, no return, or first-hit stop.

    no_return removes every edge *into* that state but permits starting there.
    stop removes outgoing edges at that state, so accepting there is first-hit.
    """
    blocked = I.bad | frozenset(forbidden)
    rows = tuple(tuple(-1 if p in blocked or p == stop or q < 0 or
                       q in blocked or q == no_return else q for q in row)
                 for p, row in enumerate(I.delta))
    accepting = frozenset(finals) - blocked
    # A blocked initial state must reject even epsilon and cannot make a step.
    return DFA(rows, start, accepting, I.alphabet)


def capture_language(I: Instance, target: int) -> DFA:
    return path_dfa(I, target, I.final)


def no_capture_language(I: Instance, target: int) -> DFA:
    """Complement of L_target Sigma*: a complete k+2-state DFA.

    hit is absorbing and rejecting; miss is absorbing and accepting. A safe
    simulation state is accepting until its run first reaches a final state.
    """
    k = len(I.delta)
    hit, miss = k, k + 1
    def classify(q):
        if q < 0 or q in I.bad:
            return miss
        return hit if q in I.final else q
    rows = []
    for p, row in enumerate(I.delta):
        if p in I.bad:
            rows.append((miss, miss))
        elif p in I.final:
            rows.append((hit, hit))
        else:
            rows.append(tuple(classify(q) for q in row))
    rows.extend(((hit, hit), (miss, miss)))
    return DFA(tuple(rows), classify(target), frozenset(set(range(k + 2)) - {hit}))


def capture_prefix(I: Instance, target: int, word: str) -> Optional[str]:
    """The unique prefix accepted from target, or None (terminal inputs only)."""
    q = target
    if q in I.bad:
        return None
    if q in I.final:
        return ''
    for i, a in enumerate(word):
        if a not in I.alphabet:
            return None
        q = I.delta[q][I.alphabet.index(a)]
        if q < 0 or q in I.bad:
            return None
        if q in I.final:
            return word[:i + 1]
    return None


def capture_clause(I: Instance, source: int, target: int, word: str) -> bool:
    """No violation from the single source *position* 0 to target-state cuts.

    The surrounding theorem also requires a safe accepted run from source.
    """
    v = capture_prefix(I, target, word)
    if v is None or not word.endswith(v):
        return True
    u = word[:len(word) - len(v)]
    return path_dfa(I, source, set(range(len(I.delta))) - {target}).accepts(u)


def single_source_normal_form(I: Instance, word: str) -> str:
    """Erase first-to-last source return; sound on single-source witnesses."""
    sources = {p for p, _ in I.flags}
    if len(sources) > 1:
        raise ValueError('Single-source normalization requires at most one source')
    if not I.admissible(word):
        raise ValueError('An admissible word is required')
    if not sources:
        return word
    p = next(iter(sources))
    positions = [i for i, q in enumerate(I.run(word)) if q == p]
    return word if not positions else word[:positions[0]] + word[positions[-1]:]


# A small positive existential formula representation. Every string variable
# ranges over {0,1}*. No length, substring, containment or universal primitives.
def var(name):
    return ('var', name)


def literal(value):
    return ('lit', value)


def cat(*terms):
    return ('cat',) + terms


def eq(left, right):
    return ('eq', left, right)


def conjunction(*parts):
    return ('and',) + parts


def disjunction(*parts):
    return ('or',) + parts


class Program:
    def __init__(self):
        self.variables = []
        self.languages = {}
        self.formula = ('and',)

    def fresh(self, prefix):
        name = prefix + '_' + str(len(self.variables))
        self.variables.append(name)
        return var(name)

    def member(self, term, automaton):
        if term[0] != 'var':
            raise ValueError('Regular membership is attached to a variable')
        name = 'L' + str(len(self.languages))
        self.languages[name] = automaton
        return ('reg', term, name)

    def capture(self, I, source, target, word):
        v, x, u = (self.fresh(s) for s in ('V', 'X', 'U'))
        mismatches = []
        for a, b in (('0', '1'), ('1', '0')):
            r, s, z = (self.fresh(t) for t in ('R', 'S', 'Z'))
            mismatches.append(conjunction(eq(v, cat(r, literal(a), z)),
                                          eq(word, cat(s, literal(b), z))))
        return disjunction(
            self.member(word, no_capture_language(I, target)),
            conjunction(eq(word, cat(v, x)),
                        self.member(v, capture_language(I, target)),
                        disjunction(*mismatches,
                            conjunction(eq(word, cat(u, v)),
                                self.member(u, path_dfa(I, source,
                                    set(range(len(I.delta))) - {target}))))))

    def to_dict(self):
        return {'alphabet': '01', 'quantifier': 'exists',
                'variables': self.variables, 'formula': self.formula,
                'languages': {name: dict(delta=d.delta, start=d.start,
                                        final=sorted(d.final), alphabet=d.alphabet)
                              for name, d in self.languages.items()}}

    def smt2(self, fixed_word=None, timeout_ms=5000):
        """Practical backend representation; regex elimination is not polynomial.

        The theoretical size/PSPACE claim concerns explicit DFA atoms above,
        not this optional state-elimination adapter or a solver's heuristics.
        """
        out = ['(set-logic QF_S)', '(set-option :produce-models true)',
               '(set-option :timeout ' + str(int(timeout_ms)) + ')']
        rex = RegexDAG(out)
        binary = rex.star(rex.union(rex.letter('0'), rex.letter('1')))
        for name in self.variables:
            out.append('(declare-const ' + name + ' String)')
            out.append('(assert (str.in_re ' + name + ' ' + binary + '))')
        languages = {name: rex.from_dfa(d) for name, d in self.languages.items()}
        def emit(node):
            op = node[0]
            if op == 'var':
                return node[1]
            if op == 'lit':
                return json.dumps(node[1])
            if op == 'cat':
                if len(node) == 1:
                    return '""'
                if len(node) == 2:
                    return emit(node[1])
                return '(str.++ ' + ' '.join(emit(t) for t in node[1:]) + ')'
            if op == 'eq':
                return '(= ' + emit(node[1]) + ' ' + emit(node[2]) + ')'
            if op == 'reg':
                return '(str.in_re ' + emit(node[1]) + ' ' + languages[node[2]] + ')'
            if op in ('and', 'or'):
                if len(node) == 1:
                    return 'true' if op == 'and' else 'false'
                return '(' + op + ' ' + ' '.join(emit(t) for t in node[1:]) + ')'
            raise ValueError('Unknown formula operator: ' + op)
        out.append('(assert ' + emit(self.formula) + ')')
        if fixed_word is not None:
            if any(a not in '01' for a in fixed_word):
                raise ValueError('A fixed word must be binary')
            out.append('(assert (= W ' + json.dumps(fixed_word) + '))')
        out.append('(check-sat)')
        return '\n'.join(out) + '\n'


def compile_single_source(I: Instance) -> Program:
    """An exact existential formula for existence, including source returns."""
    validate_terminal(I)
    sources = {p for p, _ in I.flags}
    if len(sources) > 1:
        raise ValueError('This compiler accepts at most one flagged source state')
    P = Program()
    P.variables.append('W')
    w = var('W')
    if not sources:
        P.formula = P.member(w, path_dfa(I, I.start, I.final))
        return P
    p = next(iter(sources))
    e, z = P.fresh('E'), P.fresh('Tail')
    avoid = P.member(w, path_dfa(I, I.start, I.final, forbidden={p}))
    once = conjunction(eq(w, cat(e, z)),
             P.member(e, path_dfa(I, I.start, {p}, stop=p)),
             P.member(z, path_dfa(I, p, I.final, no_return=p)),
             *(P.capture(I, p, t, z) for t in sorted({t for s, t in I.flags})))
    P.formula = disjunction(avoid, once)
    return P


def compile_source_sequence(I: Instance, sequence) -> Program:
    """Exact formula for one supplied source-visit sequence (not a cover).

    For a supplied count bound R, enumerate sequences of length <=R. Positive
    segments prevent counting a source position twice. Terminal-source visits
    and epsilon are retained; the final segment may be empty.
    """
    validate_terminal(I)
    sources = {p for p, _ in I.flags}
    sequence = tuple(sequence)
    if any(p not in sources for p in sequence):
        raise ValueError('A sequence entry must be a flagged source state')
    P = Program()
    P.variables.append('W')
    w = var('W')
    if not sequence:
        P.formula = P.member(w, path_dfa(I, I.start, I.final, forbidden=sources))
        return P
    segments = [P.fresh('B') for _ in range(len(sequence) + 1)]
    tails = [P.fresh('Tail') for _ in sequence]
    parts = [eq(w, cat(*segments))]
    # First entry: no source may be visited before the chosen first one.
    parts.append(P.member(segments[0], path_dfa(
        I, I.start, {sequence[0]}, forbidden=sources - {sequence[0]},
        stop=sequence[0])))
    # If initial is already a source different from sequence[0], this rejects.
    for j, p in enumerate(sequence):
        parts.append(eq(tails[j], cat(*segments[j + 1:])))
        if j + 1 < len(sequence):
            parts.append(P.member(segments[j + 1], between_sources(I, p, sequence[j+1], sources)))
        else:
            parts.append(P.member(segments[j+1], after_last_source(I, p, sources)))
        parts.extend(P.capture(I, p, t, tails[j]) for s, t in sorted(I.flags) if s == p)
    P.formula = conjunction(*parts)
    return P


def between_sources(I, source, target, sources) -> DFA:
    """Positive paths with the indicated next source and no interior source.

    Extra state k represents the initial source occurrence. Original source
    states have no outgoing edges; only target is accepting. Thus even when
    source==target, the segment is nonempty and ends at its next occurrence.
    """
    k = len(I.delta)
    blocked = I.bad
    def row(p):
        return tuple(-1 if p in blocked or q < 0 or q in blocked or
                      (q in sources and q != target) else q for q in I.delta[p])
    rows = [((-1, -1) if q in sources else row(q)) for q in range(k)]
    rows.append(row(source))
    return DFA(tuple(rows), k, frozenset({target}) - blocked)


def after_last_source(I, source, sources) -> DFA:
    """Final segment from a source, permitting epsilon but no later source."""
    rows = tuple(tuple(-1 if p in I.bad or q < 0 or q in I.bad or q in sources
                       else q for q in row) for p, row in enumerate(I.delta))
    return DFA(rows, source, I.final - I.bad)


class RegexDAG:
    """GNFA state elimination with named, hash-consed regex subexpressions."""
    empty = 're.none'
    epsilon = '(str.to_re "")'

    def __init__(self, output):
        self.output = output
        self.memo = {}

    def make(self, op, *args):
        key = (op,) + args
        if key not in self.memo:
            name = 're_' + str(len(self.memo))
            self.memo[key] = name
            self.output.append('(define-fun ' + name + ' () (RegEx String) (' +
                               op + ' ' + ' '.join(args) + '))')
        return self.memo[key]

    def letter(self, a):
        return '(str.to_re ' + json.dumps(a) + ')'

    def union(self, a, b):
        if a == self.empty or a == b:
            return b
        if b == self.empty:
            return a
        return self.make('re.union', *sorted((a, b)))

    def concat(self, *args):
        if self.empty in args:
            return self.empty
        args = tuple(a for a in args if a != self.epsilon)
        if not args:
            return self.epsilon
        if len(args) == 1:
            return args[0]
        return self.make('re.++', *args)

    def star(self, a):
        return self.epsilon if a in (self.empty, self.epsilon) else self.make('re.*', a)

    def from_dfa(self, d):
        n = len(d.delta)
        start, end = n, n + 1
        edges = {}
        def add(i, j, value):
            edges[i, j] = self.union(edges.get((i, j), self.empty), value)
        add(start, d.start, self.epsilon)
        for q in d.final:
            add(q, end, self.epsilon)
        for q, row in enumerate(d.delta):
            for ai, target in enumerate(row):
                if target >= 0:
                    add(q, target, self.letter(d.alphabet[ai]))
        for q in range(n):
            left = [(i, r) for (i, j), r in edges.items() if j == q and i != q]
            right = [(j, r) for (i, j), r in edges.items() if i == q and j != q]
            loop = self.star(edges.get((q, q), self.empty))
            for i, a in left:
                for j, b in right:
                    add(i, j, self.concat(a, loop, b))
            edges = {(i, j): r for (i, j), r in edges.items() if i != q and j != q}
        return edges.get((start, end), self.empty)
