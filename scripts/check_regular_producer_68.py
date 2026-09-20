"""Issue 68: independent exact-language and original-input model checks.

This runs the byte-pinned existing Python extractor. The epsilon-free NFA is
an independent executable presentation of the proposed proof, NOT execution
of Lean. Pair-product exhaustion proves all-word language equivalence for each
completed finite case. Caps are UNKNOWN, never an entailment answer.

Run from any directory:
  python3 scripts/check_regular_producer_68.py --lean
Lean gates are NOT RUN when the pinned toolchain is unavailable. No shared
workflow, import aggregator, or existing producer file is modified.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import random
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import regular_countermodel as rc

BASE = '19b06d4fed9da635d9b911f0e908d04e4fc4b099'
PRODUCER_BLOB = 'b59c57174e24d00fdbe8dfca1c99337921adf88f'
SEED = 2026092068
PAIR_CAP = 50000


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def require(condition: bool, detail: object) -> None:
    if not condition:
        raise AssertionError(detail)


@dataclass(frozen=True)
class Problem:
    variables: tuple[str, ...]
    constraints: tuple[tuple[tuple, tuple], ...]
    query: tuple[tuple, tuple]


BOT = ('bot',)


def var(i: int) -> tuple:
    return ('var', i)


def prod(left: tuple, right: tuple) -> tuple:
    return ('prod', left, right)


def balanced_sets(system: rc.System) -> set[tuple[int, int]]:
    """Literal finite Horn saturation, independent of bit-row Warshall code."""
    relation = {(p, p) for p in range(system.size)} | set(system.epsilon)
    while True:
        old = set(relation)
        relation |= {(p, r) for p, q in old for s, r in old if q == s}
        relation |= {(p, t) for p, a, q in system.push
                     for r, b, t in system.pop if a == b and (q, r) in old}
        if relation == old:
            return relation


def consume(system: rc.System, balanced: set, p: int, word: tuple) -> set[int]:
    states = {q for s, q in balanced if s == p}
    for a in word:
        targets = {q for s, b, q in system.pop if s in states and a == b}
        states = {q for s, q in balanced if s in targets}
    return states


class EpsilonFree:
    """Semantic presentation of the Lean draft; not a Lean runtime proxy."""
    def __init__(self, system: rc.System, seeds: set[tuple[int, tuple]]):
        reverse = system.reverse()
        forward_balanced = balanced_sets(system)
        reverse_balanced = balanced_sets(reverse)
        suffixes = {u[i:] for _, u in seeds for i in range(len(u) + 1)}
        self.states = [('c', q) for q in range(system.size)]
        self.states += [('s', z) for z in sorted(suffixes)]
        self.ids = {state: i for i, state in enumerate(self.states)}
        self.edges = {(i, a): set() for i in range(len(self.states)) for a in (0, 1)}
        self.final = set()
        attachments = {r: set() for r in range(system.size)}
        for p, u in seeds:
            for i in range(len(u) + 1):
                for r in consume(system, forward_balanced, p, u[:i]):
                    attachments[r].add(u[i:])
        for q in range(system.size):
            source = self.ids['c', q]
            for p, r in reverse_balanced:
                if p != q:
                    continue
                for start, a, target in reverse.pop:
                    if start == r:
                        self.edges[source, a].add(self.ids['c', target])
                for suffix in attachments[r]:
                    if not suffix:
                        self.final.add(source)
                    else:
                        self.edges[source, suffix[0]].add(self.ids['s', suffix[1:]])
        for suffix in suffixes:
            source = self.ids['s', suffix]
            if not suffix:
                self.final.add(source)
            else:
                self.edges[source, suffix[0]].add(self.ids['s', suffix[1:]])

    def start(self, q: int) -> frozenset[int]:
        return frozenset({self.ids['c', q]})

    def step(self, states: frozenset[int], a: int) -> frozenset[int]:
        return frozenset(t for p in states for t in self.edges[p, a])

    def accepts_set(self, states: frozenset[int]) -> bool:
        return bool(states & self.final)


def exact_equivalence(left_start, left_step, left_final,
                      right_start, right_step, right_final, cap=PAIR_CAP) -> dict:
    """Exhaust the synchronous finite product. Return a real separator or UNKNOWN."""
    start = (left_start, right_start)
    seen, queue = {start}, deque([(start, ())])
    while queue:
        (left, right), word = queue.popleft()
        if left_final(left) != right_final(right):
            return {'status': 'FAIL', 'separator': list(word), 'pairs': len(seen)}
        for a in (0, 1):
            pair = (left_step(left, a), right_step(right, a))
            if pair not in seen:
                if len(seen) >= cap:
                    return {'status': 'UNKNOWN', 'reason': 'pair_limit', 'pairs': len(seen)}
                seen.add(pair)
                queue.append((pair, word + (a,)))
    return {'status': 'PASS', 'pairs': len(seen)}


def literal_closure(system: rc.System, seeds: set) -> set:
    """All configurations, not depth-bounded: every edge strictly raises control."""
    require(all(p < q for p, q in system.epsilon), 'cyclic epsilon input')
    require(all(p < q for p, _, q in system.push | system.pop), 'cyclic stack input')
    found, queue = set(seeds), deque(seeds)
    while queue:
        p, word = queue.popleft()
        successors = [(q, word) for s, q in system.epsilon if s == p]
        successors += [(q, (a,) + word) for s, a, q in system.push if s == p]
        successors += [(q, word[1:]) for s, a, q in system.pop
                       if s == p and word and a == word[0]]
        for successor in successors:
            if successor not in found:
                found.add(successor)
                queue.append(successor)
    return found


def trie_machine(words: set[tuple]):
    prefixes = {w[:i] for w in words for i in range(len(w) + 1)} | {()}

    def step(state, a):
        if state is None:
            return None
        child = state + (a,)
        return child if child in prefixes else None

    return (), step, lambda state: state is not None and state in words


def expand_expressions(problem: Problem, model: dict):
    """Evaluate original syntax by appending nodes; never call normalization."""
    nodes = [None if x is None else tuple(x) for x in model['nodes']]
    count = len(nodes)
    require(count > 0, 'graph has no nodes')
    for node in nodes:
        require(node is None or (len(node) == 2 and all(type(q) is int and 0 <= q < count
                                                       for q in node)), ('invalid node', node))
    require(set(model['roots']) == set(problem.variables), 'wrong variable roots')
    roots = [model['roots'][name] for name in problem.variables]
    require(all(type(q) is int and 0 <= q < count for q in roots), 'invalid root')
    memo = {}

    def evaluate(e):
        if e in memo:
            return memo[e]
        if e[0] == 'var':
            q = roots[e[1]]
        else:
            node = None if e[0] == 'bot' else (evaluate(e[1]), evaluate(e[2]))
            q = len(nodes)
            nodes.append(node)
        memo[e] = q
        return q

    premise_pairs = [(evaluate(s), evaluate(t)) for s, t in problem.constraints]
    query_pair = tuple(evaluate(e) for e in problem.query)
    return nodes, premise_pairs, query_pair


def inclusion(nodes, start) -> dict:
    """All-address inclusion by the finite synchronous pair graph, including cycles."""
    seen, queue = {start}, deque([(start, ())])
    while queue:
        (p, q), word = queue.popleft()
        if nodes[p] is None:
            continue
        if nodes[q] is None:
            return {'below': False, 'separator': word, 'pairs': len(seen)}
        for a in (0, 1):
            child = (nodes[p][a], nodes[q][a])
            if child not in seen:
                seen.add(child)
                queue.append((child, word + (a,)))
    return {'below': True, 'pairs': len(seen)}


def at_word(nodes, root, word) -> bool:
    for a in word:
        if nodes[root] is None:
            return False
        root = nodes[root][a]
    return nodes[root] is not None


def check_model(problem: Problem, model: dict, word=None) -> dict:
    nodes, premises, query = expand_expressions(problem, model)
    checks = [inclusion(nodes, pair) for pair in premises]
    result = inclusion(nodes, query)
    valid = all(x['below'] for x in checks) and not result['below']
    if word is not None:
        valid = valid and at_word(nodes, query[0], word) and not at_word(nodes, query[1], word)
    return {'valid': valid, 'premise_pairs': sum(x['pairs'] for x in checks),
            'query_pairs': result['pairs'],
            'independent_separator': list(result.get('separator', ()))}


def has_reachable_cycle(model: dict) -> bool:
    nodes = model['nodes']
    reachable = set(model['roots'].values())
    queue = deque(reachable)
    while queue:
        p = queue.popleft()
        for q in (() if nodes[p] is None else nodes[p]):
            if q not in reachable:
                reachable.add(q)
                queue.append(q)
    degree = {p: 0 for p in reachable}
    for p in reachable:
        for q in (() if nodes[p] is None else nodes[p]):
            degree[q] += 1
    queue = deque(p for p in degree if degree[p] == 0)
    removed = 0
    while queue:
        p = queue.popleft()
        removed += 1
        for q in (() if nodes[p] is None else nodes[p]):
            degree[q] -= 1
            if degree[q] == 0:
                queue.append(q)
    return removed < len(reachable)


def periodic_problem(period: tuple[int, ...], depth: int) -> Problem:
    m = len(period)
    variables = tuple('x' + str(i) for i in range(m))
    premises = []
    for i, a in enumerate(period):
        child = var((i + 1) % m)
        rhs = prod(child, BOT) if a == 0 else prod(BOT, child)
        premises += [(var(i), rhs), (rhs, var(i))]
    approximant = BOT
    for i in reversed(range(depth)):
        approximant = prod(approximant, BOT) if period[i % m] == 0 else prod(BOT, approximant)
    return Problem(variables, tuple(premises), (var(0), approximant))


def language_checks(rng: random.Random) -> dict:
    result = {'cyclic_systems': 160, 'acyclic_systems': 80,
              'exact_nfa_equivalences': 0, 'exact_literal_equivalences': 0,
              'product_pairs': 0, 'literal_configurations': 0, 'unknown': []}
    small_words = [w for d in range(4) for w in product((0, 1), repeat=d)]
    for sample in range(result['cyclic_systems'] + result['acyclic_systems']):
        acyclic = sample >= result['cyclic_systems']
        n = rng.randrange(1, 6 if acyclic else 5)
        pairs = [(p, q) for p in range(n) for q in range(n) if not acyclic or p < q]
        eps = {(p, q) for p, q in pairs if rng.random() < .18}
        push = {(p, a, q) for p, q in pairs for a in (0, 1) if rng.random() < .17}
        pop = {(p, a, q) for p, q in pairs for a in (0, 1) if rng.random() < .17}
        system = rc.System(n, eps, push, pop, set(), set(), 0, 0)
        seeds = {(rng.randrange(n), rng.choice(small_words)) for _ in range(sample % 5)}
        original = rc.ClosureNFA(rc.PopMachine(system), rc.PopMachine(system.reverse()), seeds)
        alternative = EpsilonFree(system, seeds)
        literal = literal_closure(system, seeds) if acyclic else None
        if literal is not None:
            result['literal_configurations'] += len(literal)
        for q in range(n):
            check = exact_equivalence(original.epsilon[q], original.step,
                lambda states: bool(states & original.final),
                alternative.start(q), alternative.step, alternative.accepts_set)
            require(check['status'] != 'FAIL', ('epsilon-free mismatch', sample, q, check))
            result['product_pairs'] += check['pairs']
            if check['status'] == 'UNKNOWN':
                result['unknown'].append({'sample': sample, 'control': q, **check})
            else:
                result['exact_nfa_equivalences'] += 1
            if literal is not None:
                start, step, final = trie_machine({w for p, w in literal if p == q})
                check = exact_equivalence(original.epsilon[q], original.step,
                    lambda states: bool(states & original.final), start, step, final)
                require(check['status'] != 'FAIL', ('literal mismatch', sample, q, check))
                result['product_pairs'] += check['pairs']
                if check['status'] == 'UNKNOWN':
                    result['unknown'].append({'sample': sample, 'control': q, **check})
                else:
                    result['exact_literal_equivalences'] += 1
    return result


def model_checks() -> dict:
    periods = [(0, 1), (0, 0, 1), (0, 0, 0, 1), (0, 0, 1, 0, 1),
               (0, 0, 1, 0, 1, 1), (0, 1, 0, 0, 0, 1, 1)]
    rows, old_assignments = [], 0
    for period in periods:
        for depth in (1, 2, 4):
            problem = periodic_problem(period, depth)
            found = rc.extract(problem, time.monotonic() + 10, max_words=128)
            require(found['status'] == 'FOUND', (period, depth, found))
            word = found['separating_path']
            checked = check_model(problem, found['model'], word)
            require(checked['valid'], (period, depth, found, checked))
            require(word == [period[i % len(period)] for i in range(depth)],
                    ('same earliest address', period, depth, word))
            require(has_reachable_cycle(found['model']), ('cycle lost', period, depth))
            rows.append({'period': list(period), 'depth': depth, 'status': 'PASS',
                         'candidates': found['candidates'], 'separator': word,
                         'graph_nodes': len(found['model']['nodes']), 'reachable_cycle': True,
                         'model': found['model'], 'independent_check': checked})
        if len(period) <= 4:
            problem = periodic_problem(period, 2)
            old_nodes = [None, [0, 0], [2, 2], [3, 0], [0, 4]]
            for values in product(range(5), repeat=len(period)):
                old_assignments += 1
                old_model = {'nodes': old_nodes, 'roots': dict(zip(problem.variables, values))}
                require(not check_model(problem, old_model)['valid'], ('old library worked', period, values))
    boundary_problems = [
        Problem(('x',), (), (var(0), BOT)),
        Problem((), (), (prod(BOT, prod(BOT, BOT)), prod(BOT, BOT))),
        Problem(('x', 'y'), ((var(0), prod(var(1), BOT)),), (var(0), BOT)),
    ]
    boundaries = []
    for problem in boundary_problems:
        found = rc.extract(problem, time.monotonic() + 5, max_words=64)
        require(found['status'] == 'FOUND', found)
        checked = check_model(problem, found['model'], found['separating_path'])
        require(checked['valid'], (problem, found, checked))
        boundaries.append({'variables': len(problem.variables), 'status': 'PASS',
                           'separator': found['separating_path'], 'independent_check': checked})
    return {'periodic_cyclic_models': rows, 'boundary_models': boundaries,
            'old_library_assignments_rejected': old_assignments}


def guard_checks() -> dict:
    system = rc.System(1, set(), set(), set(), set(), set(), 0, 0)
    nfa = rc.ClosureNFA(rc.PopMachine(system), rc.PopMachine(system.reverse()), {(0, (0,))})
    try:
        nfa.graph(('x',))
    except ValueError as exc:
        require('not prefix-closed' in str(exc), str(exc))
    else:
        raise AssertionError('rejected residual with accepting extension was pruned silently')
    positives = [
        Problem(('x',), ((var(0), BOT),), (var(0), BOT)),
        Problem(('x',), ((var(0), BOT), (prod(BOT, BOT), var(0))), (var(0), BOT)),
        Problem(('x',), (), (var(0), var(0))),
    ]
    limits = []
    for problem in positives:
        output = rc.extract(problem, max_words=16)
        require(output['status'] == 'UNKNOWN' and output['reason'] == 'word_limit', output)
        limits.append(output)
    expired = rc.extract(Problem(('x',), (), (var(0), BOT)), deadline=0)
    require(expired['status'] == 'UNKNOWN' and expired['reason'] == 'time_limit', expired)
    # Full finite-product equivalence must also expose its cap, not claim success.
    capped = exact_equivalence(0, lambda p, a: (p + 1) % 3, lambda p: False,
                               0, lambda p, a: (p + 1) % 4, lambda p: False, cap=1)
    require(capped['status'] == 'UNKNOWN', capped)
    return {'non_prefix_closed_graph_guard': 'PASS', 'capped_extractions': limits,
            'expired_extraction': expired, 'pair_cap_guard': capped}


def lean_checks(requested: bool, timeout: float) -> dict:
    names = ['core_build', 'module_build', 'kernel_replay', 'axiom_audit', 'native_producer']
    answer = {name: {'status': 'NOT RUN'} for name in names}
    if not requested:
        answer['reason'] = 'not requested; use --lean'
        return answer
    if not shutil.which('lake') or not shutil.which('lean'):
        answer['reason'] = 'Lean/Lake unavailable in this container; no inherited PASS'
        return answer
    lean = ROOT / 'lean'
    commands = [
        ('version', ['lake', 'env', 'lean', '--version']),
        ('core_build', ['lake', 'build']),
        ('module_build', ['lake', 'build', '+Subtail.RegularLanguageGraph',
                          '+Subtail.RegularCountermodelProducer']),
        ('kernel_replay', ['lake', 'env', 'leanchecker', 'Subtail.RegularCountermodelProducer']),
        ('axiom_audit', ['lake', 'env', 'lean', 'Subtail/RegularCountermodelProducerAudit.lean']),
    ]
    logs = ROOT / 'tmp' / 'regular-producer-68'
    logs.mkdir(parents=True, exist_ok=True)
    for name, command in commands:
        started = time.monotonic()
        try:
            out = subprocess.run(command, cwd=lean, text=True, capture_output=True,
                                 timeout=timeout)
        except subprocess.TimeoutExpired:
            answer[name] = {'status': 'UNKNOWN', 'reason': 'time_limit', 'command': command}
            return answer
        text = out.stdout + out.stderr
        (logs / (name + '.log')).write_text(text)
        answer[name] = {'status': 'PASS' if out.returncode == 0 else 'FAIL',
                        'command': command, 'seconds': time.monotonic() - started,
                        'log_sha256': hashlib.sha256(text.encode()).hexdigest()}
        if out.returncode != 0:
            print(text, flush=True)
            return answer
        if name == 'version' and 'version 4.33.1,' not in text:
            answer[name]['status'] = 'FAIL'
            answer[name]['reason'] = 'wrong pinned Lean version'
            return answer
        if name == 'axiom_audit':
            matches = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])", text)
            found = {name: sorted(x.strip() for x in axioms.split(',') if x.strip())
                     for name, axioms in matches}
            expected = (lean / 'Subtail/RegularCountermodelProducerAudit.lean').read_text()
            expected = set(re.findall(r'^#print axioms (\S+)', expected, re.M))
            answer[name]['closures'] = found
            answer[name]['inventory_complete'] = set(found) == expected
            unexpected = {name: values for name, values in found.items()
                          if set(values) - {'propext', 'Quot.sound', 'Classical.choice'}}
            answer[name]['unexpected_axioms'] = unexpected
            answer[name]['classical_closures'] = [name for name, values in found.items()
                                                if 'Classical.choice' in values]
            # Classical in an executable declaration can be an erased proof dependency;
            # it is NOT silently reported as a choice-free runtime closure.
            answer[name]['runtime_erasure_review'] = 'NOT RUN'
            if set(found) != expected or unexpected:
                answer[name]['status'] = 'FAIL'
                return answer
    helper = r"""import Subtail.RegularCountermodelProducer
open Subtail Subtail.TreeSemantics Subtail.ExpressionNormalization
open Subtail.RegularCountermodelProducer
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def emit (label : String) {n : Nat} (result : Option (Model n)) : IO Unit := do
  match result with
  | none => IO.println ("REGULAR68 " ++ label ++ " null")
  | some m =>
      let nodes := (List.finRange m.size).map fun q =>
        match m.graph.nodes.get q with
        | none => "null"
        | some (l, r) => "[" ++ toString l.val ++ "," ++ toString r.val ++ "]"
      let roots := (List.finRange n).map fun q => toString (m.roots q).val
      let word := m.word.map fun a => if a then "1" else "0"
      IO.println ("REGULAR68 " ++ label ++ " {\"nodes\":[" ++
        String.intercalate "," nodes ++ "],\"roots\":[" ++
        String.intercalate "," roots ++ "],\"word\":[" ++
        String.intercalate "," word ++ "]}")
"""
    native_cases = [
        ('closed_negative', Problem((), (), (prod(BOT, BOT), BOT)),
         'produce ([] : Input 0) (.prod .bot .bot) .bot', False),
        ('variable_negative', Problem(('x',), (), (var(0), BOT)),
         'produce ([] : Input 1) (.var 0) .bot', False),
        ('cyclic_negative', Problem(('x',), ((prod(var(0), BOT), var(0)),), (var(0), BOT)),
         'produce ([(.prod (.var 0) .bot, .var 0)] : Input 1) (.var 0) .bot', False),
        ('positive', Problem(('x',), (), (var(0), var(0))),
         'produce ([] : Input 1) (.var 0) (.var 0)', True),
        ('normalized_alternating', Problem(('x', 'y', 'b'),
          ((prod(var(2), var(1)), var(0)), (var(0), prod(var(2), var(1))),
           (prod(var(0), var(2)), var(1)), (var(1), prod(var(0), var(2))), (var(2), BOT)),
          (var(0), prod(BOT, BOT))),
         'some (normalizedModel ([.lower 2 1 0, .upper 0 2 1, .lower 0 2 1, .upper 1 0 2, .denial 2] : List (Constraint 3)) 0 [true])', False),
    ]
    records = []
    for label, problem, expression, positive in native_cases:
        filename = logs / (label + '.lean')
        filename.write_text(helper + '\n#eval emit "' + label + '" (' + expression + ')\n')
        command = ['lake', 'env', 'lean', str(filename)]
        try:
            out = subprocess.run(command, cwd=lean, text=True, capture_output=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            records.append({'case': label, 'status': 'UNKNOWN', 'reason': 'time_limit'})
            continue
        text = out.stdout + out.stderr
        (logs / (label + '.log')).write_text(text)
        if out.returncode:
            print(text, flush=True)
            records.append({'case': label, 'status': 'FAIL', 'reason': 'native_command_failed'})
            continue
        marker = 'REGULAR68 ' + label + ' '
        lines = [line[len(marker):] for line in text.splitlines() if line.startswith(marker)]
        if len(lines) != 1:
            records.append({'case': label, 'status': 'FAIL', 'reason': 'missing_or_duplicate_marker'})
            continue
        data = json.loads(lines[0])
        if positive:
            records.append({'case': label, 'status': 'PASS' if data is None else 'FAIL',
                            'answer': 'none' if data is None else 'unexpected_model'})
            continue
        if data is None:
            records.append({'case': label, 'status': 'FAIL', 'reason': 'unexpected_none'})
            continue
        model = {'nodes': data['nodes'], 'roots': dict(zip(problem.variables, data['roots']))}
        checked = check_model(problem, model, data['word'])
        records.append({'case': label, 'status': 'PASS' if checked['valid'] else 'FAIL',
                        'independent_check': checked, 'separator': data['word'],
                        'graph_nodes': len(data['nodes']), 'reachable_cycle': has_reachable_cycle(model),
                        'log_sha256': hashlib.sha256(text.encode()).hexdigest()})
    status = 'FAIL' if any(x['status'] == 'FAIL' for x in records) else (
        'UNKNOWN' if any(x['status'] == 'UNKNOWN' for x in records) else 'PASS')
    answer['native_producer'] = {'status': status, 'cases': records}

    return answer


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true')
    parser.add_argument('--lean-timeout', type=float, default=120)
    parser.add_argument('--output', type=Path, default=ROOT / 'results/regular-producer-68.json')
    args = parser.parse_args()
    started = time.monotonic()
    source = ROOT / 'scripts/regular_countermodel.py'
    require(git_blob(source.read_bytes()) == PRODUCER_BLOB, 'upstream Python producer changed')
    result = {'upstream_commit': BASE, 'upstream_producer_blob': PRODUCER_BLOB,
              'seed': SEED, 'finite_product_pair_cap': PAIR_CAP,
              'environment': {'python': sys.version, 'platform': platform.platform()},
              'scope': 'Actual pinned Python extractor; all-depth finite checks. Lean separately gated.'}
    result['language_checks'] = language_checks(random.Random(SEED))
    result['model_checks'] = model_checks()
    result['guard_checks'] = guard_checks()
    result['lean'] = lean_checks(args.lean, args.lean_timeout)
    result['source_hashes'] = {}
    for path in ['lean/Subtail/RegularLanguageGraph.lean',
                 'lean/Subtail/RegularCountermodelProducer.lean',
                 'lean/Subtail/RegularCountermodelProducerAudit.lean',
                 'scripts/check_regular_producer_68.py']:
        data = (ROOT / path).read_bytes()
        result['source_hashes'][path] = {'git_blob': git_blob(data),
                                      'sha256': hashlib.sha256(data).hexdigest()}
    result['elapsed_seconds'] = time.monotonic() - started
    result['python_status'] = 'PASS' if not result['language_checks']['unknown'] else 'UNKNOWN'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'python_status': result['python_status'],
        'nfa_equivalences': result['language_checks']['exact_nfa_equivalences'],
        'literal_equivalences': result['language_checks']['exact_literal_equivalences'],
        'cyclic_models': len(result['model_checks']['periodic_cyclic_models']),
        'lean': result['lean'], 'receipt': str(args.output)}, indent=2))
    return 1 if any(isinstance(x, dict) and x.get('status') == 'FAIL'
                    for x in result['lean'].values()) else 0


if __name__ == '__main__':
    raise SystemExit(main())
