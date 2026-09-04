"""Independent executable definitions for sep-topfree.pdf, Sections 8.1-8.5.

No original memo scripts were available. All strings below are finite words.
The finite-state sandwich search is exact if it exhausts its state graph.
A resource cap returns UNKNOWN, never NO. Standard library only, Python 3.9+.
"""

from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import FrozenSet, Optional, Tuple


@dataclass(frozen=True)
class Instance:
    # delta[state][alphabet index], with -1 meaning undefined.
    delta: Tuple[Tuple[int, ...], ...]
    final: FrozenSet[int]
    flags: FrozenSet[Tuple[int, int]] = frozenset()
    bad: FrozenSet[int] = frozenset()
    start: int = 0
    alphabet: str = "01"

    def run(self, word):
        states = [self.start]
        for a in word:
            q = self.delta[states[-1]][self.alphabet.index(a)]
            if q < 0:
                return None
            states.append(q)
        return tuple(states)

    def admissible(self, word):
        c = self.run(word)
        return c is not None and c[-1] in self.final and not self.bad.intersection(c)


def words(alphabet, max_length):
    for n in range(max_length + 1):
        for letters in product(alphabet, repeat=n):
            yield "".join(letters)


def witness(instance, word):
    """Definition 8.1, directly in forward suffix-agreement form."""
    if not instance.admissible(word):
        return False
    c = instance.run(word)
    n = len(word)
    return not any(
        (c[i], c[j]) in instance.flags and word[i:].startswith(word[j:])
        for i in range(n + 1) for j in range(i, n + 1)
    )


def border_witness(instance, word):
    """Independent reversal/border formulation, including empty/full borders."""
    if not instance.admissible(word):
        return False
    rho, c = word[::-1], instance.run(word)[::-1]
    for m in range(len(rho) + 1):
        for b in range(m + 1):
            if rho[:b] == rho[m-b:m] and (c[m], c[b]) in instance.flags:
                return False
    return True


def necessary(instance, word, L, D):
    if not instance.admissible(word):
        return False
    rho, c = word[::-1], instance.run(word)[::-1]
    for m in range(len(rho) + 1):
        for b in range(m + 1):
            if (b <= L or m-b <= D) and rho[:b] == rho[m-b:m]:
                if (c[m], c[b]) in instance.flags:
                    return False
    return True


def sufficient(instance, word, L, D):
    if not necessary(instance, word, L, D):
        return False
    rho = word[::-1]
    if len(rho) <= L:
        return True
    prefix = rho[:L+1]
    return all(rho[s:s+L+1] != prefix for s in range(D+1, len(rho)-L))


def lrs(word):
    """Longest suffix with an occurrence ending strictly before the word end."""
    return max((k for k in range(1, len(word)) if word[-k:] in word[:-1]), default=0)


def first_end(word, length):
    return 0 if length == 0 else word.index(word[-length:]) + length


def rigid(instance, word):
    if not witness(instance, word):
        return False
    c, n = instance.run(word), len(word)
    return all(c[first_end(word, k)-k] != c[n-k] for k in range(lrs(word)+1))


def suffix_trace_cut(instance, word, end, use_profiles=False):
    """New sufficient truncation criterion; see REVIEW.md for its proof.

    Only the repeated suffix of the proposed shorter word needs to transfer.
    This function checks the criterion, not the resulting witness directly.
    """
    if not 0 <= end < len(word) or not witness(instance, word):
        return False
    c, short = instance.run(word), word[:end]
    h = lrs(short)
    if h and short[-h:] != word[-h:]:
        return False
    if not use_profiles:
        return c[end-h] == c[len(word)-h]
    if c[end] not in instance.final:
        return False
    incoming = [{q for q in range(len(instance.delta)) if (q, r) in instance.flags}
                for r in range(len(instance.delta))]
    return all(incoming[c[end-j]] <= incoming[c[len(word)-j]] for j in range(h+1))


def word_budget(instance, word):
    """Minimum L+D certifying THIS word; not in general the instance budget."""
    if not witness(instance, word):
        return None
    n = len(word)
    return min(L + (n-first_end(word, L+1) if L < n else 0) for L in range(n+1))


@dataclass(frozen=True)
class Memory:
    length: int
    head: str
    head_classes: Tuple[int, ...]
    tail: str
    tail_classes: Tuple[int, ...]
    periods: int


class Sandwich:
    """Finite reverse-reading automaton for N'' or S'' at a fixed L,D."""

    def __init__(self, instance, L, D, strong=False):
        self.I, self.L, self.D, self.strong = instance, L, D, strong
        self.cap = L + D + 2
        self.tail_size = max(L+1, D)
        self.predecessors = {q: [] for q in range(len(instance.delta))}
        for q, row in enumerate(instance.delta):
            for ai, target in enumerate(row):
                if target >= 0:
                    self.predecessors[target].append((instance.alphabet[ai], q))

    def initial(self, final):
        if final in self.I.bad or (final, final) in self.I.flags:
            return None
        return Memory(0, "", (final,), "", (final,), (1 << self.D)-1)

    def step(self, state, letter, q):
        I, L, D = self.I, self.L, self.D
        if q in I.bad or (q, q) in I.flags:
            return None
        if (q, state.head_classes[0]) in I.flags:  # empty border
            return None
        m = min(state.length + 1, self.cap)
        head = (state.head + letter)[:L+1]
        hc = (state.head_classes + (q,))[:L+1]
        tail = state.tail + letter
        tc = state.tail_classes + (q,)
        for b in range(1, min(L, m)+1):
            if head[:b] == tail[-b:] and (q, hc[b]) in I.flags:
                return None
        periods = state.periods
        for d in range(1, D+1):
            mask = 1 << (d-1)
            if periods & mask and m > d and tail[-d-1] != letter:
                periods &= ~mask
            if periods & mask and d <= m and (q, tc[-d-1]) in I.flags:
                return None
        if self.strong and m > L+1+D and tail[-L-1:] == head:
            return None
        return Memory(m, head, hc, tail[-self.tail_size:], tc[-D-1:], periods)

    def accepts(self, word):
        c = self.I.run(word)
        if c is None or c[-1] not in self.I.final:
            return False
        state = self.initial(c[-1])
        for index in range(len(word)-1, -1, -1):
            if state is None:
                return False
            state = self.step(state, word[index], c[index])
        return state is not None and state.tail_classes[-1] == self.I.start

    def search(self, max_states=200000):
        """Returns YES+word, NO after full exhaustion, or UNKNOWN at the cap."""
        parent, queue = {}, deque()
        for f in sorted(self.I.final):
            s = self.initial(f)
            if s is not None:
                parent[s] = None
                queue.append(s)
        while queue:
            s = queue.popleft()
            q = s.tail_classes[-1]
            if q == self.I.start:
                forward = []
                node = s
                while parent[node] is not None:
                    node, letter = parent[node]
                    forward.append(letter)
                return {"status": "YES", "word": "".join(forward), "states": len(parent)}
            for letter, prev in self.predecessors[q]:
                t = self.step(s, letter, prev)
                if t is not None and t not in parent:
                    if len(parent) >= max_states:
                        return {"status": "UNKNOWN", "reason": "state cap", "states": len(parent)}
                    parent[t] = (s, letter)
                    queue.append(t)
        return {"status": "NO", "states": len(parent)}


def fixed_word_instance(n):
    """Only 0^n is accepted; G is empty. Exact budget is n-1 for n>=1."""
    return Instance(tuple((q+1, -1) if q < n else (-1, -1) for q in range(n+1)), frozenset({n}))


def rigid_family():
    return Instance(((1, -1), (1, -1)), frozenset({1}), frozenset({(1, 0)}))


def memo_examples():
    return (
        Instance(((0, 1), (0, 2), (0, 2)), frozenset({2}), frozenset({(0, 1)})),
        Instance(((2, 0), (2, 2), (1, 0)), frozenset({1}), frozenset({(0, 2)})),
    )
