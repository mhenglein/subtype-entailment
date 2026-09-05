"""Bounded falsification search for Q003 strict agreement-profile descent."""
import itertools
import json
import random
from pathlib import Path


def run(delta, word):
    q = 0
    states = [q]
    for ch in word:
        q = delta[q][ord(ch) - 48]
        if q < 0:
            return None
        states.append(q)
    return tuple(states)


def profile(word, states):
    n = len(word)
    out = set()
    for j in range(n + 1):
        target = word[j:]
        for i in range(j + 1):
            if word.startswith(target, i):
                out.add((states[i], states[j]))
    return frozenset(out)


def word_budget(word):
    n = len(word)
    return min([n] + [n - word.find(word[-m:]) - 1 for m in range(1, n + 1)])


def main():
    rng = random.Random(202609051748)
    result = {}
    for k, tables, max_length in ((5, 1200, 12), (6, 900, 12), (7, 500, 12)):
        high_targets = 0
        max_target_budget = 0
        counterexamples = []
        examined = 0
        for case in range(tables):
            delta = [tuple(rng.randrange(-1, k) for _ in range(2)) for _ in range(k - 1)]
            delta.append((-1, -1))
            delta = tuple(delta)
            accepted = []
            for n in range(1, max_length + 1):
                for bits in itertools.product('01', repeat=n):
                    word = ''.join(bits)
                    states = run(delta, word)
                    if states is not None and states[-1] == k - 1:
                        accepted.append((word, profile(word, states), word_budget(word)))
            for word, agreement_profile, budget in accepted:
                if budget <= k - 2:
                    continue
                high_targets += 1
                max_target_budget = max(max_target_budget, budget)
                shorter = any(len(v) < len(word) and p <= agreement_profile
                              for v, p, _ in accepted)
                if not shorter:
                    counterexamples.append({
                        'delta': delta,
                        'word': word,
                        'budget': budget,
                        'profile_size': len(agreement_profile),
                    })
                    break
            examined = case + 1
            if counterexamples:
                break
        result[str(k)] = {
            'tables': examined,
            'high_targets': high_targets,
            'max_target_budget': max_target_budget,
            'counterexamples': counterexamples,
        }
        if counterexamples:
            break
    out = Path(__file__).resolve().parents[1] / 'results' / 'profile-descent.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
