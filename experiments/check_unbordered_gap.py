"""Independent bounded checks for C045 unbordered-gap normalization."""
import itertools, json, random
from pathlib import Path


def run(delta, start, word):
    q = start
    states = [q]
    for ch in word:
        q = delta[q][int(ch)]
        if q < 0:
            return None
        states.append(q)
    return tuple(states)


def profile(delta, start, word):
    states = run(delta, start, word)
    if states is None:
        return None
    n = len(word)
    return {(states[i], states[j]) for i in range(n + 1) for j in range(i, n + 1)
            if word[i:].startswith(word[j:])}


def unbordered(word):
    return bool(word) and all(word[:r] != word[-r:] for r in range(1, len(word)))


def string_budget(word):
    n = len(word)
    return min([n] + [n - word.find(word[-m:]) - 1 for m in range(1, n + 1)])


def unique_terminal(word, length):
    return length <= len(word) and word.find(word[-length:]) == len(word) - length


def randomized_theorem_checks():
    rng = random.Random(202609051817)
    counts = {}
    for k in range(3, 8):
        checked = 0
        for _ in range(20000):
            final = k - 1
            delta = [tuple(rng.randrange(-1, k) for _ in range(2)) for _ in range(k - 1)]
            delta.append((-1, -1))
            delta = tuple(delta)
            start = rng.randrange(k - 1)
            for n in range(3, 11):
                word = ''.join(rng.choice('01') for _ in range(n))
                states = run(delta, start, word)
                if states is None or states[-1] != final:
                    continue
                for m in range(1, min(5, n // 2 + 1)):
                    s = word[-m:]
                    if not unbordered(s):
                        continue
                    terminal_start = n - m
                    a = word.find(s)
                    while 0 <= a < terminal_start:
                        if states[a + m] == states[terminal_start]:
                            candidate = word[:a] + s + s
                            if unique_terminal(candidate, m + 1):
                                c = run(delta, start, candidate)
                                assert c is not None and c[-1] == final
                                assert profile(delta, start, candidate) <= profile(delta, start, word)
                                assert string_budget(candidate) <= m
                                checked += 1
                        a = word.find(s, a + 1)
        counts[str(k)] = checked
    return counts


def double_copy_budget_checks():
    checked = 0
    for m in range(1, 9):
        for bits in itertools.product('01', repeat=m):
            s = ''.join(bits)
            if unbordered(s):
                assert unique_terminal(s + s, m + 1)
                assert string_budget(s + s) <= m
                checked += 1
    return checked


def failed_earliest_copy_extension():
    delta = ((1, 2), (2, 1), (3, 2), (-1, -1))
    start = 0
    word = '0101110'
    s = '10'
    a = word.find(s)
    terminal_start = len(word) - len(s)
    states = run(delta, start, word)
    assert a == 1 and terminal_start == 5 and unbordered(s)
    assert states[-1] == 3 and states[a + len(s)] == states[terminal_start]
    candidate = word[:a] + s + s
    new_pairs = sorted(profile(delta, start, candidate) - profile(delta, start, word))
    assert new_pairs == [(0, 1)]
    assert not unique_terminal(candidate, len(s) + 1)
    return {'delta': delta, 'word': word, 'suffix': s, 'earliest_start': a,
            'terminal_start': terminal_start, 'candidate': candidate,
            'new_pairs': new_pairs}


def main():
    result = {
        'status': 'PASS',
        'seed': 202609051817,
        'random_instances_per_k': 20000,
        'applicable_profile_checks_by_k': randomized_theorem_checks(),
        'pure_unbordered_strings_checked': double_copy_budget_checks(),
        'failed_earliest_copy_extension': failed_earliest_copy_extension(),
        'scope': 'bounded validation only; C045 rests on the written proof'
    }
    out = Path(__file__).resolve().parents[1] / 'results' / 'unbordered-gap.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
