#!/usr/bin/env python3
"""Independent bounded checks for the graph-only first-return note.

Standard library only; imports no repository compiler or prefix-graph code.
This is NOT a full implementation/enumeration of the uniform preimage compiler.
Literal word graphs, relational edge surgery, product BFS, and a separate
finite interval product are compared on the exact recorded finite corpora.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
import itertools
import json
from pathlib import Path
import platform
import random
from typing import Callable, Hashable, Iterable

BASE = "19b06d4fed9da635d9b911f0e908d04e4fc4b099"
SEED = 2026092072
LABELS = ("F", "S", "K0", "K1")
Colour = Hashable


@dataclass(frozen=True)
class Graph:
    colours: tuple[Colour, ...]
    edges: frozenset[tuple[int, str, int]]

    def successors(self, v: int, label: str) -> tuple[int, ...]:
        return tuple(sorted(y for x, lab, y in self.edges if x == v and lab == label))


@dataclass(frozen=True)
class Observer:
    size: int
    initial: tuple[int, ...]
    final: frozenset[int]
    allows: Callable[[int, Colour], bool]
    move: Callable[[int, Colour, str, Colour], tuple[int, ...]]


def exact(labels: Iterable[str], allow: Callable[[int, Colour], bool] | None = None) -> Observer:
    word = tuple(labels)
    return Observer(len(word) + 1, (0,), frozenset({len(word)}),
                    allow or (lambda _s, _c: True),
                    lambda s, _c, lab, _d: (s + 1,) if s < len(word) and lab == word[s] else ())


def path(g: Graph, o: Observer, source: int, target: int):
    """BFS in the literal vertex/control product; return a simple product run."""
    pred = {}
    todo = deque()
    adj = {}
    for x, lab, y in sorted(g.edges):
        adj.setdefault(x, []).append((lab, y))
    for s in o.initial:
        if o.allows(s, g.colours[source]):
            pred[(source, s)] = None
            todo.append((source, s))
    while todo:
        node = todo.popleft()
        x, s = node
        if x == target and s in o.final:
            nodes, labs = [node], []
            while pred[node] is not None:
                node, lab = pred[node]
                nodes.append(node)
                labs.append(lab)
            return list(reversed(nodes)), list(reversed(labs))
        for lab, y in adj.get(x, ()):
            for t in o.move(s, g.colours[x], lab, g.colours[y]):
                nxt = (y, t)
                if o.allows(t, g.colours[y]) and nxt not in pred:
                    pred[nxt] = (node, lab)
                    todo.append(nxt)
    return None


def borders(word: str) -> list[int]:
    return [j for j in range(len(word) + 1) if not j or word[:j] == word[-j:]]


def column(flags: int, q: int, k: int) -> int:
    return sum(1 << p for p in range(k) if flags & (1 << (p * k + q)))


def literal_graph(word: str, states: tuple[int, ...], flags: int, k: int) -> Graph:
    """Definition from literal equality of prefixes and suffixes, no KMP recurrence."""
    assert len(states) == len(word) + 1
    n, cols, edges = len(word), [], set()
    for j in range(n + 1):
        bs = borders(word[:j])
        mask = 0
        for b in bs:
            mask |= column(flags, states[b], k)
        cols.append((states[j], mask, word[j] if j < n else None, j == 0, j == n))
        parent = max((b for b in bs if b < j), default=0)
        edges.add((j, "F", parent))
        if j < n:
            edges.add((j, "S", j + 1))
        for a in "01":
            text = word[:j] + a
            matches = [b for b in range(n + 1) if not b or text.endswith(word[:b])]
            edges.add((j, "K" + a, max(matches)))
    return Graph(tuple(cols), frozenset(edges))


def first_return(base: str, full: str) -> bool:
    m = len(base)
    return (m > 0 and full.startswith(base) and len(full) > m and full.endswith(base)
            and all(full[j-m:j] != base for j in range(m + 1, len(full))))


def rho(a: str, c: tuple) -> tuple:
    q, mask, nxt, root, end = c
    return (q, mask, a, root, False) if end else c


def extension(base: Graph, emitted: str, origins: tuple[int, ...], states: tuple[int, ...],
              flags: int = 0, k: int = 1) -> Graph:
    """Relational-copy surgery. Validate one entire decorated origin trace."""
    ends = [i for i, c in enumerate(base.colours) if c[4]]
    assert len(ends) == 1 and emitted
    e, m, length = ends[0], len(base.colours), len(emitted)
    assert len(origins) == length + 1 and len(states) == length
    assert (e, "F", origins[0]) in base.edges
    assert all((origins[i], "K" + a, origins[i+1]) in base.edges for i, a in enumerate(emitted))
    assert all(h != e for h in origins[1:-1]) and origins[-1] == e
    cols = [rho(emitted[0], c) for c in base.colours]
    edges = {(x, lab, y) for x, lab, y in base.edges
             if not (x == e and lab in ("S", "K" + emitted[0]))}
    edges.update({(e, "S", m), (e, "K" + emitted[0], m)})
    for i, q in enumerate(states):
        v, h = m + i, origins[i+1]
        nxt = emitted[i+1] if i + 1 < length else None
        cols.append((q, base.colours[h][1] | column(flags, q, k), nxt, False, nxt is None))
        edges.add((v, "F", h))
        matching = nxt if nxt is not None else emitted[0]
        if nxt is not None:
            edges.update({(v, "S", v+1), (v, "K" + matching, v+1)})
        else:
            edges.add((v, "K" + matching, m))
        for a in "01":
            if a != matching:
                edges.update((v, "K" + a, y) for y in base.successors(h, "K" + a))
    return Graph(tuple(cols), frozenset(edges))


def trace(base: Graph, emitted: str) -> tuple[int, ...]:
    e = next(i for i, c in enumerate(base.colours) if c[4])
    h = base.successors(e, "F")[0]
    hs = [h]
    for a in emitted:
        h = base.successors(h, "K" + a)[0]
        hs.append(h)
    return tuple(hs)


def safe_graph(g: Graph, bad: int) -> bool:
    return all(not (bad & (1 << c[0])) and not (c[1] & (1 << c[0])) for c in g.colours)


def blocks(run, old_size: int):
    """Maximal old blocks / forward-adjacent fresh blocks; portals separate them."""
    nodes, labs = run
    assert len(nodes) == len(set(nodes))
    answer = []
    start = 0
    for i, lab in enumerate(labs):
        x, y = nodes[i][0], nodes[i+1][0]
        same = ((x < old_size and y < old_size) or
                (x >= old_size and y == x + 1 and lab in ("S", "K0", "K1")))
        if not same:
            answer.append((nodes[start][0] >= old_size, start, i))
            start = i + 1
    answer.append((nodes[start][0] >= old_size, start, len(nodes) - 1))
    return answer


def word_checks(rng: random.Random) -> dict:
    counts = dict(first_return_pairs=0, coloured_graph_equalities=0,
                  safe_base_equivalences=0, valid_reverse_run_annotations=0,
                  overlaps=0, singleton_returns=0, alias_traces=0)
    for n in range(2, 8):
        for bits in itertools.product("01", repeat=n):
            full = "".join(bits)
            for m in range(1, min(3, n-1) + 1):
                word = full[:m]
                if not first_return(word, full):
                    continue
                counts["first_return_pairs"] += 1
                counts["overlaps"] += int(n - m < m)
                counts["singleton_returns"] += int(n - m == 1)
                for mode in range(3):
                    k = 3
                    qs = tuple(0 if mode == 0 else rng.randrange(k) for _ in range(n+1))
                    flags = 0 if mode == 0 else rng.randrange(1 << (k*k))
                    bad = 0 if mode == 0 else rng.randrange(1 << k)
                    old = literal_graph(word, qs[:m+1], flags, k)
                    expected = literal_graph(full, qs, flags, k)
                    hs = trace(old, full[m:])
                    actual = extension(old, full[m:], hs, qs[m+1:], flags, k)
                    assert actual == expected, (word, full, qs, flags)
                    counts["coloured_graph_equalities"] += 1
                    counts["alias_traces"] += int(len(set(hs[1:])) < len(hs[1:]))
                    delta, consistent = {}, True
                    for j, a in enumerate(full):
                        key = (qs[j+1], a)
                        if key in delta and delta[key] != qs[j]:
                            consistent = False
                        delta[key] = qs[j]
                    counts["valid_reverse_run_annotations"] += int(consistent)
                    local = all(not (bad & (1 << q)) and not (flags & (1 << (q*k+q)))
                                and not (old.colours[h][1] & (1 << q))
                                for q, h in zip(qs[m+1:], hs[1:]))
                    if safe_graph(old, bad):
                        assert safe_graph(expected, bad) == local
                        counts["safe_base_equivalences"] += 1
    return counts


def generators(g: Graph, cap: int):
    e = next(i for i, c in enumerate(g.colours) if c[4])
    todo = [("", (h,)) for h in g.successors(e, "F")]
    while todo:
        word, hs = todo.pop()
        if len(word) == cap:
            continue
        for a in "01":
            for h in g.successors(hs[-1], "K" + a):
                item = word + a, hs + (h,)
                if h == e:
                    yield item
                else:
                    todo.append(item)


def random_observer(g: Graph, s: int, rng: random.Random) -> Observer:
    colours = sorted(set(g.colours), key=repr)
    allowed = {(q, c) for q in range(s) for c in colours if rng.randrange(5)}
    moves = {(q, c, lab, d): tuple(t for t in range(s) if rng.randrange(4) == 0)
             for q in range(s) for c in colours for lab in LABELS for d in colours}
    return Observer(s, (0,), frozenset({s-1}), lambda q, c: (q, c) in allowed,
                    lambda q, c, l, d: moves.get((q, c, l, d), ()))


def relational_bounds(rng: random.Random) -> dict:
    count = dict(bases=40, generated_extensions=0, endpoint_tests=0, accepted_product_paths=0,
                 empty_paths=0, joint_mark_checks=0, nonfunctional_bases=0)
    for _ in range(count["bases"]):
        edges = {(x, lab, y) for x in range(3) for lab in LABELS for y in range(3)
                 if rng.randrange(4) == 0}
        edges.add((2, "F", 0))
        old = Graph(tuple((i, 0, None, False, i == 2) for i in range(3)), frozenset(edges))
        count["nonfunctional_bases"] += int(any(len(old.successors(x, lab)) > 1
                                               for x in range(3) for lab in LABELS))
        chosen = list(itertools.islice(generators(old, 4), 3))
        for word, hs in chosen:
            g = extension(old, word, hs, (0,) * len(word))
            count["generated_extensions"] += 1
            for s in (1, 2, 3, 4):
                obs = random_observer(g, s, rng)
                accepted = []
                for source in range(len(g.colours)):
                    for target in range(len(g.colours)):
                        count["endpoint_tests"] += 1
                        run = path(g, obs, source, target)
                        if run is None:
                            continue
                        count["accepted_product_paths"] += 1
                        count["empty_paths"] += int(not run[1])
                        parts = blocks(run, 3)
                        assert sum(f for f, _, _ in parts) <= s + 1
                        assert sum(not f for f, _, _ in parts) <= s + 2
                        accepted.append(run)
                if len(accepted) >= 2:
                    selected = accepted[0], accepted[-1]
                    marks = {3, len(g.colours)-1}
                    for run in selected:
                        for fresh, left, right in blocks(run, 3):
                            if fresh:
                                marks.update({run[0][left][0], run[0][right][0]})
                        marks.update(v for v, _q in (run[0][0], run[0][-1]) if v >= 3)
                    # Two atoms, four endpoint-variable roles; repeated controls count twice.
                    assert len(marks) <= 2 + 4 + 2*2 + 2*(s+s)
                    count["joint_mark_checks"] += 1
    return count


def interval_product(g: Graph, observers: tuple[Observer, ...], source: int, target: int,
                     max_steps: int, positive: bool = True) -> bool:
    """Independent synchronous interval primitive, finite length cap for this test.

    The generator has one control; next letters are selected by actual base edges.
    Colour input is the actual shared origin colour. Repeated observer occurrences
    remain separate coordinates. End has no outgoing generator step.
    """
    initials = itertools.product(*(o.initial for o in observers))
    todo = deque((source, tuple(ps), 0) for ps in initials
                 if all(o.allows(p, g.colours[source]) for o, p in zip(observers, ps)))
    seen = set(todo)
    while todo:
        x, ps, length = todo.popleft()
        if (x == target and (length > 0 or not positive)
                and all(p in o.final for o, p in zip(observers, ps))):
            return True
        if length == max_steps or g.colours[x][4]:
            continue
        for a in "01":
            for y in g.successors(x, "K" + a):
                choices = []
                for o, p in zip(observers, ps):
                    choices.append(tuple(sorted(set(t for lab in ("S", "K" + a)
                                                     for t in o.move(p, g.colours[x], lab, g.colours[y])
                                                     if o.allows(t, g.colours[y])))))
                for ts in itertools.product(*choices):
                    item = y, tuple(ts), length + 1
                    if item not in seen:
                        seen.add(item)
                        todo.append(item)
    return False


def literal_interval(g: Graph, observers: tuple[Observer, ...], source: int, target: int,
                     cap: int) -> bool:
    """Enumerate actual origin walks, build each physical strip, evaluate observers."""
    todo = [(source, (), (source,))]
    while todo:
        x, word, vertices = todo.pop()
        if word and x == target:
            edges = set()
            for i, a in enumerate(word):
                edges.update({(i, "S", i+1), (i, "K" + a, i+1)})
            strip = Graph(tuple(g.colours[v] for v in vertices), frozenset(edges))
            if all(path(strip, o, 0, len(vertices)-1) is not None for o in observers):
                return True
        if len(word) == cap or g.colours[x][4]:
            continue
        for a in "01":
            for y in g.successors(x, "K" + a):
                todo.append((y, word + (a,), vertices + (y,)))
    return False


def interval_checks(rng: random.Random) -> dict:
    counts = dict(comparisons=0, positive=0, negative=0, zero_coordinate_cases=0)
    for _ in range(30):
        edges = frozenset((x, "K"+a, y) for x in range(3) for a in "01" for y in range(3)
                          if rng.randrange(3) == 0)
        g = Graph(tuple((i, 0, None, False, i == 2) for i in range(3)), edges)
        for active_count in (0, 1, 2, 3):
            obs = tuple(random_observer(g, 2, rng) for _ in range(active_count))
            for source in (0, 1):
                for target in range(3):
                    left = interval_product(g, obs, source, target, 4)
                    right = literal_interval(g, obs, source, target, 4)
                    assert left == right, (g, active_count, source, target)
                    counts["comparisons"] += 1
                    counts["positive" if left else "negative"] += 1
                    counts["zero_coordinate_cases"] += int(active_count == 0)
    return counts


def fixtures() -> dict:
    out = {}
    # Joint first-return query: root-to-end S-length 2 versus S-length 3.
    witnesses = {2: [], 3: [], "joint": []}
    for n in range(9):
        word = "0" + "1" * n + "0"
        g = literal_graph(word, (0,) * (len(word)+1), 0, 1)
        ok = {k: path(g, exact(["S"]*k), 0, len(word)) is not None for k in (2, 3)}
        for k in (2, 3):
            if ok[k]:
                witnesses[k].append(word)
        if all(ok.values()):
            witnesses["joint"].append(word)
    assert witnesses == {2: ["00"], 3: ["010"], "joint": []}
    out["shared_extension"] = {str(k): v for k, v in witnesses.items()}

    g = literal_graph("010", (0,)*4, 0, 1)
    run = path(g, exact(("S", "K1", "S")), 2, 3)
    assert run and run[1] == ["S", "K1", "S"]
    assert sum(f for f, _, _ in blocks(run, 2)) == 2
    out["repeated_interval"] = {"word": "010", "run": run, "coordinates_required": 2}
    old = literal_graph("0", (0, 0), 0, 1)
    hs = trace(old, "110")
    assert hs[1] == hs[2] == 0
    out["distinct_marks_equal_origins"] = {"word": "0110", "origins": hs,
                                           "fresh_positions": [2, 3, 4]}

    g = literal_graph("00", (0,)*3, 0, 1)
    assert path(g, exact(("K0",)), 2, 2) is not None
    assert path(g, exact(()), 2, 2) is not None
    assert path(g, exact((), lambda _q, _c: False), 2, 2) is None
    assert path(g, exact(()), 1, 2) is None
    out["singleton_empty_and_equality"] = "PASS: loop, empty allowed, disallowed empty, distinct endpoints"
    assert first_return("00", "000")
    later = literal_graph("000", (0,)*4, 0, 1)
    assert (3, "F", 2) in later.edges and (3, "F", 1) not in later.edges
    out["later_return_surgery_counterexample"] = {"base": "0", "later_word": "000", "actual_F": [3,2], "wrong_F": [3,1]}

    # Two real successors copied into ONE relational extension.
    rb = Graph(((0,0,None,False,False), (0,0,None,False,True)),
               frozenset({(1,"F",0),(0,"K0",0),(0,"K0",1),(1,"K1",0),(1,"K1",1)}))
    rg = extension(rb, "0", (0,1), (0,))
    assert path(rg, exact(("K1",)), 2, 0) and path(rg, exact(("K1",)), 2, 1)
    out["relational_exits"] = {"fresh_vertex": 2, "distinct_targets": list(rg.successors(2,"K1"))}

    # Unsafe old reference cannot be repaired by local fresh safety.
    old_bad = literal_graph("00", (0,1,2), 0, 4)
    new_bad = literal_graph("000", (0,1,2,3), 0, 4)
    assert not safe_graph(old_bad, 1 << 1) and not safe_graph(new_bad, 1 << 1)
    assert not (old_bad.colours[2][1] & (1 << 3)) and not ((1 << 1) & (1 << 3))
    out["old_safety_premise"] = "PASS: fresh q safe, old bad persists"

    # Extra entrances: fixed p=2 violates old s+1, obeys p*s+1.
    two = Graph(tuple(range(5)), frozenset({(4,"F",0),(0,"J",2),(2,"F",1),
                                           (1,"J",3),(2,"S",3),(3,"S",4)}))
    one_control = Observer(1,(0,),frozenset({0}),lambda _s,_c:True,
                           lambda _s,_c,l,_d:(0,) if l in ("F","J") else ())
    run = path(two, one_control, 4, 3)
    assert run
    fresh_count = sum(f for f, _, _ in blocks(run, 2))
    assert fresh_count == 3 and fresh_count > 1+1 and fresh_count <= 2*1+1
    out["two_entrances"] = {"observer_controls": 1, "fresh_blocks": fresh_count, "p":2}
    many = []
    for n in range(1, 13):
        old_size = n+1
        edges = {(i-1,"J",old_size+i-1) for i in range(1,n+1)}
        edges |= {(old_size+i-1,"F",i) for i in range(1,n+1)}
        edges |= {(old_size+i,"S",old_size+i+1) for i in range(n-1)}
        chain = Graph(tuple(range(2*n+1)), frozenset(edges))
        jf = Observer(2,(0,),frozenset({0}),lambda _s,_c:True,
                      lambda s,_c,l,_d:(1-s,) if (s,l) in ((0,"J"),(1,"F")) else ())
        run = path(chain,jf,0,n)
        assert run
        fresh_count = sum(f for f,_,_ in blocks(run, old_size))
        assert fresh_count == n
        many.append([n,fresh_count,len(run[1])])
    out["unbounded_entrance_family"] = many

    inverse = []
    move = {(0,"S"):(1,3),(1,"S"):(2,),(2,"Sbar"):(0,)}
    inv = Observer(4,(0,),frozenset({3}),lambda _s,_c:True,
                   lambda s,_c,l,_d:move.get((s,l),()))
    for length in range(2, 13):
        chain = Graph(tuple(range(length)), frozenset(
            {(i,"S",i+1) for i in range(length-1)} |
            {(i+1,"Sbar",i) for i in range(length-1)}))
        run = path(chain, inv, 0, length-1)
        assert run and len(run[0]) == len(set(run[0]))
        backward = run[1].count("Sbar")
        forward_blocks = sum(f for f,_,_ in blocks(run, 0))
        assert backward == length-2 and forward_blocks == length-1
        inverse.append([length,backward,forward_blocks])
    out["inverse_S_family"] = inverse

    # Same emitted word, incompatible origin-colour observations of its middle.
    diamond = Graph(((0,0,None,False,False),(1,0,None,False,False),
                     (2,0,None,False,False),(3,0,None,False,True)),
                    frozenset({(0,"K1",1),(0,"K1",2),(1,"K0",3),(2,"K0",3)}))
    red = exact(("S","S"), lambda s,c: s != 1 or c[0] == 1)
    blue = exact(("S","S"), lambda s,c: s != 1 or c[0] == 2)
    assert interval_product(diamond,(red,),0,3,2)
    assert interval_product(diamond,(blue,),0,3,2)
    assert not interval_product(diamond,(red,blue),0,3,2)
    out["same_word_different_origin_traces"] = {"word":"10", "each_alone":True, "joint":False}

    # Positivity, End guard, and generator retention with no observer coordinates.
    loop = Graph(((0,0,None,False,False),(0,0,None,False,True)),
                 frozenset({(0,"K1",0),(0,"K0",1),(1,"K1",0)}))
    epsilon = exact(())
    assert not interval_product(loop,(epsilon,),0,0,3)
    assert interval_product(loop,(epsilon,),0,0,3,positive=False)
    assert interval_product(loop,(),0,0,3)
    assert not interval_product(loop,(),1,0,3)
    no_edges = Graph(loop.colours, frozenset())
    assert not interval_product(no_edges,(),0,1,3)
    out["interval_mutation_traps"] = "PASS: zero interval, leave End, no-observation/no-generator"
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write deterministic JSON (otherwise stdout).")
    args = parser.parse_args()
    rng = random.Random(SEED)
    result = {
        "status": "PASS", "base_revision": BASE, "seed": SEED,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "python": platform.python_version(),
        "scope": "Independent bounded graph/interval checks; NOT full Pre_T enumeration or Lean verification",
        "bounds": {"binary_base_length_max":3,"binary_full_word_length_max":7,
                   "relational_base_count":40,"relational_base_vertices":3,
                   "generator_length_max":4,"generators_per_base_max":3,
                   "observer_sizes":[1,2,3,4],"interval_walk_length_max":4},
        "word_surgery": word_checks(rng),
        "relational_bounds": relational_bounds(rng),
        "interval_products": interval_checks(rng),
        "fixtures": fixtures(),
        "review_status": "Author checks only; independent mathematical review of generalized theorem pending",
        "limits": ["No repository modules imported", "No full compiler implemented or exhausted",
                   "No all-input claim derived from finite counts", "No Lean build or repository CI executed",
                   "All-length fixture conclusions are ordinary arguments in the accompanying note"]
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
