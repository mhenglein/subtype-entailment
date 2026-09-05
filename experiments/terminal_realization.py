"""Word-preserving realization of terminal-final binary BorderAvoid instances.

The construction uses 2*k+1 subtype variables. Every final state must have
no outgoing transition. See the accompanying written proof. It is not an
encoding of unrestricted (nonterminal-final) BorderAvoid.
"""
from dataclasses import dataclass
from typing import Tuple
from border_lab import Instance


def validate(instance: Instance) -> None:
    """Reject malformed automata rather than silently changing their meaning."""
    k = len(instance.delta)
    if k == 0 or instance.alphabet != "01":
        raise ValueError("A nonempty binary automaton over alphabet '01' is required")
    if not isinstance(instance.start, int) or not 0 <= instance.start < k:
        raise ValueError("Invalid initial state")
    if any(len(row) != 2 or any(not isinstance(q, int) or q < -1 or q >= k
                               for q in row) for row in instance.delta):
        raise ValueError("Invalid transition table")
    if any(not isinstance(q, int) or not 0 <= q < k
           for q in set(instance.final) | set(instance.bad)):
        raise ValueError("Invalid annotation state")
    if any(len(pair) != 2 or any(not isinstance(q, int) or not 0 <= q < k
                                 for q in pair) for pair in instance.flags):
        raise ValueError("Invalid flag relation")


@dataclass(frozen=True)
class Realization:
    variables: int
    constraints: Tuple[tuple, ...]
    alpha: int
    beta: int
    bottom: int


def realize(instance: Instance) -> Realization:
    """Construct an always-satisfiable normalized subtype system.

    Variables 0..k-1 are a_q, k..2*k-1 are v_q, and 2*k is bottom.
    Separating paths for a_start <= v_start are exactly the input witnesses.
    """
    validate(instance)
    k = len(instance.delta)
    if any(any(q != -1 for q in instance.delta[f]) for f in instance.final):
        raise ValueError("All accepting states must be terminal")
    b = 2*k
    constraints = [("denial", b)]
    for q, row in enumerate(instance.delta):
        children = tuple(b if r == -1 else r for r in row)
        constraints.append(("upper", q, *children))
        if q not in instance.final:
            copies = tuple(b if r == -1 else k+r for r in row)
            constraints.append(("lower", *copies, k+q))
    constraints.extend(("leq", p, k+q) for p, q in sorted(instance.flags))
    constraints.extend(("denial", q) for q in sorted(instance.bad))
    return Realization(2*k+1, tuple(constraints), instance.start,
                       k+instance.start, b)


def terminal_restriction(instance: Instance) -> Instance:
    """Keep precisely the original safe terminal witnesses.

    Safety here excludes Bad and diagonal-flagged states. This transformation
    is valid for any well-formed instance; absorption is needed only for the
    later terminal/infinite-continuation completeness split.
    """
    validate(instance)
    unsafe = instance.bad | frozenset(p for p, q in instance.flags if p == q)
    delta = tuple(tuple(-1 if q in unsafe or r in unsafe else r for r in row)
                  for q, row in enumerate(instance.delta))
    final = frozenset(q for q in instance.final if q not in unsafe
                      and all(r == -1 for r in delta[q]))
    return Instance(delta, final, instance.flags, unsafe, instance.start)
