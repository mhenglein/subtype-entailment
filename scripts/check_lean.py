"""Build the Lean core, inspect theorem axioms, and compare it with Python.

The comparisons are finite regression evidence. The Lean theorems, rather than
these examples, establish their stated all-word implications.
"""

import json
from pathlib import Path
import random
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
sys.path.insert(0, str(ROOT / "experiments"))
from border_lab import Instance, border_witness, lrs, witness, words


def run(command):
    completed = subprocess.run(command, cwd=LEAN, text=True, capture_output=True)
    if completed.returncode:
        raise RuntimeError(completed.stdout + completed.stderr)
    return completed.stdout


def boolean(value):
    return "true" if value else "false"


def vector(values):
    return "#v[" + ", ".join(values) + "]"


def word_term(word):
    return "[" + ", ".join(boolean(a == "1") for a in word) + "]"


def instance_term(instance):
    count = len(instance.delta)
    rows = ["(" + ", ".join("none" if q < 0 else "some " + str(q) for q in row) + ")"
            for row in instance.delta]
    fields = [
        "initial := " + str(instance.start),
        "transitions := " + vector(rows),
        "bad := " + vector(boolean(q in instance.bad) for q in range(count)),
        "final := " + vector(boolean(q in instance.final) for q in range(count)),
        "flags := " + vector(vector(boolean((q, r) in instance.flags) for r in range(count))
                             for q in range(count)),
    ]
    return "({ " + ", ".join(fields) + " } : Instance " + str(count) + ")"


def cases(seed, count):
    rng = random.Random(seed)
    for index in range(count):
        k = rng.randrange(1, 6)
        density = (0.0, 0.04, 0.12, 0.25)[index % 4]
        yield Instance(
            tuple(tuple(-1 if rng.random() < .1 else rng.randrange(k)
                        for _ in range(2)) for _ in range(k)),
            frozenset(q for q in range(k) if rng.random() < .5),
            frozenset((q, r) for q in range(k) for r in range(k)
                      if rng.random() < density),
            frozenset(q for q in range(k) if rng.random() < .1),
            start=rng.randrange(k),
        )


def check_axioms(output):
    algorithms = {"witnessCheck", "lrs", "finiteBudgetDecision"}
    theorems = {"witnessCheck_correct", "incomingLe_iff_flags", "lrs_spec",
                "profile_truncation", "visited_profile_truncation",
                "suffix_trace_truncation", "finiteBudgetDecision_correct"}
    found = {}
    for name, empty, listed in re.findall(
            r"'Subtail\.([^']+)' (does not depend on any axioms|depends on axioms: \[([^]]*)\])",
            output):
        axioms = sorted(a.strip() for a in listed.split(",") if a.strip())
        allowed = {"propext", "Quot.sound"}
        if name in theorems:
            allowed.add("Classical.choice")
        if set(axioms) - allowed:
            raise RuntimeError(f"Unexpected axioms in {name}: {axioms}")
        found[name] = axioms
    if set(found) != algorithms | theorems:
        raise RuntimeError(f"Incomplete axiom report: {sorted(found)}")
    return found


def main():
    version = run(["lean", "--version"]).strip()
    if "version 4.33.1," not in version:
        raise RuntimeError("Use the pinned Lean 4.33.1 toolchain: " + version)
    run(["lake", "build"])
    run(["lake", "env", "leanchecker", "Subtail"])
    axioms = check_axioms(run(["lake", "env", "lean", "Subtail/Audit.lean"]))
    seed, count, maximum = 20260904, 80, 6
    lines = [
        "import Subtail", "open Subtail", "set_option maxRecDepth 4096",
        "set_option maxHeartbeats 10000000",
        "def checkWords (I : Instance k) (rows : List (Word × Bool)) : IO Unit := do",
        "  for (w, expected) in rows do",
        "    unless witnessCheck I w == expected do",
        '      throw (IO.userError s!"witness mismatch: {w}")',
    ]
    comparisons = 0
    for index, instance in enumerate(cases(seed, count)):
        rows = []
        for word in words("01", maximum):
            expected = witness(instance, word)
            if expected != border_witness(instance, word):
                raise RuntimeError(f"Python oracle disagreement: {index}, {word}")
            rows.append("(" + word_term(word) + ", " + boolean(expected) + ")")
            comparisons += 1
        lines.append("#eval checkWords " + instance_term(instance) + " [" + ", ".join(rows) + "]")
    lrs_words = list(words("01", 8))
    lines += [
        "def checkSuffixes (rows : List (Word × Nat)) : IO Unit := do",
        "  for (w, expected) in rows do",
        "    unless Subtail.lrs w == expected do",
        '      throw (IO.userError s!"lrs mismatch: {w}")',
        "#eval checkSuffixes [" + ", ".join(
            "(" + word_term(word) + ", " + str(lrs(word)) + ")" for word in lrs_words) + "]",
    ]
    scratch = ROOT / "tmp" / "lean-checks.lean"
    scratch.parent.mkdir(exist_ok=True)
    scratch.write_text("\n".join(lines) + "\n")
    run(["lake", "env", "lean", str(scratch)])
    result = {
        "toolchain": "leanprover/lean4:v4.33.1",
        "kernel_replay": "PASS (bundled leanchecker)",
        "seed": seed,
        "instances": count,
        "max_word_length": maximum,
        "witness_comparisons": comparisons,
        "lrs_comparisons": len(lrs_words),
        "axioms": axioms,
        "failures": 0,
        "scope": "binary BorderAvoid core; conditional budget theorem; no SEP decision procedure",
    }
    (ROOT / "results/lean-checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
