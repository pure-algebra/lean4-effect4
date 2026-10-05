#!/usr/bin/env python3
"""Finite mirror of acceptLoop's length behaviour; not a Lean or runtime proof."""
from pathlib import Path
from itertools import product
import hashlib
import json


def accept_loop(room, messages, offers):
    """The finite-room branch, preserving the source's empty-offer and room-zero cases."""
    if not offers:
        return list(messages), []
    first, rest = offers[0], offers[1:]
    if room == 0:
        return list(messages), [list(xs) for xs in offers]
    count = min(room, len(first))
    updated = list(messages) + first[:count]
    left = first[count:]
    if not left:
        return accept_loop(max(0, room - count), updated, rest)
    return updated, [left] + [list(xs) for xs in rest]


def unbounded_append_mutant(room, messages, offers):
    """Deliberate fault: append all offered data despite the finite room."""
    return list(messages) + [x for xs in offers for x in xs], []


def observe(room, messages, offers, implementation=accept_loop):
    out, pending = implementation(room, messages, offers)
    return {"room": room, "messages": messages, "offers": offers,
            "output": out, "pending": pending,
            "bound": len(out) <= len(messages) + room,
            "old_prefix_kept": out[:len(messages)] == messages}


def main():
    named = {
        "empty_offers": observe(3, [90, 91], []),
        "zero_room": observe(0, [90], [[1, 2]]),
        "partial_acceptance": observe(2, [90], [[1, 2, 3], [4]]),
        "several_full_offers": observe(4, [90], [[1], [], [2, 3], [4]]),
        "exact_fill_then_pending": observe(2, [90], [[1], [2], [3]]),
        "empty_pending_offer": observe(1, [], [[], [1], [2]]),
    }
    assert all(x["bound"] and x["old_prefix_kept"] for x in named.values())
    assert named["partial_acceptance"]["pending"] == [[3], [4]]
    assert named["several_full_offers"]["output"] == [90, 1, 2, 3, 4]
    assert named["exact_fill_then_pending"]["pending"] == [[3]]
    checked = 0
    for count in range(4):
        for lengths in product(range(5), repeat=count):
            offers = [[100 * i + j for j in range(n)] for i, n in enumerate(lengths)]
            for room in range(6):
                for initial_length in range(4):
                    observation = observe(room, list(range(initial_length)), offers)
                    assert observation["bound"] and observation["old_prefix_kept"], observation
                    checked += 1
    red = observe(0, [90], [[1]], unbounded_append_mutant)
    assert not red["bound"] and red["old_prefix_kept"]
    script = Path(__file__)
    result = {
        "kind": "finite Python mirror; not Lean compilation, proof or runtime conformance",
        "scope": "finite room, messages represented by integers, at most three pending offers of length zero through four",
        "grid_cases": checked,
        "named_positive_controls": named,
        "unbounded_append_mutant_red": red,
        "source_question": "Can acceptLoop append more messages than its finite room on this bounded domain?",
        "observation": "No witness in the enumerated mirror domain; the deliberate append mutant exceeds the bound.",
        "exclusions": ["source-to-mirror agreement proof", "Lean proof candidate elaboration", "all Queue steps", "signals and answers", "wrapper delivery", "target runtime"],
        "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
    }
    (script.parent / "capacity-mirror.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"grid_cases": checked, "named_controls": len(named),
                      "mutant_rejected": not red["bound"], "kind": result["kind"]}, indent=2))


if __name__ == "__main__":
    main()
