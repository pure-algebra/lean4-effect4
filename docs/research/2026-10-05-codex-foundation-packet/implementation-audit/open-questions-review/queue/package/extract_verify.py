#!/usr/bin/env python3
"""Split one retained Queue source, then verify exact bytes. No Lean command runs."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent
EXPECTED = "17910cf6d42ab9782896435e55022b66c1386d21aacf0b2c7ca0bdc0fe30755a"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def prepare():
    raw = (ROOT / "source/QueueContract.lean").read_bytes()
    assert digest(raw) == EXPECTED, "retained source changed"
    src = raw.decode("utf-8")
    anchors = [
        "namespace QueueContract\n",
        "def T (id : Nat)",
        "/-! ## Controls: an unbounded queue has no limit",
        "/-! ## Controls: an offer's acceptance and its answer are two events",
        "/-! ## A bounded exploration",
        "inductive Op\n",
        "def ops : List Op :=",
        "end QueueContract\n",
    ]
    assert all(src.count(a) == 1 for a in anchors), "ambiguous extraction anchor"
    points = [src.index(a) for a in anchors]
    points[0] += len(anchors[0])
    assert points == sorted(points)
    names = ["model_operations", "named_controls_1", "large_named_controls",
             "named_controls_2", "exploration_description", "model_runner", "exploration"]
    fragments = {name: src[a:b] for name, a, b in zip(names, points, points[1:])}
    assert "".join(fragments.values()) == src[points[0]:points[-1]]

    def wrap(description, body, imported=False):
        prefix = "import Test.Program.QueueModel\n\n" if imported else ""
        return (prefix + "/-!\n" + description + "\n"
                "Prepared by byte-preserving extraction; compilation has not been checked.\n"
                "Source: source/QueueContract.lean in the integration packet.\n"
                "-/\n\nnamespace QueueContract\n" + body + "end QueueContract\n").encode()

    outputs = {
        "Test/Program/QueueModel.lean": wrap(
            "The abstract Queue transition model and its diagnostic runner.\n"
            "No effects, wrapper or signal delivery occur here.",
            fragments["model_operations"] + fragments["model_runner"]),
        "Test/Program/QueueContract.lean": wrap(
            "The retained finite named controls, excluding the two million-element controls.",
            fragments["named_controls_1"] + fragments["named_controls_2"], True),
        "retained/QueueLargeControls.lean": wrap(
            "Retained large controls and bounded exploration. No ordinary Test import is proposed.",
            fragments["large_named_controls"] + fragments["exploration_description"]
            + fragments["exploration"], True),
    }
    manifest = {
        "source_sha256": EXPECTED,
        "source_commit": "da41297b95f21b7cfef08b4cb54edf5bf7d8c8b1",
        "source_path": "docs/research/2026-10-05-claude-lead/queue-contract/QueueContract.lean",
        "fragments": [{"name": n, "source_start_char": a, "source_end_char": b,
                       "sha256": digest(src[a:b].encode())}
                      for n, a, b in zip(names, points, points[1:])],
        "outputs": {p: {"sha256": digest(b), "bytes": len(b)} for p, b in outputs.items()},
        "original_guard_count": len(re.findall(r"^#guard\b", src, re.M)),
        "original_eval_count": len(re.findall(r"^#eval\b", src, re.M)),
    }
    return src, outputs, manifest


def verify(outputs, actual):
    errors = []
    for path, expected in outputs.items():
        if path not in actual:
            errors.append("missing: " + path)
        elif actual[path] != expected:
            errors.append("bytes differ: " + path)
    return errors


def main():
    src, outputs, manifest = prepare()
    if sys.argv[1:] == ["--write"]:
        for path, data in outputs.items():
            target = ROOT / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        (ROOT / "provenance.json").write_text(json.dumps(manifest, indent=2) + "\n")
    elif sys.argv[1:] not in ([], ["--verify"]):
        raise SystemExit("use --write or --verify")
    actual = {path: (ROOT / path).read_bytes() for path in outputs if (ROOT / path).exists()}
    errors = verify(outputs, actual)
    assert not errors, errors
    joined = b"".join(actual.values()).decode()
    assert len(re.findall(r"^#guard\b", joined, re.M)) == manifest["original_guard_count"]
    assert len(re.findall(r"^#eval\b", joined, re.M)) == manifest["original_eval_count"]
    model = actual["Test/Program/QueueModel.lean"]
    assert b"#guard" not in model and b"#eval" not in model
    small = actual["Test/Program/QueueContract.lean"]
    assert b"1000000" not in small and b"1000001" not in small
    assert b"def explore" not in small
    changed = dict(actual)
    changed["Test/Program/QueueModel.lean"] = model.replace(
        b"s.capacity.map", b"s.capacity.bind", 1)
    assert changed != actual
    mutation_errors = verify(outputs, changed)
    assert mutation_errors, "body mutation passed"
    missing = dict(actual)
    del missing["Test/Program/QueueContract.lean"]
    missing_errors = verify(outputs, missing)
    assert missing_errors, "missing controls passed"
    result = {
        "status": "byte extraction verified; no Lean compilation",
        "source_sha256": EXPECTED,
        "positive": "all prepared sources exactly match their extracted ranges and wrappers",
        "body_mutation_red": mutation_errors,
        "missing_controls_red": missing_errors,
        "guards_preserved": manifest["original_guard_count"],
        "evals_preserved": manifest["original_eval_count"],
        "default_controls_have_large_evaluation": False,
        "model_has_evaluation_commands": False,
        "outputs": manifest["outputs"],
    }
    (ROOT / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
