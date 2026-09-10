"""Strict boundary for Conform reports and fresh producer runs (standard library only)."""
from collections import Counter
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tempfile


class InvalidReport(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise InvalidReport(message)


def object_keys(value, required, optional=()):
    require(isinstance(value, dict), "expected an object")
    require(set(required) <= value.keys(), f"missing keys: {set(required) - value.keys()}")
    require(value.keys() <= set(required) | set(optional), "unknown keys")


def identity(value):
    object_keys(value, ("check", "subject"))
    require(isinstance(value["check"], str) and value["check"], "invalid check")
    subject = value["subject"]
    object_keys(subject, ("kind", "path"))
    require(isinstance(subject["kind"], str) and subject["kind"], "invalid subject kind")
    require(isinstance(subject["path"], list) and
            all(isinstance(x, str) for x in subject["path"]), "invalid subject path")
    return value["check"], subject["kind"], tuple(subject["path"])


def unique_records(values, value_key):
    require(isinstance(values, list), "expected a record list")
    result = {}
    for entry in values:
        object_keys(entry, ("name", value_key))
        name, value = entry["name"], entry[value_key]
        require(isinstance(name, str) and isinstance(value, str), "invalid named record")
        require(name not in result, f"duplicate record {name}")
        result[name] = value
    return result


def validate(report, process_exit=None, *, expected_ids=None, expected_pins=None,
             expected_inputs=None, allow_on_demand=False, require_closed=False):
    object_keys(report, ("format", "tool", "pins", "inputs", "expected", "required",
                         "summary", "rows"), ("obligations",))
    require(report["format"] == "conform-report-v2", "unsupported report format")
    require(isinstance(report["tool"], str) and report["tool"], "missing tool identity")
    pins = unique_records(report["pins"], "value")
    inputs = unique_records(report["inputs"], "sha256")
    for digest in inputs.values():
        require(len(digest) == 64 and all(c in "0123456789abcdef" for c in digest), "bad digest")
    if expected_pins is not None:
        require(pins == expected_pins, "input profile or toolchain changed")
    if expected_inputs is not None:
        require(inputs == expected_inputs, "input manifest changed")
    require(type(report["expected"]) is int and report["expected"] >= 0, "invalid expected count")
    require(isinstance(report["required"], list), "missing input-domain plan")
    planned = [identity(item) for item in report["required"]]
    require(len(set(planned)) == len(planned), "duplicate planned identity")
    require(len(planned) == report["expected"], "plan/count mismatch")
    if expected_ids is not None:
        require(set(planned) == set(expected_ids), "requested input domain changed")
    require(isinstance(report["rows"], list), "invalid rows")
    seen, counts = [], Counter()
    for row in report["rows"]:
        object_keys(row, ("check", "subject", "outcome", "evidence", "message", "detail"))
        seen.append(identity({k: row[k] for k in ("check", "subject")}))
        outcome = row["outcome"]
        require(outcome in ("pass", "refused", "counterexample", "unresolved"), "bad outcome")
        require(row["evidence"] in ("assumed", "stamped", "tested", "reproduced", "proved"),
                "bad evidence method")
        require(isinstance(row["message"], str), "invalid diagnostic")
        counts[outcome] += 1
        if row["evidence"] == "proved":
            detail = row["detail"]
            require(isinstance(detail, dict) and isinstance(detail.get("theorem"), str)
                    and isinstance(detail.get("proposition"), str), "missing checked proof binding")
            axioms = detail.get("axioms")
            require(isinstance(axioms, list) and set(axioms) <= {"propext", "Quot.sound"},
                    "proof exceeds axiom policy")
        if not allow_on_demand:
            # Availability may be nested inside a compiler-declaration detail.
            def contains_on_demand(value):
                if isinstance(value, dict):
                    return any(contains_on_demand(v) for v in value.values())
                if isinstance(value, list):
                    return any(contains_on_demand(v) for v in value)
                return value == "on-demand"
            require(not contains_on_demand(row["detail"]), "on-demand compilation needs an explicit profile")
    require(len(set(seen)) == len(seen), "duplicate result identity")
    require(set(seen) == set(planned), "missing or unexpected results")
    expected_exit = 2 if counts["unresolved"] else (1 if counts["refused"] or counts["counterexample"] else 0)
    summary = {"rows": len(seen), **{k: counts[k] for k in
               ("pass", "refused", "counterexample", "unresolved")}, "complete": True, "exit": expected_exit}
    object_keys(report["summary"], tuple(summary))
    require(all(type(report["summary"][key]) is int for key in summary if key != "complete")
            and type(report["summary"]["complete"]) is bool, "invalid summary field types")
    require(report["summary"] == summary, "summary does not match results")
    if process_exit is not None:
        require(process_exit == expected_exit, "producer exit disagrees with report")
    obligations = report.get("obligations", [])
    require(isinstance(obligations, list), "invalid obligations")
    for obligation in obligations:
        object_keys(obligation, ("kind", "subject", "status", "dependsOn", "profile", "statement", "detail"))
        identity({"check": obligation["kind"], "subject": obligation["subject"]})
        require(obligation["status"] in ("unproved", "automation-failed", "unsupported", "malformed-input", "refuted"),
                "invalid obligation status")
        require(isinstance(obligation["dependsOn"], list) and all(isinstance(x, str) for x in obligation["dependsOn"])
                and isinstance(obligation["profile"], str) and isinstance(obligation["statement"], str),
                "invalid obligation fields")
    if require_closed:
        require(not obligations, "certificate has open obligations")
    return expected_exit


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def manifest(root):
    """Bind current source, configuration, compiled Lean artifacts and package pins.

    A successful Lake build must precede this snapshot. Source and compiled identities
    are retained separately; a source digest alone is never called a compiled-input receipt.
    """
    root = Path(root)
    files = set()
    for directory in ("src", "tools", "Test", "scripts", "ocaml", "ts", "harness"):
        for folder, directories, names in os.walk(root / directory):
            directories[:] = [d for d in directories if d not in {"node_modules", "_build", ".lake", ".git", "__pycache__"}]
            files.update(Path(folder) / n for n in names if Path(n).suffix in
                         {".lean", ".json", ".jsonl", ".py", ".ts", ".ml", ".sh", ".toml", ".lock"})
    files.update((root / ".lake/build/lib/lean").rglob("*.olean"))
    for package in (root / ".lake/packages").glob("*"):
        files.update((package / ".lake/build/lib/lean").rglob("*.olean"))
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        files.add(root / name)
    return {str(p.relative_to(root)): sha256(p) for p in sorted(files) if p.exists()}


def fresh_run(command, destination, expected_files, *, cwd, input_snapshot=None):
    """A producer gets an empty directory. Only a validated, unchanged-input run is published.

    COMMAND contains {out} as its output-directory argument. Every named output is required;
    JSON reports are recognized by format. Other JSON artifacts are not called reports.
    Exit 2 remains exit 2, including when a profile intentionally has unresolved rows.
    """
    destination = Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    before = input_snapshot() if input_snapshot else {}
    with tempfile.TemporaryDirectory(prefix=".conform-", dir=destination.parent) as scratch:
        out = Path(scratch)
        completed = subprocess.run([x.replace("{out}", str(out)) for x in command], cwd=cwd,
                                   capture_output=True, text=True)
        found = {str(p.relative_to(out)) for p in out.rglob("*") if p.is_file()}
        require(found == set(expected_files), f"producer output set differs: {found ^ set(expected_files)}; exit {completed.returncode}\n{completed.stderr[-3000:]}")
        statuses, reports = [], {}
        for name in expected_files:
            path = out / name
            if path.suffix == ".json":
                value = json.loads(path.read_text())
                if isinstance(value, dict) and "format" in value and value["format"].startswith("conform-report"):
                    statuses.append(validate(value))
                    reports[name] = value
        require(statuses, "producer emitted no reports")
        require(completed.returncode == max(statuses), "phase exit differs from its reports")
        after = input_snapshot() if input_snapshot else {}
        require(before == after, "inputs changed during execution")
        receipt = {"format": "conform-run-v1", "command": command,
                   "exit": completed.returncode, "inputs": before,
                   "outputs": {name: sha256(out / name) for name in expected_files},
                   "reports": reports, "stdout": completed.stdout, "stderr": completed.stderr}
        generation = hashlib.sha256(json.dumps(receipt["outputs"], sort_keys=True).encode()).hexdigest()
        artifacts = destination.parent / "artifacts" / generation
        artifacts.parent.mkdir(parents=True, exist_ok=True)
        if not artifacts.exists():
            shutil.copytree(out, artifacts)
        receipt["artifactDirectory"] = str(artifacts)
        temporary = destination.with_suffix(".tmp")
        temporary.write_text(json.dumps(receipt, indent=2) + "\n")
        os.replace(temporary, destination)
        return completed.returncode
