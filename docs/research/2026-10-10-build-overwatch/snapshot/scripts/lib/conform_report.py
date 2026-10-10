"""Strict boundary for Conform reports and fresh producer runs (standard library only)."""
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tempfile

REPORT_FORMAT = "conform-report-v2"


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


def validate(report, process_exit=None, *, expected_tool=None, expected_ids=None,
             expected_pins=None, expected_inputs=None, allow_on_demand=False,
             require_closed=False):
    """Check one report against its own plan, and against the caller's request.

    A report is self-described: its plan, its pins and its inputs are its own. The four
    `expected_*` arguments are the caller's request. A caller builds them from what it asked
    for, never from the report that came back.
    """
    object_keys(report, ("format", "tool", "pins", "inputs", "expected", "required",
                         "summary", "rows"), ("obligations",))
    require(report["format"] == REPORT_FORMAT, "unsupported report format")
    require(isinstance(report["tool"], str) and report["tool"], "missing tool identity")
    if expected_tool is not None:
        require(report["tool"] == expected_tool,
                f"the report names the tool `{report['tool']}`, not `{expected_tool}`")
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


def carries_report_format(path):
    """Whether a file is a JSON object with a report's format tag."""
    try:
        value = json.loads(Path(path).read_text())
    except ValueError:
        return False
    return (isinstance(value, dict) and isinstance(value.get("format"), str)
            and value["format"].startswith("conform-report"))


def retain_attempt(out, destination, record, error):
    """Keep a refused run beside its receipt, and publish nothing of it.

    The folder `attempts/<profile>/` holds the producer's files as it left them (`files/`) and
    `attempt.json`: the command, the exit, the full standard output and standard error, the
    digest of each file and the refusal. It holds the latest refused run of the profile. The
    record's format is not the receipt's, and its `valid` field is false.
    """
    folder = destination.parent / "attempts" / destination.stem
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir(parents=True)
    files = folder / "files"
    os.replace(out, files)
    record["error"] = str(error)
    record["time"] = datetime.now(timezone.utc).isoformat(timespec="seconds")
    record["files"] = {str(p.relative_to(files)): sha256(p)
                       for p in sorted(files.rglob("*")) if p.is_file()}
    (folder / "attempt.json").write_text(json.dumps(record, indent=2) + "\n")
    return folder


def fresh_run(command, destination, reports, artifacts=(), *, cwd, input_snapshot=None):
    """A producer gets an empty directory. Only a validated, unchanged-input run is published.

    COMMAND contains {out} as its output-directory argument. Every output has a declared role.
    REPORTS maps each report file to the tool identity it must carry, and ARTIFACTS names the
    other files. A report is validated, and an artifact is hashed. The role is never read off
    the file: a declared report without the report format is refused, and so is a declared
    artifact that carries it. Exit 2 remains exit 2, including when a profile intentionally has
    unresolved rows.

    A refused run publishes nothing: the earlier receipt stays as it was. `retain_attempt` keeps
    the run's files, command, exit, standard output and standard error for the diagnosis.
    """
    destination = Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    reports, artifacts = dict(reports), list(artifacts)
    names = list(reports) + artifacts
    require(reports, "the profile declares no report")
    require(len(set(names)) == len(names), "the profile names an output twice")
    roles = {**{name: f"report:{tool}" for name, tool in reports.items()},
             **{name: "artifact" for name in artifacts}}
    before = input_snapshot() if input_snapshot else {}
    out = Path(tempfile.mkdtemp(prefix=".conform-", dir=destination.parent))
    record = {"format": "conform-attempt-v1", "valid": False, "command": command,
              "roles": roles, "inputs": before}
    try:
        try:
            completed = subprocess.run([x.replace("{out}", str(out)) for x in command], cwd=cwd,
                                       capture_output=True, text=True)
            record.update(exit=completed.returncode, stdout=completed.stdout,
                          stderr=completed.stderr)
            found = {str(p.relative_to(out)) for p in out.rglob("*") if p.is_file()}
            require(found == set(names),
                    f"producer output set differs: missing {sorted(set(names) - found)}, "
                    f"unexpected {sorted(found - set(names))}; exit {completed.returncode}\n"
                    f"{completed.stderr[-3000:]}")
            statuses, read = [], {}
            for name, tool in reports.items():
                try:
                    value = json.loads((out / name).read_text())
                except ValueError as error:
                    raise InvalidReport(f"{name}: declared a report, and it is not JSON: {error}")
                found_format = value.get("format") if isinstance(value, dict) else None
                require(found_format == REPORT_FORMAT,
                        f"{name}: declared a report, and its format is {found_format!r}, "
                        f"not {REPORT_FORMAT!r}")
                try:
                    statuses.append(validate(value, expected_tool=tool))
                except InvalidReport as error:
                    raise InvalidReport(f"{name}: {error}") from error
                read[name] = value
            for name in artifacts:
                require(not carries_report_format(out / name),
                        f"{name}: declared an artifact, and it carries a report's format")
            require(completed.returncode == max(statuses), "phase exit differs from its reports")
            after = input_snapshot() if input_snapshot else {}
            changed = sorted(k for k in before.keys() | after.keys()
                             if before.get(k) != after.get(k))
            require(not changed, f"inputs changed during execution: {changed[:8]}")
            receipt = {"format": "conform-run-v1", "command": command,
                       "exit": completed.returncode, "inputs": before, "roles": roles,
                       "outputs": {name: sha256(out / name) for name in names},
                       "reports": read, "stdout": completed.stdout, "stderr": completed.stderr}
            generation = hashlib.sha256(json.dumps(receipt["outputs"], sort_keys=True).encode()).hexdigest()
            artifact_folder = destination.parent / "artifacts" / generation
            artifact_folder.parent.mkdir(parents=True, exist_ok=True)
            if not artifact_folder.exists():
                shutil.copytree(out, artifact_folder)
            receipt["artifactDirectory"] = str(artifact_folder)
            temporary = destination.with_suffix(".tmp")
            temporary.write_text(json.dumps(receipt, indent=2) + "\n")
            os.replace(temporary, destination)
            return completed.returncode
        except (InvalidReport, OSError) as error:
            folder = retain_attempt(out, destination, record, error)
            raise InvalidReport(f"{error}\nthe attempt is kept: {folder}") from error
    finally:
        shutil.rmtree(out, ignore_errors=True)
