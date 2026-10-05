#!/usr/bin/env python3
"""Build once, run fresh Conform profiles, validate every result, retain exact run receipts.

    python3 scripts/check-conform.py [PROFILE ...]      default: native

`make check-cases` and `make check-native` run the `cases` and `native` profiles; `compiler`
runs by name (CI's OCaml job). Each profile is a producer that gets an empty directory and
must write exactly its named files. A profile states the role of each file: a report, with
the tool identity it must carry, or an artifact. `conform_report.fresh_run` validates the
reports, refuses an input that changed during the run, and keeps the receipt under
`.lake/conform/`. A refused run publishes nothing: its files, its command and its full output
are kept under `.lake/conform/attempts/<profile>/`.

`compiler` is a Python step of this file (`--step`): one production compiler checkpoint. Lean
writes the requested fixture selection (`selection.json`) and then the emitted OCaml for
normalization. The step compiles that OCaml and runs it against the selection. The
emitted-code mutations follow (`MUTATIONS`), and each must fail the observation that reads it.
The step takes every expectation from the selection: the identities a report must plan, its
pins and its inputs. It never takes one from the report that came back.

The runner's finite controls are `scripts/test-conform-runner.py`. They run without Lean and
without a compiler. The `models`, `types`, `layouts` and `target` profiles were retired on
2026-09-13: receipts of theorems the build already checks, a layout enumeration the wire
theorems and the OCaml lane cover, and a subset of `make check-target`.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/lib"))
from conform_report import InvalidReport, fresh_run, manifest, sha256, validate

SELF = "scripts/check-conform.py"

# Each output of a profile has one role. A report names the tool that must have written it.
PROFILES = {
    "compiler": {
        "command": [sys.executable, SELF, "--step", "compiler", "{out}"],
        "reports": {"normalization.json": "conform.normalization",
                    "validity.json": "conform-lcnf-validity",
                    "ocaml.json": "conform.normalization.ocaml"},
        "artifacts": ["selection.json", "closure.json", "normalization.ml", "expected.txt",
                      "actual.txt", "mutated.ml", "mutated-support.ml", "mutated-contains.ml",
                      "mutation.txt", "processes.json"],
    },
    "native": {
        "command": ["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Effect4/NativeMain.lean", "{out}"],
        "reports": {"layout-lean-native.json": "conform.layout[lean-native]"},
        "artifacts": ["native-layout.json"],
    },
    "cases": {
        "command": ["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Cli/Audit.lean",
                    "--config", "tools/Conform/Effect4/cases.json", "--out", "{out}/cases.json"],
        "reports": {"cases.json": "conform-cases"},
        "artifacts": [],
    },
}

# The emitted-code mutations of the compiler checkpoint. Each alters one definition of the
# emitted prelude and names the first observation that reads the altered definition: the key
# of the handle type whose name is not ASCII, the product of the first name fixture, and the
# membership test under an asymmetric instance, whose two arguments the third one swaps. The
# name is a host fixture of the selection, never a position in a list.
MUTATIONS = [
    {"id": "utf8-mutation", "file": "mutated", "original": "Char.code (String.get s i)",
     "replacement": "0", "fails": {"key/handle-utf8"}},
    {"id": "support-mutation", "file": "mutated-support", "original": "max_int else a * b",
     "replacement": "max_int else a * a", "fails": {"names/mulCap"}},
    {"id": "contains-mutation", "file": "mutated-contains", "original": "(fun e -> inst a e)",
     "replacement": "(fun e -> inst e a)", "fails": {"contains-order"}},
]

SELECTION_FORMAT = "conform-selection-v1"
LANES = ("source", "target", "host")


# ---------------------------------------------------------------- the compiler step

def execute(command):
    """Run one process to its end and return its full result. A nonzero exit is a result."""
    return subprocess.run(command, cwd=ROOT, capture_output=True, text=True)


class Processes:
    """The processes of one step, each with its command and its full result.

    `processes.json` is written after every call, so a step that stops keeps what it ran. The
    output directory is spelled `{out}` in a command: the record does not depend on where the
    run was.
    """

    def __init__(self, out, execute):
        self.out, self.execute, self.calls = Path(out), execute, []

    def run(self, command, check=True):
        result = self.execute(command)
        self.calls.append({"command": [part.replace(str(self.out), "{out}") for part in command],
                           "exit": result.returncode, "stdout": result.stdout,
                           "stderr": result.stderr})
        (self.out / "processes.json").write_text(json.dumps(self.calls, indent=2) + "\n")
        if check and result.returncode:
            raise RuntimeError(f"{command[0]} exited {result.returncode}\n{result.stdout}\n{result.stderr}")
        return result


def read_selection(path):
    """The requested fixture selection, checked for its own shape.

    The producer writes it before it evaluates anything. A fixture has a stable name and the
    lanes it takes part in: the source interpreter, the target evaluator, compiled OCaml.
    """
    try:
        value = json.loads(Path(path).read_text())
    except (OSError, ValueError) as error:
        raise RuntimeError(f"selection.json: {error}")
    keys = {"format", "tool", "pins", "phase", "roots", "fixtures", "controls"}
    if not isinstance(value, dict) or value.keys() != keys:
        raise RuntimeError(f"selection.json: expected an object with the keys {sorted(keys)}")
    if value["format"] != SELECTION_FORMAT:
        raise RuntimeError(f"selection.json: unsupported format {value['format']!r}")
    strings = lambda xs: isinstance(xs, list) and all(isinstance(x, str) and x for x in xs)
    if not (isinstance(value["tool"], str) and isinstance(value["phase"], str)
            and strings(value["roots"]) and strings(value["controls"])):
        raise RuntimeError("selection.json: invalid tool, phase, roots or controls")
    pins = value["pins"]
    if not (isinstance(pins, list) and all(
            isinstance(p, dict) and p.keys() == {"name", "value"}
            and isinstance(p["name"], str) and isinstance(p["value"], str) for p in pins)):
        raise RuntimeError("selection.json: invalid pins")
    fixtures = value["fixtures"]
    if not (isinstance(fixtures, list) and all(
            isinstance(f, dict) and f.keys() == {"name", "lanes"} and isinstance(f["name"], str)
            and f["name"] and not set(f["name"]) & set("\t\n\r") and strings(f["lanes"])
            and f["lanes"] and set(f["lanes"]) <= set(LANES)
            and len(set(f["lanes"])) == len(f["lanes"]) for f in fixtures)):
        raise RuntimeError("selection.json: invalid fixtures")
    for label, names in (("fixture", [f["name"] for f in fixtures]),
                         ("control", value["controls"]), ("pin", [p["name"] for p in pins])):
        if len(set(names)) != len(names):
            raise RuntimeError(f"selection.json: a {label} is named twice")
    return value


def lane(selection, name):
    """The names of the fixtures that take part in one lane, in the selection's order."""
    return [f["name"] for f in selection["fixtures"] if name in f["lanes"]]


def lean_version():
    """The Lean version that the tree pins, read off `lean-toolchain`."""
    return (ROOT / "lean-toolchain").read_text().strip().rsplit(":", 1)[-1].removeprefix("v")


def fixture_ids(check, names):
    return [(check, "fixture", (name,)) for name in names]


def load_report(out, name, **expectations):
    """Validate a report of the step against the request. Any failed row stops the step."""
    try:
        report = json.loads((out / name).read_text())
        status = validate(report, **expectations)
    except (OSError, ValueError) as error:
        raise RuntimeError(f"{name}: {error}")
    if status:
        raise RuntimeError(f"{name}: checkpoint has unresolved or failed rows")
    return report


def first_difference(actual, expected):
    """Where two observation lists part, for the diagnostic of a mismatch."""
    observed, wanted = actual.splitlines(), expected.splitlines()
    for index, (a, e) in enumerate(zip(observed, wanted)):
        if a != e:
            return f"line {index + 1}: observed {a!r}, expected {e!r}"
    if len(observed) < len(wanted):
        return f"the run stopped before {wanted[len(observed)]!r}"
    if len(observed) > len(wanted):
        return f"the run went on with {observed[len(wanted)]!r}"
    return "the lists differ only in their line ends"


def mutation(out, processes, compiler, text, spec, host):
    """Compile an altered copy of the emitted module and run it.

    The alteration must compile. The run must stop with exit 1 at one observation. That
    observation must be one that the mutation names, and it must be a host fixture of the
    selection. The output before it must be the expected prefix. A compiler failure, an
    exception, or a failure of another observation is not the evidence this control asks for.
    """
    name, intended = spec["file"], spec["fails"]
    if not intended <= set(host):
        raise RuntimeError(f"{name}: {sorted(intended - set(host))} is not a host fixture of the selection")
    if text.count(spec["original"]) != 1:
        raise RuntimeError(f"{name}: mutation anchor missing or ambiguous")
    (out / f"{name}.ml").write_text(text.replace(spec["original"], spec["replacement"]))
    processes.run([compiler, "-w", "-a", str(out / f"{name}.ml"), "-o", str(out / name)])
    result = processes.run([str(out / name)], check=False)
    failed = [line.split("\t")[0] for line in result.stderr.splitlines() if line.endswith("\tFAIL")]
    if result.returncode != 1 or len(failed) != 1:
        raise RuntimeError(f"{name}: the mutation did not fail exactly one selected observation (exit {result.returncode})")
    if failed[0] not in intended:
        raise RuntimeError(f"{name}: the mutation failed {failed[0]}, not one of {sorted(intended)}")
    before = host[:host.index(failed[0])]
    if result.stdout != "".join(f"{id}\tPASS\n" for id in before):
        raise RuntimeError(f"{name}: the observations before {failed[0]} differ from the expected prefix")
    return failed[0], result.stderr


def step_compiler(out, execute=execute):
    """One production compiler checkpoint."""
    processes = Processes(out, execute)
    processes.run(["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Effect4/Normalization.lean", str(out)])
    # The request, read before any report. Every expectation below comes from it.
    selection = read_selection(out / "selection.json")
    tools = PROFILES["compiler"]["reports"]
    if selection["tool"] != tools["normalization.json"]:
        raise RuntimeError(f"selection.json: written for the tool {selection['tool']!r}")
    host = lane(selection, "host")
    bound = {"selection": sha256(out / "selection.json")}
    lean = lean_version()
    load_report(out, "normalization.json", expected_tool=tools["normalization.json"],
                expected_ids=fixture_ids("normalization.source", lane(selection, "source"))
                + fixture_ids("normalization.target", lane(selection, "target"))
                + [("normalization.control", "mutation", (c,)) for c in selection["controls"]],
                expected_pins={"lean": lean, **{p["name"]: p["value"] for p in selection["pins"]}},
                expected_inputs=bound)
    # The closure is found by a walk, so no list of its declarations exists before the run. The
    # request names the roots: the walk must start from them, and its report must plan each.
    validity = load_report(out, "validity.json", expected_tool=tools["validity.json"],
                           expected_pins={"lean": lean, "phase": selection["phase"]},
                           expected_inputs=bound)
    planned = {tuple(item["subject"]["path"]) for item in validity["required"]}
    closure = json.loads((out / "closure.json").read_text())
    if closure.get("roots") != selection["roots"] or not all((root,) in planned for root in selection["roots"]):
        raise RuntimeError("validity.json: the closure does not start from the requested roots")
    expected = (out / "expected.txt").read_text()
    if expected != "".join(f"{id}\tPASS\n" for id in host):
        raise RuntimeError("expected.txt differs from the host lane of the selection")
    compiler = os.environ.get("OCAMLOPT") or shutil.which("ocamlopt")
    if shutil.which("opam") and not os.environ.get("OCAMLOPT"):
        compiler = str(Path(processes.run(["opam", "var", "bin", "--switch=effect4"]).stdout.strip()) / "ocamlopt")
    if not compiler:
        raise RuntimeError("ocamlopt is required for the compiler profile")
    processes.run([compiler, "-w", "-a", str(out / "normalization.ml"), "-o", str(out / "normalization")])
    # The observation is written before it is judged: a mismatch keeps what the run printed.
    observed = processes.run([str(out / "normalization")], check=False)
    (out / "actual.txt").write_text(observed.stdout)
    if observed.returncode or observed.stdout != expected:
        raise RuntimeError("compiled OCaml observations differ from the Lean fixture list "
                           f"(exit {observed.returncode}): {first_difference(observed.stdout, expected)}\n{observed.stderr}")
    text = (out / "normalization.ml").read_text()
    failures = [mutation(out, processes, compiler, text, spec, host) for spec in MUTATIONS]
    controls = [spec["id"] for spec in MUTATIONS]
    if len(set(host + controls)) != len(host + controls):
        raise RuntimeError("duplicate host observation ID")
    required = [{"check": "normalization.ocaml", "subject": {"kind": "fixture", "path": [id]}} for id in host]
    rows = [{**item, "outcome": "pass", "evidence": "tested", "message": "actual emitted OCaml observation matched", "detail": None} for item in required]
    for spec, (failed, _) in zip(MUTATIONS, failures):
        item = {"check": "normalization.ocaml.control", "subject": {"kind": "mutation", "path": [spec["id"]]}}
        required.append(item)
        rows.append({**item, "outcome": "pass", "evidence": "tested",
                     "message": f"the altered emitted module fails {failed}",
                     "detail": {"file": f"{spec['file']}.ml", "fails": failed}})
    version = processes.run([compiler, "-version"]).stdout.strip()
    inputs = {**bound, "normalization.ml": sha256(out / "normalization.ml"), "expected.txt": sha256(out / "expected.txt")}
    report = {"format": "conform-report-v2", "tool": tools["ocaml.json"],
              "pins": [{"name": "ocaml", "value": version}],
              "inputs": [{"name": name, "sha256": digest} for name, digest in inputs.items()],
              "expected": len(rows), "required": required, "rows": rows,
              "summary": {"rows": len(rows), "pass": len(rows), "refused": 0, "counterexample": 0, "unresolved": 0, "complete": True, "exit": 0}}
    validate(report, 0, expected_tool=tools["ocaml.json"],
             expected_ids=fixture_ids("normalization.ocaml", host)
             + [("normalization.ocaml.control", "mutation", (id,)) for id in controls],
             expected_pins={"ocaml": version}, expected_inputs=inputs)
    (out / "ocaml.json").write_text(json.dumps(report, indent=2) + "\n")
    (out / "mutation.txt").write_text("".join(stderr for _, stderr in failures))
    for spec in [{"file": "normalization"}] + MUTATIONS:
        for suffix in ["", ".cmi", ".cmx", ".o"]:
            (out / (spec["file"] + suffix)).unlink(missing_ok=True)
    print(f"compiler checkpoint: {len(host)} actual OCaml checks and {len(MUTATIONS)} emitted-code mutations passed")
    return 0


STEPS = {"compiler": step_compiler}


# ---------------------------------------------------------------- the runner

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("profiles", nargs="*", metavar="PROFILE")
    parser.add_argument("--step", choices=sorted(STEPS), help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.step:
        (out,) = args.profiles
        try:
            return STEPS[args.step](Path(out).resolve())
        except (RuntimeError, OSError, ValueError) as error:
            print(error, file=sys.stderr)
            return 2
    args.profiles = args.profiles or ["native"]
    unknown = set(args.profiles) - PROFILES.keys()
    if unknown:
        parser.error(f"unknown profiles: {sorted(unknown)}; choose from {list(PROFILES)}")
    if len(args.profiles) != len(set(args.profiles)):
        parser.error("each profile may be requested only once")
    build = subprocess.run(["lake", "build", "Conform", "Effect4.Laws.Program.Typing.Check"], cwd=ROOT)
    if build.returncode:
        return build.returncode
    worst = 0
    for name in args.profiles:
        profile = PROFILES[name]
        code = fresh_run(profile["command"], ROOT / f".lake/conform/{name}.json", profile["reports"],
                         profile["artifacts"], cwd=ROOT, input_snapshot=lambda: manifest(ROOT))
        label = {0: "PASS", 1: "REFUSED", 2: "UNRESOLVED"}[code]
        print(f"conform {name}: {label}, exit {code}; .lake/conform/{name}.json")
        worst = max(worst, code)
    return worst


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (InvalidReport, ValueError, OSError) as error:
        print(f"conform: INVALID: {error}", file=sys.stderr)
        sys.exit(2)
