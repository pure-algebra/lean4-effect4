#!/usr/bin/env python3
"""Native comparison, revision 3 (finding R2-F2 of the review at 59074f2c).

Each client is printed twice: over our module (`lib`) and over Effect's own module (`pin`).
The runner type-checks both with the pinned tsgo, runs both on the pinned Effect, and classifies
each client. Revision 3 corrects the grading:

- equality is typed: two observations agree when their canonical JSON texts are equal, so `true`
  and `1` differ;
- two failures are never equal by their rendered causes: the row is unresolved;
- a signed difference names a decisions row that exists and is ruled in `docs/core/decisions.md`;
- the clients are declared with their expected outcomes; an empty, missing or extra client is
  refused, and so is a difference row that no client uses;
- the pins are enforced, and every run has a time limit.

An expected outcome other than pass is a control: the original Latch's batch client must stay a
counterexample, a regression witness of finding F3.

Exit 0 when every client meets its expected outcome; 1 on a refusal; 2 otherwise.
`--self-test` checks each failure path in a temporary replica. Run from the repository root.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path.cwd()
HERE = ROOT / "docs/research/2026-10-08-seat-MODULES-r3"
PIN = ROOT / "docs/research/2026-10-08-seat-MODULES/pin"
REVIEW = ROOT / "docs/research/2026-10-08-modules-review"
R2 = ROOT / "docs/research/2026-10-08-seat-MODULES-r2"
PINS = {"effect": "4.0.0-rc.112", "tsgo": "7.0.0-dev.20260629.1", "bun": "1.4.2"}
TIMEOUT = 120
CLIENTS = {
    "d1": ({"lib": PIN / "d1-lib.ts", "pin": PIN / "d1-pin.ts"}, "pass"),
    "d2": ({"lib": PIN / "d2-lib.ts", "pin": PIN / "d2-pin.ts"}, "pass"),
    "d3": ({"lib": PIN / "d3-lib.ts", "pin": PIN / "d3-pin.ts"}, "pass"),
    "batch-coalesced": ({"lib": R2 / "batch-coalesced-lib.body.ts",
                         "pin": REVIEW / "batch-pin.body.ts"}, "pass"),
    "batch-original": ({"lib": REVIEW / "batch-lib.body.ts",
                        "pin": REVIEW / "batch-pin.body.ts"}, "counterexample"),
}
FOOTER = """const result = await Effect.runPromiseExit(main)
console.log(JSON.stringify(result._tag === "Success"
  ? { _tag: "Success", value: result.value }
  : { _tag: "Failure", cause: String(result.cause) }))
"""


def canon(value) -> str:
    """The typed identity of an observation: its canonical JSON text."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ruled_rows() -> set[str]:
    """The decisions rows whose status column records a ruling."""
    rows = set()
    for line in (ROOT / "docs/core/decisions.md").read_text().splitlines():
        cells = [c.strip() for c in line.split("|")]
        if len(cells) > 3 and re.fullmatch(r"\d+", cells[1]) and "ruled" in cells[-2].lower():
            rows.add(cells[1])
    return rows


def tools() -> dict:
    found = {
        "effect": json.loads((ROOT / "harness/truth/node_modules/effect/package.json")
                             .read_text())["version"],
        "tsgo": json.loads((ROOT / "ts/eff/node_modules/@typescript/native-preview/package.json")
                           .read_text())["version"],
        "bun": subprocess.run(["bun", "--version"], capture_output=True, text=True,
                              timeout=TIMEOUT, check=True).stdout.strip(),
    }
    return found


def run_bodies(clients: dict, work: Path) -> tuple[dict, dict]:
    (work / "node_modules").symlink_to(ROOT / "harness/truth/node_modules",
                                       target_is_directory=True)
    imports = (ROOT / "harness/truth/generated/pDefsOdd.ts").read_text().splitlines()[2:4]
    imports[0] = imports[0].replace("import { Cause,", "import { Latch, Cause,")
    imports[1] = imports[1].replace('"../prelude.ts"',
                                    json.dumps(str(ROOT / "harness/truth/prelude.ts")))
    inputs, files = {}, []
    for client, (sides, _) in clients.items():
        for side in ["lib", "pin"]:
            inputs[f"{client}-{side}"] = digest(sides[side])
            target = work / f"{client}-{side}.ts"
            target.write_text("\n".join(imports) + "\n" + sides[side].read_text() + "\n" + FOOTER)
            files.append(target.name)
    config = {"extends": str(ROOT / "harness/truth/tsconfig.json"), "files": files,
              "include": [], "exclude": []}
    (work / "tsconfig.json").write_text(json.dumps(config))
    try:
        check = subprocess.run([str(ROOT / "ts/eff/node_modules/.bin/tsgo"), "--noEmit", "-p",
                                str(work / "tsconfig.json")], capture_output=True, text=True,
                               timeout=TIMEOUT)
        typecheck = {"exit": check.returncode, "output": check.stdout + check.stderr}
    except subprocess.TimeoutExpired:
        typecheck = {"exit": None, "output": "timeout"}
    runs = {}
    for client in clients:
        runs[client] = {}
        for side in ["lib", "pin"]:
            try:
                proc = subprocess.run(["bun", "run", str(work / f"{client}-{side}.ts")],
                                      capture_output=True, text=True, timeout=TIMEOUT)
                lines = proc.stdout.strip().splitlines()
                try:
                    value = json.loads(lines[-1]) if proc.returncode == 0 and lines else None
                except json.JSONDecodeError:
                    value = None
                runs[client][side] = {"exit": proc.returncode, "result": value,
                                      "stderr": proc.stderr[-2000:]}
            except subprocess.TimeoutExpired:
                runs[client][side] = {"exit": None, "result": None, "stderr": "timeout"}
    return {"inputs": inputs, "typecheck": typecheck}, runs


def classify(runs: dict, typecheck_ok: bool, rows: list[dict], ruled: set[str]) -> tuple[str, str]:
    ours, effects = runs["lib"]["result"], runs["pin"]["result"]
    if not typecheck_ok or ours is None or effects is None:
        return "refused", "a run crashed, printed no result, or the type check failed"
    if ours.get("_tag") == "Failure" and effects.get("_tag") == "Failure":
        return "unresolved", "two failures: rendered causes are not structured cause equality"
    if canon(ours) == canon(effects):
        return "pass", "equal observations, typed"
    predicted = [r for r in rows if canon(r["ours"]) == canon(ours)
                 and canon(r["effect"]) == canon(effects)]
    if len(predicted) != 1:
        return "counterexample", "unequal observations that no difference row predicts"
    row = predicted[0]
    ruling = row.get("ruling") or ""
    number = re.fullmatch(r"decisions row (\d+)", ruling)
    if number is None:
        return "candidate", f"difference {row['id']} has no ruling"
    if number.group(1) not in ruled:
        return "refused", f"difference {row['id']} names {ruling}, which is not a ruled row"
    return "signed", f"difference {row['id']}, {ruling}"


def compare(clients: dict, differences: list[dict], pins: dict = PINS) -> dict:
    report = {"pins": pins, "tools": tools(), "clients": {}, "refusals": []}
    if report["tools"] != pins:
        report["refusals"].append(f"tools {report['tools']} differ from the pins {pins}")
    if not clients:
        report["refusals"].append("no client is declared")
    for row in differences:
        if row["client"] not in clients:
            report["refusals"].append(f"difference {row['id']} names no declared client")
    ruled = ruled_rows()
    with tempfile.TemporaryDirectory(prefix="modules-native-r3-") as temp:
        meta, runs = run_bodies(clients, Path(temp))
    report.update(meta)
    report["inputs"]["runner"] = digest(Path(__file__))
    report["inputs"]["prelude"] = digest(ROOT / "harness/truth/prelude.ts")
    used = set()
    for client, (_, expected) in clients.items():
        rows = [r for r in differences if r["client"] == client]
        outcome, reason = classify(runs[client], meta["typecheck"]["exit"] == 0, rows, ruled)
        for r in rows:
            if outcome in ("signed", "candidate") and reason.startswith(f"difference {r['id']}"):
                used.add(r["id"])
        report["clients"][client] = {"expected": expected, "outcome": outcome, "reason": reason,
                                     "runs": runs[client]}
    for row in differences:
        if row["id"] not in used:
            report["refusals"].append(f"difference {row['id']} is used by no client")
    return report


def exit_code(report: dict) -> int:
    if report["refusals"] or any(c["outcome"] == "refused" for c in report["clients"].values()):
        return 1
    if any(c["outcome"] != c["expected"] for c in report["clients"].values()):
        return 2
    return 0


def self_test() -> None:
    with tempfile.TemporaryDirectory(prefix="modules-native-r3-self-") as temp:
        copy = Path(temp)

        def body(name: str, text: str) -> Path:
            path = copy / name
            path.write_text(text)
            return path

        typed = "export const main: Effect.Effect<boolean | number, never, never> = Effect.succeed"
        t_true = body("true.ts", f"{typed}(true)\n")
        t_one = body("one.ts", f"{typed}(1)\n")
        crash = body("crash.ts", 'throw new Error("INJECTED")\nexport const main = Effect.succeed(1)\n')
        # true and 1 are unequal observations.
        r = compare({"bool-num": ({"lib": t_true, "pin": t_one}, "pass")}, [])
        assert r["clients"]["bool-num"]["outcome"] == "counterexample", r["clients"]
        assert exit_code(r) == 2
        # A crash is a refusal.
        r = compare({"crash": ({"lib": crash, "pin": t_one}, "pass")}, [])
        assert r["clients"]["crash"]["outcome"] == "refused" and exit_code(r) == 1
        # A ruling that names no ruled row is a refusal.
        fake = [{"id": "fake", "client": "bool-num", "ours": {"_tag": "Success", "value": True},
                 "effect": {"_tag": "Success", "value": 1}, "ruling": "decisions row 99999"}]
        r = compare({"bool-num": ({"lib": t_true, "pin": t_one}, "signed")}, fake)
        assert r["clients"]["bool-num"]["outcome"] == "refused" and exit_code(r) == 1
        # An empty client set is a refusal.
        r = compare({}, [])
        assert exit_code(r) == 1
        # A difference row that no client uses is a refusal.
        stale = [dict(fake[0], id="stale", client="same", ruling=None)]
        r = compare({"same": ({"lib": t_one, "pin": t_one}, "pass")}, stale)
        assert r["clients"]["same"]["outcome"] == "pass" and exit_code(r) == 1
        # Wrong pins are a refusal.
        r = compare({"same": ({"lib": t_one, "pin": t_one}, "pass")}, [],
                    pins=dict(PINS, effect="0.0.0"))
        assert exit_code(r) == 1
    print("self-test: unequal types, a crash, a false ruling, no client, a stale row and wrong "
          "pins are each reported")


def main() -> int:
    if sys.argv[1:] == ["--self-test"]:
        self_test()
        return 0
    differences = json.loads((HERE / "differences.json").read_text())
    report = compare(CLIENTS, differences)
    (HERE / "native-results.json").write_text(json.dumps(report, indent=2) + "\n")
    for client, row in report["clients"].items():
        print(f"{client}: {row['outcome']} (expected {row['expected']})"
              f"  ours {canon(row['runs']['lib']['result'])}"
              f"  Effect's {canon(row['runs']['pin']['result'])}")
    for refusal in report["refusals"]:
        print(f"refused: {refusal}")
    print(f"tools {report['tools']}, typecheck exit {report['typecheck']['exit']}")
    return exit_code(report)


if __name__ == "__main__":
    sys.exit(main())
