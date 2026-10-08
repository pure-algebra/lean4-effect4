#!/usr/bin/env python3
"""Native comparison for the MODULES revision (finding F5 of the review at 37c1dea4).

Each client is printed twice: over our module (`lib`) and over Effect's own module (`pin`).
The runner type-checks both with the pinned tsgo, runs both on the pinned Effect, and
classifies each client:

- pass: both runs succeed and their results are equal;
- signed: the results differ exactly as a ruled row of `differences.json` predicts;
- candidate: they differ exactly as an unruled row predicts;
- counterexample: they differ and no row predicts the pair;
- refused: a run crashed, printed no result, or the type check failed.

Exit 0 when every client passes or is signed; 2 when one is a candidate or a counterexample;
1 when one is refused. `--self-test` checks the three failure paths in a temporary replica.
Run from the repository root.
"""
from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path.cwd()
HERE = ROOT / "docs/research/2026-10-08-seat-MODULES-r2"
PIN = ROOT / "docs/research/2026-10-08-seat-MODULES/pin"
REVIEW = ROOT / "docs/research/2026-10-08-modules-review"
CLIENTS = {
    "d1": {"lib": PIN / "d1-lib.ts", "pin": PIN / "d1-pin.ts"},
    "d2": {"lib": PIN / "d2-lib.ts", "pin": PIN / "d2-pin.ts"},
    "d3": {"lib": PIN / "d3-lib.ts", "pin": PIN / "d3-pin.ts"},
    "batch": {"lib": REVIEW / "batch-lib.body.ts", "pin": REVIEW / "batch-pin.body.ts"},
    "batch-coalesced": {"lib": HERE / "batch-coalesced-lib.body.ts",
                        "pin": REVIEW / "batch-pin.body.ts"},
}
FOOTER = """const result = await Effect.runPromiseExit(main)
console.log(JSON.stringify(result._tag === "Success"
  ? { _tag: "Success", value: result.value }
  : { _tag: "Failure", cause: String(result.cause) }))
"""


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compare(bodies: dict[str, dict[str, Path]], differences: list[dict]) -> dict:
    report = {"tools": {}, "inputs": {}, "clients": {}}
    report["tools"]["effect"] = json.loads(
        (ROOT / "harness/truth/node_modules/effect/package.json").read_text())["version"]
    report["tools"]["tsgo"] = json.loads(
        (ROOT / "ts/eff/node_modules/@typescript/native-preview/package.json").read_text())["version"]
    report["tools"]["bun"] = subprocess.run(["bun", "--version"], capture_output=True,
                                            text=True, check=True).stdout.strip()
    with tempfile.TemporaryDirectory(prefix="modules-native-") as temp:
        work = Path(temp)
        (work / "node_modules").symlink_to(ROOT / "harness/truth/node_modules",
                                           target_is_directory=True)
        imports = (ROOT / "harness/truth/generated/pDefsOdd.ts").read_text().splitlines()[2:4]
        imports[0] = imports[0].replace("import { Cause,", "import { Latch, Cause,")
        imports[1] = imports[1].replace('"../prelude.ts"',
                                        json.dumps(str(ROOT / "harness/truth/prelude.ts")))
        files = []
        for client, sides in bodies.items():
            for side in ["lib", "pin"]:
                source = sides[side]
                report["inputs"][f"{client}-{side}"] = digest(source)
                target = work / f"{client}-{side}.ts"
                target.write_text("\n".join(imports) + "\n" + source.read_text() + "\n" + FOOTER)
                files.append(target.name)
        config = {"extends": str(ROOT / "harness/truth/tsconfig.json"), "files": files,
                  "include": [], "exclude": []}
        (work / "tsconfig.json").write_text(json.dumps(config))
        tsgo = subprocess.run([str(ROOT / "ts/eff/node_modules/.bin/tsgo"), "--noEmit", "-p",
                               str(work / "tsconfig.json")], capture_output=True, text=True)
        report["typecheck"] = {"exit": tsgo.returncode, "output": tsgo.stdout + tsgo.stderr}
        for client in bodies:
            runs = {}
            for side in ["lib", "pin"]:
                proc = subprocess.run(["bun", "run", str(work / f"{client}-{side}.ts")],
                                      capture_output=True, text=True)
                lines = proc.stdout.strip().splitlines()
                try:
                    value = json.loads(lines[-1]) if proc.returncode == 0 and lines else None
                except json.JSONDecodeError:
                    value = None
                runs[side] = {"exit": proc.returncode, "result": value,
                              "stderr": proc.stderr[-2000:]}
            report["clients"][client] = classify(client, runs, differences, tsgo.returncode)
    return report


def classify(client: str, runs: dict, differences: list[dict], typecheck: int) -> dict:
    ours, effects = runs["lib"]["result"], runs["pin"]["result"]
    row = {"runs": runs}
    if typecheck != 0 or ours is None or effects is None:
        row["outcome"] = "refused"
    elif ours == effects:
        row["outcome"] = "pass"
    else:
        predicted = [d for d in differences
                     if d["client"] == client and d["ours"] == ours and d["effect"] == effects]
        if len(predicted) == 1:
            row["difference"] = predicted[0]["id"]
            row["outcome"] = "signed" if predicted[0].get("ruling") else "candidate"
        else:
            row["outcome"] = "counterexample"
    return row


def exit_code(report: dict) -> int:
    outcomes = [c["outcome"] for c in report["clients"].values()]
    if "refused" in outcomes:
        return 1
    if "candidate" in outcomes or "counterexample" in outcomes:
        return 2
    return 0


def self_test(differences: list[dict]) -> None:
    """Each failure path must be reported: a wrong result, a crash, an unpredicted pair."""
    with tempfile.TemporaryDirectory(prefix="modules-native-self-") as temp:
        copy = Path(temp)
        wrong = {"lib": copy / "wrong-lib.ts", "pin": copy / "wrong-pin.ts"}
        shutil.copyfile(PIN / "d1-pin.ts", copy / "wrong-pin.ts")
        (copy / "wrong-lib.ts").write_text(
            "export const main = Effect.succeed([999] as ReadonlyArray<number>)\n")
        crash = {"lib": copy / "crash-lib.ts", "pin": copy / "crash-pin.ts"}
        shutil.copyfile(PIN / "d1-pin.ts", copy / "crash-pin.ts")
        (copy / "crash-lib.ts").write_text(
            'throw new Error("INJECTED")\nexport const main = Effect.succeed([1])\n')
        wrong_report = compare({"wrong": wrong}, differences)
        assert wrong_report["clients"]["wrong"]["outcome"] == "counterexample", wrong_report
        assert exit_code(wrong_report) == 2
        crash_report = compare({"crash": crash}, differences)
        assert crash_report["clients"]["crash"]["outcome"] == "refused", crash_report
        assert exit_code(crash_report) == 1
        unsigned = [dict(d, ruling=None) for d in differences]
        batch_report = compare({"batch": CLIENTS["batch"]}, unsigned)
        assert batch_report["clients"]["batch"]["outcome"] == "candidate", batch_report
    print("self-test: a wrong result, a crash and an unruled difference are each reported")


def main() -> int:
    differences = json.loads((HERE / "differences.json").read_text())
    if sys.argv[1:] == ["--self-test"]:
        self_test(differences)
        return 0
    report = compare(CLIENTS, differences)
    (HERE / "native-results.json").write_text(json.dumps(report, indent=2) + "\n")
    for client, row in report["clients"].items():
        print(f"{client}: {row['outcome']}  ours {json.dumps(row['runs']['lib']['result'])}"
              f"  Effect's {json.dumps(row['runs']['pin']['result'])}")
    print(f"effect {report['tools']['effect']}, tsgo {report['tools']['tsgo']}, "
          f"bun {report['tools']['bun']}, typecheck exit {report['typecheck']['exit']}")
    return exit_code(report)


if __name__ == "__main__":
    sys.exit(main())
