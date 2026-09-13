#!/usr/bin/env python3
"""Build once, run fresh Conform profiles, validate every result, retain exact run receipts."""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/lib"))
from conform_report import InvalidReport, fresh_run, manifest

PROFILES = {
    "compiler": ("scripts/check-conform-compiler.py", ["{out}"],
                 ["normalization.json", "validity.json", "closure.json", "normalization.ml", "expected.txt", "actual.txt", "mutated.ml", "ocaml.json", "mutation.txt"]),
    "target": ("scripts/check-conform-target.py", ["{out}"],
               ["target-fixtures.json", "target-oracle.json", "typing-target.json"]),
    "types": ("tools/Conform/Effect4/InspectTypes.lean", ["{out}"], ["types.json", "type-descriptions.json"]),
    "models": ("tools/Conform/Effect4/ModelsMain.lean", ["{out}"], ["models.json"]),
    "native": ("tools/Conform/Effect4/NativeMain.lean", ["{out}"],
               ["layout-lean-native.json", "native-layout.json"]),
    "layouts": ("tools/Conform/Effect4/LayoutMain.lean", ["{out}"],
                ["layout-x2-typescript.json", "layout-x2-typescript-corrected.json", "layout-canonical-wire.json", "layout-ocaml-eff.json"]),
    "cases": ("tools/Conform/Cli/Audit.lean",
              ["--config", "tools/Conform/Effect4/cases.json", "--out", "{out}/cases.json"],
              ["cases.json"]),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profiles", nargs="*", metavar="PROFILE")
    args = parser.parse_args()
    args.profiles = args.profiles or ["models", "native", "types"]
    unknown = set(args.profiles) - PROFILES.keys()
    if unknown:
        parser.error(f"unknown profiles: {sorted(unknown)}; choose from {list(PROFILES)}")
    if len(args.profiles) != len(set(args.profiles)):
        parser.error("each profile may be requested only once")
    build = subprocess.run(["lake", "build", "Conform", "Effect4.Laws.Program.Typing.Check"], cwd=ROOT)
    if build.returncode:
        return build.returncode
    controls = subprocess.run([sys.executable, "scripts/test-conform-report.py"], cwd=ROOT)
    if controls.returncode:
        return controls.returncode
    worst = 0
    for profile in args.profiles:
        source, arguments, files = PROFILES[profile]
        command = [sys.executable, source, *arguments] if source.endswith(".py") else ["lake", "env", "lean", "-M4096", "--run", source, *arguments]
        code = fresh_run(command,
                         ROOT / f".lake/conform/{profile}.json", files, cwd=ROOT,
                         input_snapshot=lambda: manifest(ROOT))
        label = {0: "PASS", 1: "REFUSED", 2: "UNRESOLVED"}[code]
        print(f"conform {profile}: {label}, exit {code}; .lake/conform/{profile}.json")
        worst = max(worst, code)
    return worst


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (InvalidReport, ValueError, OSError) as error:
        print(f"conform: INVALID: {error}", file=sys.stderr)
        sys.exit(2)
