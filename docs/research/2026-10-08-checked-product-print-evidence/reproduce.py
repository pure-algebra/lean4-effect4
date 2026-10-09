#!/usr/bin/env python3
"""Finite pinned target controls; catalogue call annotation remains a design experiment."""
import argparse, hashlib, json, pathlib, shutil, subprocess
p = argparse.ArgumentParser()
p.add_argument("--install", required=True, type=pathlib.Path)
p.add_argument("--out", required=True, type=pathlib.Path)
p.add_argument("--helpers-only", action="store_true")
a = p.parse_args()
here = pathlib.Path(__file__).resolve().parent
if a.out.exists():
    raise SystemExit("Output path must be new")
a.out.mkdir(parents=True)
compiler = a.install / "node_modules/.bin/tsgo"

def run(command, folder, stem, expected=0):
    result = subprocess.run(command, cwd=folder, text=True, capture_output=True)
    (a.out / (stem + ".log")).write_text(result.stdout + result.stderr)
    if result.returncode != expected:
        raise SystemExit(f"{stem}: exit {result.returncode}, expected {expected}")
    return result.stdout

compiler_pin = "7.0.0-dev.20260629.1"
compiler_package = json.loads((a.install / "node_modules/@typescript/native-preview/package.json").read_text())
if compiler_package.get("version") != compiler_pin:
    raise SystemExit(f"Unsupported @typescript/native-preview version: {compiler_package.get('version')}")
effect_package = json.loads((a.install / "node_modules/effect/package.json").read_text())
effect_versions = {"4.0.1", "4.0.0-rc.112"} if a.helpers_only else {"4.0.1"}
if effect_package.get("version") not in effect_versions:
    raise SystemExit(f"Unsupported Effect version for this mode: {effect_package.get('version')}")
compiler_version = run([str(compiler), "--version"], a.out, "compiler-version")
if compiler_version.strip() != f"Version {compiler_pin}":
    raise SystemExit(f"Unsupported tsgo executable version: {compiler_version.strip()}")
run(["bun", "--version"], a.out, "runtime-version")
helpers = a.out / "helpers"
helpers.mkdir()
(helpers / "node_modules").symlink_to(a.install / "node_modules", target_is_directory=True)
for name in ["helper-controls.ts", "helper-observe.ts", "helper-tsconfig.json", "prelude-atoms.gen.ts", "literals.typecheck.ts", "records.ts", "tuples.ts"]:
    shutil.copyfile(here / name, helpers / name)
config = json.loads((helpers / "helper-tsconfig.json").read_text())
config["files"] = ["helper-controls.ts", "helper-observe.ts", "literals.typecheck.ts"]
(helpers / "helper-tsconfig.json").write_text(json.dumps(config, indent=2) + "\n")
run([str(compiler), "--project", "helper-tsconfig.json"], helpers, "helper-diagnostics")
observed = json.loads(run(["bun", "helper-observe.ts"], helpers, "helper-observations"))
assert observed == {"values": [7, "seven"], "checkedAndOrdinarySlotsRetained": True, "nestedRefIdentityRetained": True}
packets = {}
for label in ([] if a.helpers_only else ["baseline", "experiment"]):
    folder = a.out / label
    shutil.copytree(here / "catalogue-baseline", folder)
    (folder / "node_modules").symlink_to(a.install / "node_modules", target_is_directory=True)
    if label == "experiment":
        shutil.copyfile(here / "prelude-atoms.gen.ts", folder / "prelude-atoms.gen.ts")
        source = folder / "streamIndependent.ts"
        old = "tuple(a2, a3)"
        new = 'tuple<readonly ["End", void] | readonly ["Chunk", ReadonlyArray<number>], readonly ["End", void] | readonly ["Chunk", ReadonlyArray<number>]>(a2, a3)'
        text = source.read_text()
        assert text.count(old) == 1
        source.write_text(text.replace(old, new))
    output = run([str(compiler), "--project", "tsconfig.json"], folder, "catalogue-" + label + "-diagnostics", 1 if label == "baseline" else 0)
    if label == "baseline":
        assert output.count("error TS2375") == 1 and "streamIndependent.ts" in output
    else:
        observed = json.loads(run(["bun", "observe.ts", str(folder)], folder, "catalogue-experiment-observations"))
        manifest = json.loads((folder / "manifest.json").read_text())
        expected = {case["id"]: case["expected"] for case in manifest["cases"]}
        assert {row["id"]: row["observed"] for row in observed["rows"]} == expected
        assert observed["latest"] == {"stream": [1,2,3], "empty": [], "sync": [5,7], "strings": ["before", "after"]}
        shutil.copyfile(folder / "streamIndependent.ts", a.out / "catalogue-experiment-streamIndependent.ts")
input_names = ["helper-controls.ts", "helper-observe.ts", "helper-tsconfig.json", "prelude-atoms.gen.ts", "literals.typecheck.ts", "records.ts", "tuples.ts", "reproduce.py"]
input_paths = [here / name for name in input_names] + [path for path in (here / "catalogue-baseline").rglob("*") if path.is_file()]
hashes = {str(path.relative_to(here)): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(input_paths)}
for package in ["effect", "@typescript/native-preview"]:
    path = a.install / "node_modules" / package / "package.json"
    hashes[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
(a.out / "input-sha256.json").write_text(json.dumps(hashes, indent=2) + "\n")
print("Pinned helper controls pass." if a.helpers_only else "Pinned helper controls and twelve-case annotated catalogue experiment pass; original packet retains TS2375.")
