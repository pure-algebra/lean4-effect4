#!/usr/bin/env python3
"""Replay five exact emitted callers and two failing binding controls; never install packages."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
COMPILER = "7.0.0-dev.20260629.1"
EFFECT = "4.0.0-rc.112"
CASES = ["scalar", "emptyMap", "populatedMap", "mapLookup", "mapKeys"]
MAPS = ["emptyMap", "populatedMap"]
PRELUDE = ["prelude-atoms.gen.ts", "records.ts", "tuples.ts", "control.ts"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--install", type=Path, required=True, help="Existing pinned node_modules")
    parser.add_argument("--out", type=Path, required=True, help="Fresh retained evidence directory")
    parser.add_argument("--skip-build", action="store_true", help="Parent already built Tools.Code.Module")
    args = parser.parse_args()
    install, out = args.install.resolve(), args.out.resolve()
    for package, expected in [("effect", EFFECT), ("@typescript/native-preview", COMPILER)]:
        actual = json.loads((install / package / "package.json").read_text())["version"]
        if actual != expected:
            raise RuntimeError(f"Wrong {package} version: {actual}; expected {expected}")
    if out.exists():
        raise RuntimeError(f"Refuse to overwrite evidence: {out}")
    out.mkdir(parents=True)
    commands = []
    record = {"format": "effect4-codegen-bindings-results-v1", "compiler": COMPILER,
              "effect": EFFECT, "commands": commands, "results": [],
              "limit": "Five emitted callers, structured admission/equality, and finite target typing controls. No execution or emitted-text read-back."}

    def run(name, command, cwd=ROOT):
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                                env={**os.environ, "LEAN_NUM_THREADS": "3"}, timeout=300)
        (out / f"{name}.stdout.log").write_text(result.stdout)
        (out / f"{name}.stderr.log").write_text(result.stderr)
        commands.append({"name": name, "command": [str(x) for x in command], "cwd": str(cwd),
                         "environment": {"LEAN_NUM_THREADS": "3"}, "exitCode": result.returncode,
                         "stdout": result.stdout, "stderr": result.stderr})
        return result

    def require_success(result, label):
        if result.returncode:
            raise RuntimeError(f"{label} failed with exit {result.returncode}")

    def setup(root):
        prelude = root / "prelude"
        prelude.mkdir()
        for name in PRELUDE:
            shutil.copyfile(ROOT / "harness/truth" / name, prelude / name)
        (prelude / "prelude.ts").write_text("".join(f'export * from "./{name}"\n' for name in PRELUDE))
        (root / "node_modules").symlink_to(install, target_is_directory=True)
        config = {"compilerOptions": {"target": "ES2022", "module": "ESNext", "moduleResolution": "Bundler",
                  "strict": True, "noEmit": True, "allowImportingTsExtensions": True,
                  "verbatimModuleSyntax": True, "noUnusedLocals": True, "noUnusedParameters": True,
                  "skipLibCheck": True}, "include": ["corpus/*.ts", "prelude/*.ts"]}
        (root / "tsconfig.json").write_text(json.dumps(config, indent=2) + "\n")

    def compile_case(label, root, expected_names, expected_code=None, expected_count=0):
        corpus = root / "corpus"
        sources = sorted(corpus.rglob("*.ts"))
        expected_files = {name + ".ts" for name in expected_names}
        actual_files = {path.relative_to(corpus).as_posix() for path in sources}
        if not expected_files or actual_files != expected_files:
            raise RuntimeError(f"Wrong compiler input set in {label}: {sorted(actual_files)}")
        for source in sources:
            if not source.read_text().strip():
                raise RuntimeError(f"Empty compiler input: {source}")
        command = compiler + ["--pretty", "false", "--noEmit", "-p", str(root / "tsconfig.json")]
        discovery = run(label + "-discovery", command + ["--listFilesOnly"], root)
        require_success(discovery, label + " discovery")
        discovered = {Path(line).resolve() for line in discovery.stdout.splitlines() if line}
        for source in sources:
            if source.resolve() not in discovered:
                raise RuntimeError(f"Compiler omitted {source}")
        result = run(label, command, root)
        diagnostics = result.stdout + result.stderr
        codes = re.findall(r"error (TS\d+):", diagnostics)
        if expected_code is None:
            require_success(result, label)
            if codes:
                raise RuntimeError(f"Unexpected diagnostics in {label}")
        elif result.returncode == 0 or codes != [expected_code] * expected_count:
            raise RuntimeError(f"Wrong negative diagnostics in {label}: {codes}")
        record["results"].append({"name": label, "exitCode": result.returncode,
                                  "diagnosticCodes": codes, "expectedCode": expected_code})
        return diagnostics

    try:
        compiler = ["node", str(install / "@typescript/native-preview/bin/tsgo")]
        version = run("compiler-version", compiler + ["--version"])
        require_success(version, "Compiler version")
        if version.stdout.strip() != "Version " + COMPILER:
            raise RuntimeError("Compiler binary does not match its pinned manifest")
        record["commit"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        if not args.skip_build:
            require_success(run("build", ["lake", "build", "Tools.Code.Module"]), "Lean dependency build")
        target = out / "target"
        require_success(run("emit", ["lake", "env", "lean", "--run", "harness/codegen-bindings/Emit.lean", str(target)]), "Lean emission")
        manifest = json.loads((target / "manifest.json").read_text())
        if manifest["format"] != "effect4-codegen-bindings-v1" or [c["id"] for c in manifest["cases"]] != CASES:
            raise RuntimeError("Wrong emitted case inventory")
        for case in manifest["cases"]:
            if case["file"] != "corpus/" + case["id"] + ".ts":
                raise RuntimeError(f"Wrong emitted path: {case['id']}: {case['file']}")
            if not case["structuredAdmission"] or not case["sameProgram"] or case["utilityImports"]:
                raise RuntimeError(f"Failed structured check: {case['id']}")
            text = (target / case["file"]).read_text()
            for imported in re.findall(r"\bimport\s+([^;]*?)\s+from\s+[\"']([^\"']+)[\"']", text):
                if imported[1].endswith("/prelude.ts") and re.search(r"\b(Readonly|Record)\b", imported[0]):
                    raise RuntimeError(f"Utility import in emitted text: {case['id']}")
        setup(target)
        compile_case("positive", target, CASES)
        # Copy exact compiler inputs; add only deliberately false imports to the two map files.
        false_imports = out / "false-imports"
        shutil.copytree(target, false_imports, ignore=shutil.ignore_patterns("node_modules"))
        (false_imports / "node_modules").symlink_to(install, target_is_directory=True)
        for name in MAPS:
            path = false_imports / "corpus" / f"{name}.ts"
            path.write_text('import type { Readonly, Record } from "../prelude/prelude.ts"\n' + path.read_text())
        diagnostics = compile_case("false-imports", false_imports, CASES, "TS2305", 4)
        for name in MAPS:
            if len(re.findall(rf"{name}\.ts[^\n]*error TS2305:", diagnostics)) != 2:
                raise RuntimeError(f"Missing paired export refusals for {name}")
        # These globals exist only in type space; using either as a value must fail.
        false_values = out / "false-values"
        false_values.mkdir()
        shutil.copyfile(target / "tsconfig.json", false_values / "tsconfig.json")
        (false_values / "node_modules").symlink_to(install, target_is_directory=True)
        (false_values / "corpus").mkdir()
        for name in ["Readonly", "Record"]:
            (false_values / "corpus" / f"{name}.ts").write_text(f"export const value = {name}\n")
        diagnostics = compile_case("false-values", false_values, ["Readonly", "Record"], "TS2693", 2)
        for name in ["Readonly", "Record"]:
            if not re.search(rf"{name}\.ts[^\n]*error TS2693:", diagnostics):
                raise RuntimeError(f"Missing value-space refusal for {name}")
        record["status"] = "passed"
        print("Five unchanged emitted callers pass; four false imports and two type-as-value uses refuse.")
    except Exception as error:
        record["status"] = "failed"
        record["failure"] = str(error)
        raise
    finally:
        paths = [p for p in out.rglob("*") if p.is_file() and "node_modules" not in p.parts]
        record["outputHashes"] = {str(p.relative_to(out)): digest(p) for p in sorted(paths)}
        sources = ["harness/codegen-bindings/Emit.lean", "harness/codegen-bindings/run.py",
                   "src/Effect4/Codegen/SourceBindings.lean", "src/Effect4/Codegen/ClassTable.lean",
                   "src/Effect4/Codegen/Types.lean", "tools/Tools/Code/Module.lean"]
        record["sourceHashes"] = {name: digest(ROOT / name) for name in sources}
        record["resultHash"] = hashlib.sha256(json.dumps(record["results"], sort_keys=True).encode()).hexdigest()
        (out / "results.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
