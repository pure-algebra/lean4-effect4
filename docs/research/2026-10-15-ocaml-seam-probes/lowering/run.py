#!/usr/bin/env python3
"""Compile isolated controls and retain exact diagnostics and source hashes."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import tempfile
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def execute(command, directory):
    proc = subprocess.run(command, cwd=directory, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return {"command": command, "exit": proc.returncode, "output": proc.stdout}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--checker-dir", type=Path)
    options = parser.parse_args()
    records = []
    paths = ["lean-toolchain", "ocaml/gen/roots.json", "ocaml/engine/externs.txt",
             "ocaml/eff/eff_types.ml", "ocaml/gen/api_gen.ml", "ocaml/engine/api_engine.ml"]
    for folder in ["src/OCaml5/Lcnf", "src/OCaml5/Ml", "tools/Conform/Lcnf"]:
        paths += [str(p.relative_to(REPO)) for p in sorted((REPO / folder).glob("*.lean"))]
    paths += ["tools/Conform/Effect4/LcnfMl.lean", "tools/Conform/Effect4/Normalization.lean",
              "tools/Conform/Effect4/CompilerControls.lean"]
    pins = {"files": {path: digest(REPO / path) for path in paths}}
    pins["observed_utc"] = datetime.now(timezone.utc).isoformat()
    pins["loaded_import_artifacts"] = {}
    for name in ["Syntax", "Fold", "Identifier", "Check", "Render"]:
        for suffix in [".olean", ".olean.private", ".olean.server", ".olean.hash", ".trace"]:
            path = REPO / ".lake/build/lib/lean/OCaml5/Ml" / (name + suffix)
            if path.exists():
                pins["loaded_import_artifacts"][str(path.relative_to(REPO))] = {
                    "sha256": digest(path), "mtime_ns": path.stat().st_mtime_ns}
    for name, command in [("head", ["git", "rev-parse", "HEAD"]),
                          ("branch", ["git", "branch", "--show-current"]),
                          ("status", ["git", "status", "--short"]),
                          ("ocaml_config", ["opam", "exec", "--switch=effect4", "--", "ocamlopt", "-config"])]:
        pins[name] = execute(command, REPO)
    pins["probe_files"] = {p.name: digest(p) for p in sorted(HERE.iterdir())
                           if p.suffix in {".ml", ".lean", ".py"}}
    pins["generated_inspection"] = {}
    for path in ["ocaml/eff/eff_types.ml", "ocaml/gen/api_gen.ml", "ocaml/engine/api_engine.ml"]:
        text = (REPO / path).read_text()
        pins["generated_inspection"][path] = {
            "placeholder_occurrences": text.count("Placeholder_"),
            "unknown_type_occurrences": text.count("lcnf_unknown"),
            "hole_occurrences": text.count("HOLE:"),
            "lines": len(text.splitlines())}
    opam = ["opam", "exec", "--switch=effect4", "--", "ocamlopt"]
    with tempfile.TemporaryDirectory(prefix="effect4-lowering-", dir="/private/tmp") as scratch:
        work = Path(scratch)
        for source in HERE.glob("*.ml"):
            shutil.copy2(source, work / source.name)
        result = execute(opam + ["-o", "scalar_boundary", "scalar_boundary.ml"], work)
        records.append(result)
        assert result["exit"] == 0, result
        result = execute([str(work / "scalar_boundary")], work)
        records.append(result)
        assert result["exit"] == 0, result
        shutil.copy2(REPO / "ocaml/eff/eff_types.ml", work / "eff_types.ml")
        result = execute(opam + ["-w", "-a", "-o", "flat_aliases", "eff_types.ml", "flat_aliases.ml"], work)
        records.append(result)
        assert result["exit"] == 0, result
        result = execute([str(work / "flat_aliases")], work)
        records.append(result)
        assert result["exit"] == 0, result
        negative_types = {
            "reject_forged_nat.ml": ["This expression has type int", "Scalar_boundary.Nat.t"],
            "reject_mixed_profile.ml": ["This expression has type Scalar_boundary.Small.t", "Scalar_boundary.Nat.t"],
            "reject_bits_as_nat.ml": ["This expression has type Scalar_boundary.Bits64.t", "Scalar_boundary.Nat.t"]}
        for source, diagnostic in negative_types.items():
            result = execute(opam + ["-c", source], work)
            records.append(result)
            assert result["exit"] == 2 and all(part in result["output"] for part in diagnostic), result
        if options.checker_dir:
            retained = HERE / "checker-generated"
            retained.mkdir(exist_ok=True)
            expected = {"positive": 0, "wrong_type": 2, "unbound": 2,
                        "raw_scope": 2, "unknown_field": 2, "hole_fill": 0}
            diagnostics = {
                "wrong_type": ["This expression has type bool", "int"],
                "unbound": ["Unbound value missing_value"],
                "raw_scope": ["Unbound value missing_value"],
                "unknown_field": ["Unbound record field missing_label"]}
            for name, code in expected.items():
                source = options.checker_dir / (name + ".ml")
                shutil.copy2(source, work / source.name)
                if source.resolve() != (retained / source.name).resolve():
                    shutil.copy2(source, retained / source.name)
                pins["files"][str(source)] = digest(source)
                result = execute(opam + ["-c", source.name], work)
                records.append(result)
                assert result["exit"] == code, result
                assert all(part in result["output"] for part in diagnostics.get(name, [])), result
    (HERE / "pins.json").write_text(json.dumps(pins, indent=2) + "\n")
    (HERE / "ocaml-controls.json").write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps({"commands": len(records), "all_expected_results": True,
                      "checker_files_exercised": bool(options.checker_dir)}, indent=2))


if __name__ == "__main__":
    main()
