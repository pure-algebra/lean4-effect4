#!/usr/bin/env python3
"""Run conversion probes in an isolated temporary dune workspace.

Depends on the existing effect4 opam switch. Copies sources without editing them.
Properties: source SHA256 and exact commands are logged; failure propagates [tested].
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
INPUTS = [
    "ocaml/eff/eff_types.ml", "ocaml/eff/eff_frame.ml", "ocaml/eff/eff_wire.ml",
    "ocaml/clock/e4_clock.ml", "ocaml/clock/e4_clock.mli",
    "src/Effect4/Program/TyCore.lean", "src/Effect4/Schema/Modeled.lean",
    "src/Effect4/Schema/Modeled/Derive.lean", "src/Effect4/Store/Carrier/Image.lean",
    "src/Effect4/Store/Carrier/Image/Record.lean", "src/Effect4/Laws/Schema/Modeled.lean",
    "src/OCaml5/Lcnf/TypeRows.lean", "src/OCaml5/Ml/Syntax.lean",
]

def run(args, cwd, log):
    log.write("$ " + " ".join(map(str, args)) + "\n")
    log.flush()
    result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write(result.stdout)
    log.write(f"EXIT {result.returncode}\n")
    log.flush()
    result.check_returncode()
    return result.stdout.strip()

def main():
    with (HERE / "run.log").open("w") as log, tempfile.TemporaryDirectory(prefix="effect4-conversions-") as tmp:
        work = Path(tmp)
        head = run(["git", "rev-parse", "HEAD"], ROOT, log)
        run(["git", "status", "--short"], ROOT, log)
        provenance = {"head":head, "inputs":{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in INPUTS}}
        for args in [
            ["opam", "exec", "--switch=effect4", "--", "ocamlc", "-version"],
            ["opam", "exec", "--switch=effect4", "--", "dune", "--version"],
            ["opam", "list", "--switch=effect4", "--installed", "--columns=name,version", "--short"],
        ]:
            run(args, work, log)
        for name in INPUTS[:5]:
            shutil.copy2(ROOT/name, work/Path(name).name)
        raw = (work/"eff_types.ml").read_text()
        marker = "and 'a effect4_row = 'a list"
        assert raw.count(marker) == 1
        # Attribute is attached to the existing generated mutual declaration group.
        (work/"eff_types.ml").write_text("open Sexplib.Std\n" + raw.replace(marker, marker + "\n[@@deriving sexp, sexp_grammar]"))
        shutil.copy2(HERE/"probe.ml", work/"probe.ml")
        (work/"dune-project").write_text("(lang dune 3.11)\n")
        (work/"dune").write_text('''(executable
 (name probe)
 (libraries sexplib base_quickcheck zarith)
 (preprocess (pps ppx_sexp_conv ppx_compare base_quickcheck.ppx_quickcheck))
 (flags (:standard -w -a)))
''')
        provenance["instrumented_eff_types_sha256"] = hashlib.sha256((work/"eff_types.ml").read_bytes()).hexdigest()
        for package_path in [
            Path("/Users/pooks/.opam/effect4/doc/ppx_sexp_conv/README.org"),
            Path("/Users/pooks/.opam/effect4/lib/eio/resource.mli"),
            Path("/Users/pooks/.opam/effect4/lib/zarith/z.mli"),
            Path("/Users/pooks/.opam/effect4/lib/base_quickcheck/test_intf.ml"),
        ]:
            provenance.setdefault("installed_sources",{})[str(package_path)] = hashlib.sha256(package_path.read_bytes()).hexdigest()
        (HERE/"provenance.json").write_text(json.dumps(provenance, indent=2)+"\n")
        run(["opam", "exec", "--switch=effect4", "--", "dune", "exec", "--root", str(work), "./probe.exe"], work, log)
        # A separately compiled client must not construct the abstract exact clock.
        run(["opam", "exec", "--switch=effect4", "--", "ocamlc", "-c", "e4_clock.mli"], work, log)
        (work/"negative.ml").write_text("let forged : E4_clock.t = 1\n")
        args = ["opam", "exec", "--switch=effect4", "--", "ocamlc", "-c", "negative.ml"]
        log.write("$ " + " ".join(args) + "\n")
        negative = subprocess.run(args, cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log.write(negative.stdout)
        log.write(f"EXIT {negative.returncode} (expected rejection)\n")
        assert negative.returncode != 0 and "E4_clock.t" in negative.stdout and "int" in negative.stdout
        log.write("PASS abstract_clock_constructor_hidden\n")
    print(f"Probe finished: {HERE/'run.log'}")

if __name__ == "__main__":
    main()
