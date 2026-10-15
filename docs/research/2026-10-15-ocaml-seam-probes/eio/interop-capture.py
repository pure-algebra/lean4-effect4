"""Record the installed interoperability source and standalone probe environment."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def run(*argv):
    completed = subprocess.run(argv, text=True, capture_output=True, cwd=ROOT)
    return {"argv": list(argv), "returncode": completed.returncode,
            "stdout": completed.stdout, "stderr": completed.stderr}


lib = Path(run("opam", "var", "--switch=effect4", "lib")["stdout"].strip())
paths = [
    lib / "picos/picos.mli",
    lib / "picos_std/structured/picos_std_structured.mli",
    lib / "picos_mux/fifo/picos_mux_fifo.mli",
    lib / "picos_mux/thread/picos_mux_thread.mli",
    lib / "picos_mux/multififo/picos_mux_multififo.mli",
    lib / "picos_io/select/picos_io_select.mli",
    lib / "domain-local-await/Domain_local_await.mli",
    lib / "eio/utils/dla.ml",
    ROOT / "src/OCaml5/Ml/Syntax.lean",
    ROOT / "ocaml/engine/e4_sched.mli",
    ROOT / "ocaml/engine/e4_trigger.mli",
    ROOT / "docs/research/2026-10-14-lowering-cleanup/prompt.md",
    ROOT / "docs/research/2026-10-14-lowering-collation/README.md",
    HERE / "interop_probe.ml",
    HERE / "interop-run.sh",
]
data = {
    "captured_utc": run("date", "-u", "+%Y-%m-%dT%H:%M:%SZ"),
    "head": run("git", "rev-parse", "HEAD"),
    "ocamlopt": run("opam", "exec", "--switch=effect4", "--", "ocamlopt", "-version"),
    "installed_packages": run("opam", "list", "--switch=effect4", "--installed", "--columns=name,version"),
    "ctypes_lookup": run("opam", "exec", "--switch=effect4", "--", "ocamlfind", "query", "ctypes"),
    "source_sha256": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
    "domain_local_await_opam": (lib.parent / ".opam-switch/packages/domain-local-await.1.0.1/opam").read_text(),
    "primary_urls": [
        "https://ocaml.org/p/ctypes/0.24.0/doc/ctypes/Ctypes/index.html",
        "https://yallop.github.io/ocaml-ctypes/Cstubs.html",
        "https://yallop.github.io/ocaml-ctypes/Cstubs_inverted.html",
        "https://yallop.github.io/ocaml-ctypes/Foreign.html",
        "https://dune.readthedocs.io/en/stable/foreign-code.html",
        "https://ocaml.org/manual/5.1/modtypes.html",
        "https://ocaml-multicore.github.io/picos/doc/picos/Picos/index.html",
        "https://github.com/ocaml-multicore/domain-local-await",
    ],
}
(HERE / "interop-capture.json").write_text(json.dumps(data, indent=2) + "\n")
print("Captured interoperability versions, source hashes, and Ctypes absence")
