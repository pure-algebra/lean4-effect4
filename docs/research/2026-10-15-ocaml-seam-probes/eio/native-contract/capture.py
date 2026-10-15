"""Capture installed native interface definitions and finite probe provenance."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]


def run(*args):
    completed = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, check=True)
    return completed.stdout.strip()


lib = Path(run("opam", "var", "--switch=effect4", "lib"))
paths = [
    lib / "eio/resource.mli", lib / "eio/resource.ml",
    lib / "eio/flow.mli", lib / "eio/flow.ml",
    lib / "eio/net.mli", lib / "eio/net.ml",
    lib / "eio/buf_read.mli", lib / "eio/buf_read.ml",
    lib / "eio/core/eio__core.mli",
    lib / "cstruct/cstruct.mli",
    HERE / "flow_probe.ml", HERE / "run.sh",
    HERE / "missing_method.ml", HERE / "wrong_role.ml", HERE / "check-types.sh",
]
data = {
    "captured_utc": run("date", "-u", "+%Y-%m-%dT%H:%M:%SZ"),
    "head": run("git", "rev-parse", "HEAD"),
    "branch": run("git", "branch", "--show-current"),
    "ocamlopt": run("opam", "exec", "--switch=effect4", "--", "ocamlopt", "-version"),
    "packages": run("opam", "list", "--switch=effect4", "--installed", "--columns=name,version"),
    "eio_opam": (lib.parent / ".opam-switch/packages/eio.1.2/opam").read_text(),
    "source_sha256": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
    "primary_urls": [
        "https://ocaml-multicore.github.io/eio/eio/Eio/Resource/index.html",
        "https://ocaml-multicore.github.io/eio/eio/Eio/Flow/index.html",
        "https://ocaml-multicore.github.io/eio/eio/Eio/Flow/Pi/index.html",
        "https://ocaml-multicore.github.io/eio/eio/Eio/Net/index.html",
        "https://ocaml-multicore.github.io/eio/eio/Eio/Buf_read/index.html",
    ],
}
(HERE / "sources.json").write_text(json.dumps(data, indent=2) + "\n")
print("Captured native Eio interface source hashes, package versions, and checkout")
