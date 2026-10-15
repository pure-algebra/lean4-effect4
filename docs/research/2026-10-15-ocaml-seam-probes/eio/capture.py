"""Capture tool versions and hashes of the exact sources read by the probes."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def run(*args):
    completed = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, check=True)
    return completed.stdout.strip()


lib = Path(run("opam", "var", "--switch=effect4", "lib"))
paths = [
    ROOT / "ocaml/README.md",
    ROOT / "ocaml/STANDARDS.md",
    ROOT / "ocaml/gen/roots.json",
    ROOT / "ocaml/engine/e4_sched.mli",
    ROOT / "ocaml/engine/e4_sched.ml",
    ROOT / "src/Effect4/Run/Basic.lean",
    ROOT / "src/Effect4/Api/HostSession.lean",
    ROOT / "docs/core/host-boundary.md",
    ROOT / "docs/core/semantics.md",
    ROOT / "docs/core/lcnf-route.md",
    lib / "eio/core/eio__core.mli",
    lib / "eio/core/fiber.ml",
    lib / "eio/core/switch.ml",
    lib / "eio/core/promise.ml",
    lib / "eio/core/cancel.ml",
    lib / "eio/resource.mli",
    lib / "eio/resource.ml",
    lib / "eio/executor_pool.mli",
    lib / "eio/domain_manager.mli",
    lib / "eio/path.mli",
    lib / "picos/picos.mli",
    lib / "picos_mux/fifo/picos_mux_fifo.mli",
    lib / "ocaml/effect.mli",
]
data = {
    "captured_utc": run("date", "-u", "+%Y-%m-%dT%H:%M:%SZ"),
    "head": run("git", "rev-parse", "HEAD"),
    "branch": run("git", "branch", "--show-current"),
    "archive": run("git", "rev-parse", "archive/ocaml5-avatar"),
    "ocamlc": run("opam", "exec", "--switch=effect4", "--", "ocamlc", "-version"),
    "ocamlopt": run("opam", "exec", "--switch=effect4", "--", "ocamlopt", "-version"),
    "opam": run("opam", "--version"),
    "packages": run("opam", "list", "--switch=effect4", "--installed", "--columns=name,version"),
    "source_sha256": {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
    "eio_opam": (lib.parent / ".opam-switch/packages/eio.1.2/opam").read_text(),
    "picos_opam": (lib.parent / ".opam-switch/packages/picos.0.6.0/opam").read_text(),
}
(HERE / "sources.json").write_text(json.dumps(data, indent=2) + "\n")
print("Captured versions, release metadata, and source hashes in sources.json")
