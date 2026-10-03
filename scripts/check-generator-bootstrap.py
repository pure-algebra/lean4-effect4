#!/usr/bin/env python3
"""Check the early generator against a changed constructor in an isolated Lean fixture.

Build `effect4gen` first. This control never edits a library or generated repository file.
It uses the worktree's pinned Lean environment and its already built generator executable.
"""
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def checked(argv, *, env=None, success=True):
    result = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True, text=True, timeout=120)
    if (result.returncode == 0) != success:
        raise RuntimeError(f"unexpected exit {result.returncode}: {argv}\n{result.stdout}{result.stderr}")
    return result.stdout


def main():
    lean = checked(["lake", "env", "which", "lean"]).strip()
    search = checked(["lake", "env", "printenv", "LEAN_PATH"]).strip()
    executable = ROOT / ".lake/build/bin/effect4gen"
    if not executable.is_file():
        raise RuntimeError("build effect4gen before running this control")
    with tempfile.TemporaryDirectory(prefix="effect4-bootstrap-control-") as directory:
        root = Path(directory)
        module = root / "Bootstrap"
        module.mkdir()
        core, generated = module / "Core.lean", module / "Derived.lean"
        env = dict(os.environ, LEAN_PATH=str(root) + os.pathsep + search, LEAN_NUM_THREADS="3")
        base = "namespace Bootstrap\ninductive Node where\n  | leaf\n  | many (children : List Node)\n"
        core.write_text(base + "end Bootstrap\n")

        def compile(path, *, success=True):
            return checked([lean, "--root=" + str(root), "-DwarningAsError=true", "-o",
                            str(path.with_suffix(".olean")), str(path)], env=env, success=success)

        def emit():
            checked([str(executable), "Fold", "--group", "Bootstrap", "--imports", "Bootstrap.Core",
                     "--out", str(generated), "--header-out", "Bootstrap/Derived.lean",
                     "--kind", "Bootstrap.Node=elim", "Bootstrap.Node"], env=env)

        compile(core)
        emit()
        compile(generated)
        before = generated.read_bytes()
        core.write_text(base + "  | tagged (tag : Nat) (child : Node)\nend Bootstrap\n")
        compile(core)
        compile(generated, success=False)
        print("PASS bootstrap: the added constructor makes the old generated companions fail")
        emit()
        compile(generated)
        after = generated.read_bytes()
        if before == after:
            raise RuntimeError("the added constructor did not change generated output")
        print("PASS bootstrap: the early generator repairs companions without building their stale consumer")
        emit()
        if generated.read_bytes() != after:
            raise RuntimeError("repeat generation changed bytes")
        print("PASS bootstrap: repeat generation is byte-identical")


if __name__ == "__main__":
    main()
