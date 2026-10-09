#!/usr/bin/env python3
"""Replay finite public-command controls without writing production sources."""
from pathlib import Path
import os
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
fixtures = root / "docs/research/2026-10-08-s1-load-review-fixtures"
lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=root, text=True).strip()
base_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=root, text=True).strip()
with tempfile.TemporaryDirectory(prefix="effect4-s1-load-review-") as scratch:
    overlay = Path(scratch)
    tools = overlay / "Tools"
    tools.mkdir()
    for entry in (root / ".lake/build/lib/lean/Tools").iterdir():
        if entry.name != "S1LoadReview":
            (tools / entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
    compiled = tools / "S1LoadReview"
    compiled.mkdir()
    env = dict(os.environ, LEAN_PATH=f"{overlay}:{base_path}", LEAN_NUM_THREADS="3")
    for module in ("External", "Peer", "Local"):
        command = [lean, "-DwarningAsError=true", f"--root={fixtures}",
            "-o", str(compiled / f"{module}.olean"),
            str(fixtures / "Tools/S1LoadReview" / f"{module}.lean")]
        print(f"CONTROL MODULE {module}", flush=True)
        completed = subprocess.run(command, cwd=root, env=env)
        if completed.returncode:
            raise SystemExit(completed.returncode)
    print("PASS all public-command fixture modules compile", flush=True)
