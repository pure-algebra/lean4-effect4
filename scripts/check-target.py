#!/usr/bin/env python3
"""Run the pinned TypeScript target conformance oracle. No Lean, installation or generation."""
from pathlib import Path
import subprocess
import sys

if __name__ == "__main__":
    root = Path(__file__).resolve().parent.parent
    raise SystemExit(subprocess.call(["bun", str(root / "tools/target/cli.ts"), "--repo", str(root), *sys.argv[1:]], cwd=root))
