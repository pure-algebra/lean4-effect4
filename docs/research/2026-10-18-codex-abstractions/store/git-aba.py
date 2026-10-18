"""Finite Git control: digest-only compare-and-set admits an A-B-A history."""
from pathlib import Path
import shutil
import subprocess
import tempfile

root = Path(tempfile.mkdtemp(prefix="effect4-git-aba-"))


def git(*args, input=None):
    result = subprocess.run(["git", "-C", str(root), *args], input=input,
                            capture_output=True, text=True, check=True)
    return result.stdout.strip()


try:
    git("init", "-q")
    a = git("hash-object", "-w", "--stdin", input="state A")
    b = git("hash-object", "-w", "--stdin", input="state B")
    ref = "refs/sessions/demo"
    git("update-ref", ref, a, "0" * len(a))
    git("update-ref", ref, b, a)
    git("update-ref", ref, a, b)
    git("update-ref", ref, b, a)
    assert git("rev-parse", ref) == b
    print("digest-only A->B->A: stale compare-and-set from A is accepted")
finally:
    shutil.rmtree(root)
