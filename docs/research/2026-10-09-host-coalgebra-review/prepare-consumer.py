"""Prepare an isolated import overlay from existing build products."""
from pathlib import Path
import shutil
import stat

review = Path(__file__).resolve().parent
root = review.parents[2]
overlay = root / ".lake/host-coalgebra-review-overlay"

def copy_writable(source, destination):
    target = Path(destination)
    if target.exists():
        target.chmod(target.stat().st_mode | stat.S_IWUSR)
    return shutil.copyfile(source, destination)

for source, destination in [
    (root / ".lake/packages/effects/.lake/build/lib/lean/Effects", overlay / "Effects"),
    (review / "package/.lake/build/lib/lean/Effects", overlay / "Effects"),
    (review / "package/.lake/build/lib/lean/ProofGraph", overlay / "ProofGraph"),
]:
    shutil.copytree(source, destination, dirs_exist_ok=True, copy_function=copy_writable)
print(overlay)
