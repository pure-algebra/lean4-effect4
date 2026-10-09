"""Bounded controls for the import reader used by the build profile."""
from pathlib import Path
import importlib.util
import json
import sys
import tempfile

sys.dont_write_bytecode = True
root = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("review_build_profile", root / "scripts/lib/build_profile.py")
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)

names = ["Effect4.Data.Row", "Effect4.Data.FieldOrder", "Effect4.Program.TyEq", "Effect4.Program.TyVariance"]
known = {name: root / "src" / (name.replace(".", "/") + ".lean") for name in names}
actual = profile.imports_of(root / "src/Effect4/Program/Ty.lean", known)
assert actual == [], actual
with tempfile.TemporaryDirectory(prefix="effect4-profile-review-") as tmp:
    source = Path(tmp) / "Control.lean"
    source.write_text("".join(f"import {name}\n" for name in names))
    plain = profile.imports_of(source, known)
    assert plain == names, plain
    source.write_text("module\n" + "".join(f"public import {name}\n" for name in names))
    public = profile.imports_of(source, known)
    assert public == [], public
    source.write_text("/-\nHeader text.\n-/\nimport Effect4.Data.Row\n")
    header = profile.imports_of(source, known)
    assert header == [], header
print(json.dumps({"actualTyImports": actual, "expectedTyImports": names,
    "plainControl": plain, "publicControl": public, "headerControl": header}, indent=2))
print("PASS: four bounded controls reproduce omitted public imports and block-header imports.")
