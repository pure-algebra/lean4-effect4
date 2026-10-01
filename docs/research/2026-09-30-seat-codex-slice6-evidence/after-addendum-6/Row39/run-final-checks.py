from pathlib import Path
import subprocess, sys
here = Path(__file__).resolve().parent
root_relative = here.relative_to(here.parents[4])
checks = [
    ("final-comment-build", ".", ["lake", "build", "Effect4.Laws.Program.Typed.Assembly", "Test.Counterexamples.Machine.Semantics.M6Capstone"]),
    ("final-dune", "ocaml", ["opam", "exec", "--switch=effect4", "--", "dune", "build"]),
    ("final-ocaml", ".", ["make", "check-ocaml"]),
    ("final-cases", ".", ["make", "check-cases"]),
    ("final-schema-host", ".", ["bash", "scripts/check-schema-typescript-generation.sh"]),
    ("final-validation", ".", [sys.executable, str(root_relative / "final-validator/validate.py"), "--repo", ".", "--bundle", str(root_relative / "plan")]),
]
for name, cwd, command in checks:
    print("START", name, flush=True)
    result = subprocess.run([sys.executable, str(here / "check.py"), name, cwd, *command])
    if result.returncode:
        raise SystemExit(result.returncode)
print("FINAL CHECKS COMPLETE", flush=True)
