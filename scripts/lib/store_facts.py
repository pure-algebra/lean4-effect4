"""Generate native kind facts and the semantic node-read refusal mapping.

Properties:
F1 The Lean producer owns every emitted constructor and field.
F2 All requested files exist before publication starts.
F3 A check compares fresh output before copying it into its output directory.
F4 A check destination cannot alias a published output.
The producer refuses unsupported field types or a non-constructor mapping.
"""
from pathlib import Path
import shutil
import tempfile

FILES = tuple(Path('ocaml/engine/cas') / name for name in
              ('e4_kind.ml', 'e4_kind.mli', 'e4_admission.ml', 'e4_admission.mli'))


def generate(root, out, checking, run, install):
    if checking:
        published = {(root / relative).resolve() for relative in FILES}
        for relative in FILES:
            target = (out / relative).resolve()
            if target in published:
                raise ValueError(f'{relative}: output aliases repository destination')
    run(['lake', 'build', 'OCaml5.Tools.CasFacts'])
    with tempfile.TemporaryDirectory(prefix='effect4-store-facts-') as directory:
        fresh = Path(directory)
        run(['lake', 'env', 'lean', '-M4096', '--run',
             'src/OCaml5/Tools/CasFacts.lean', str(fresh)])
        for relative in FILES:
            if not (fresh / relative.name).is_file():
                raise ValueError(f'{relative}: producer left no output')
        if checking:
            for relative in FILES:
                install(fresh / relative.name, root / relative, True)
        for relative in FILES:
            if checking:
                target = out / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(fresh / relative.name, target)
            else:
                install(fresh / relative.name, root / relative, False)
