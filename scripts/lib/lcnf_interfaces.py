"""Stage generated OCaml and infer every interface before publishing the family.

Properties:
L1 Inference reads a fresh implementation typed tree, never a previous interface.
L2 Every public value comes from a source root or the retained prelude.
L3 The compiler checks each selected interface against its implementation.
L4 A refused artifact publishes no output from this run.
L5 The public facade (the recipe's `facade.out`) compiles against the staged artifacts and
   gets its interface as they do, before any output is published.
The interface and regeneration controls exercise these properties.
"""
from pathlib import Path
import json
import shutil
import tempfile


def generate(root, recipe_path, out, checking, run, install):
    recipe = json.loads((root / recipe_path).read_text())
    artifacts = recipe['artefacts']
    destinations = [Path(entry['out']) for entry in artifacts]
    facade = recipe.get('facade', {}).get('out')
    if facade:
        destinations.append(Path(facade))
    if any(path.is_absolute() or '..' in path.parts for path in destinations):
        raise ValueError('LCNF outputs must stay inside the repository')
    if len({path.name for path in destinations}) != len(destinations):
        raise ValueError('LCNF output unit names must be distinct')
    if checking:
        for path in destinations:
            if (out / path).resolve() == (root / path).resolve():
                raise ValueError(f'{path}: output aliases repository destination')
    imports = sorted({module for entry in artifacts for module in entry.get('import', [])})
    run(['lake', 'build', *imports, 'lcnfgen'])
    run(['opam', 'exec', '--switch=effect4', '--', 'dune', 'build', '--root', 'ocaml',
         'gen/interface/main.exe', 'clock/effect4_clock.cma', 'lcnf/effect4_lcnf.cma'])
    with tempfile.TemporaryDirectory(prefix='effect4-lcnf-') as directory:
        stage = Path(directory) / 'stage'
        fresh = Path(directory) / 'compile'
        fresh.mkdir()
        # One process holds one artifact's imports. Nothing is installed in this loop.
        for index in range(len(artifacts)):
            run(['lake', 'exe', 'lcnfgen',
                 '--stage', str(stage), '--recipe', recipe_path, '--one', str(index)])
        includes = [fresh, root / 'ocaml/_build/default/clock/.effect4_clock.objs/byte',
                    root / 'ocaml/_build/default/lcnf/.effect4_lcnf.objs/byte']
        flags = [flag for path in includes for flag in ['-I', str(path)]]
        compiler = ['opam', 'exec', '--switch=effect4', '--', 'ocamlopt',
                    '-bin-annot', '-w', '@55', *flags]
        for entry, destination in zip(artifacts, destinations):
            source = stage / destination
            implementation = fresh / destination.name
            interface = implementation.with_suffix('.mli')
            compiled = implementation.with_suffix('.cmx')
            shutil.copyfile(source, implementation)
            # No .mli exists beside this copy until inference has finished.
            run([*compiler, '-c', str(implementation), '-o', str(compiled)])
            metadata = json.loads(Path(str(source) + '.interface.json').read_text())
            prelude = str(root / entry['prelude']) if entry.get('prelude') else ''
            run(['opam', 'exec', '--switch=effect4', '--',
                 str(root / 'ocaml/_build/default/gen/interface/main.exe'),
                 str(implementation.with_suffix('.cmt')), str(interface),
                 ','.join(metadata['roots']), ','.join(metadata['abstract']), prelude])
            implementation.with_suffix('.cmi').unlink()
            run([*compiler, '-c', str(interface), '-o', str(interface.with_suffix('.cmi'))])
            run([*compiler, '-c', str(implementation), '-o', str(compiled)])
            shutil.copyfile(interface, source.with_suffix('.mli'))
        if facade:
            # The artifact that holds the public roots wrote the facade beside itself. It compiles
            # against the staged interfaces above, and its interface is inferred the same way.
            source = stage / facade
            if not source.is_file():
                raise ValueError(f'{facade}: no artifact wrote the public facade')
            implementation = fresh / Path(facade).name
            interface = implementation.with_suffix('.mli')
            compiled = implementation.with_suffix('.cmx')
            shutil.copyfile(source, implementation)
            run([*compiler, '-c', str(implementation), '-o', str(compiled)])
            metadata = json.loads(Path(str(source) + '.interface.json').read_text())
            run(['opam', 'exec', '--switch=effect4', '--',
                 str(root / 'ocaml/_build/default/gen/interface/main.exe'),
                 str(implementation.with_suffix('.cmt')), str(interface),
                 ','.join(metadata['roots']), ','.join(metadata['abstract']), ''])
            implementation.with_suffix('.cmi').unlink()
            run([*compiler, '-c', str(interface), '-o', str(interface.with_suffix('.cmi'))])
            run([*compiler, '-c', str(implementation), '-o', str(compiled)])
            shutil.copyfile(interface, source.with_suffix('.mli'))
        prepared = sorted(path for path in stage.rglob('*')
                          if path.is_file() and path.suffix in {'.ml', '.mli', '.tsv'})
        # Check every artifact before the first publication. Failed inference or checking
        # cannot leave a mixture of old and new generated files.
        if checking:
            # Interfaces and manifests are discovered only after preparation. Reject
            # aliases across the complete family before any comparison or output copy.
            repository_outputs = {(root / source.relative_to(stage)).resolve()
                                  for source in prepared}
            for source in prepared:
                relative = source.relative_to(stage)
                if (out / relative).resolve() in repository_outputs:
                    raise ValueError(f'{relative}: output aliases repository destination')
            for source in prepared:
                install(source, root / source.relative_to(stage), True)
        for source in prepared:
            relative = source.relative_to(stage)
            if checking:
                target = out / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
            else:
                install(source, root / relative, False)
