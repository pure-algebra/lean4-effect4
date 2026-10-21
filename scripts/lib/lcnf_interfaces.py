"""Stage generated OCaml and infer every interface before publishing the family.

Properties:
L1 Inference reads a fresh implementation typed tree, never a previous interface.
L2 Every public value comes from a source root or the retained prelude.
L3 The compiler checks each selected interface against its implementation.
L4 A refused artifact publishes no output from this run.
L5 The public facade (the recipe's `facade.out`) compiles against the staged artifacts and
   gets its interface as they do, before any output is published.
L6 Each consumer's facade (an artifact's `consumers`) compiles against its artifact, staged
   just before it, and its interface keeps the consumer's roots and the types they name
   (Lcnf_interface's `reachable`), before any output is published.
L7 An artifact that names a `closure` unit stages it first. Its `out` unit is a facade over it,
   whose interface is read off the closure's fresh typed tree (`from` in its interface data),
   so the facade's types are the closure's declarations and its sealed packages are abstract.
   An artifact's `tests` unit includes the closure and is staged after the facade, and its
   consumers' facades after it.
The interface and regeneration controls exercise these properties.
"""
from pathlib import Path
import json
import shutil
import tempfile


def generate(root, recipe_path, out, checking, run, install):
    recipe = json.loads((root / recipe_path).read_text())
    artifacts = recipe['artifacts']
    destinations = [Path(entry['out']) for entry in artifacts]
    consumers = [[Path(consumer['out']) for consumer in entry.get('consumers', [])]
                 for entry in artifacts]
    # Each artifact's scopes (L7): its closure unit and its tests unit, when it names them.
    scopes = [[Path(entry[key]) for key in ('closure', 'tests') if entry.get(key)]
              for entry in artifacts]
    facade = recipe.get('facade', {}).get('out')
    # The artifacts come first, so `zip(artifacts, destinations)` below pairs each with its own.
    destinations += [path for paths in scopes for path in paths]
    destinations += [path for paths in consumers for path in paths]
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
         'gen/interface/main.exe', 'lcnf/effect4_lcnf.cma'])
    # A Lean natural is Zarith's `Z.t` (M4): the staged units compile against its interface.
    zarith = run(['opam', 'exec', '--switch=effect4', '--', 'ocamlfind', 'query', 'zarith'],
                 True).strip()
    with tempfile.TemporaryDirectory(prefix='effect4-lcnf-') as directory:
        stage = Path(directory) / 'stage'
        fresh = Path(directory) / 'compile'
        fresh.mkdir()
        # One process holds one artifact's imports. Nothing is installed in this loop.
        for index in range(len(artifacts)):
            run(['lake', 'exe', 'lcnfgen',
                 '--stage', str(stage), '--recipe', recipe_path, '--one', str(index)])
        includes = [fresh, Path(zarith),
                    root / 'ocaml/_build/default/lcnf/.effect4_lcnf.objs/byte']
        flags = [flag for path in includes for flag in ['-I', str(path)]]
        compiler = ['opam', 'exec', '--switch=effect4', '--', 'ocamlopt',
                    '-bin-annot', '-w', '@55', *flags]
        def infer(source, prelude, reachable):
            # No .mli exists beside the copy until inference has finished.
            implementation = fresh / source.name
            interface = implementation.with_suffix('.mli')
            compiled = implementation.with_suffix('.cmx')
            shutil.copyfile(source, implementation)
            run([*compiler, '-c', str(implementation), '-o', str(compiled)])
            metadata = json.loads(Path(str(source) + '.interface.json').read_text())
            # A facade over a closure reads the closure's typed tree, staged before it (L7).
            typed_tree = (fresh / Path(metadata['from']).name).with_suffix('.cmt') \
                if metadata.get('from') else implementation.with_suffix('.cmt')
            run(['opam', 'exec', '--switch=effect4', '--',
                 str(root / 'ocaml/_build/default/gen/interface/main.exe'),
                 str(typed_tree), str(interface),
                 ','.join(metadata['roots']), ','.join(metadata['abstract']), prelude,
                 *(['reachable'] if reachable else [])])
            implementation.with_suffix('.cmi').unlink()
            run([*compiler, '-c', str(interface), '-o', str(interface.with_suffix('.cmi'))])
            run([*compiler, '-c', str(implementation), '-o', str(compiled)])
            shutil.copyfile(interface, source.with_suffix('.mli'))

        for entry, destination, facades in zip(artifacts, destinations, consumers):
            prelude = str(root / entry['prelude']) if entry.get('prelude') else ''
            if entry.get('closure'):
                # The closure first, then the facade over it, then the tests unit (L7).
                infer(stage / entry['closure'], prelude, False)
                infer(stage / destination, '', False)
                if entry.get('tests'):
                    infer(stage / entry['tests'], '', False)
            else:
                infer(stage / destination, prelude, False)
            # Each consumer's facade includes the artifact just staged (L6).
            for path in facades:
                if not (stage / path).is_file():
                    raise ValueError(f'{path}: {destination} wrote no facade for this consumer')
                infer(stage / path, '', True)
        if facade:
            # The artifact that holds the public roots wrote the facade beside itself. It compiles
            # against the staged interfaces above, and its interface is inferred the same way.
            source = stage / facade
            if not source.is_file():
                raise ValueError(f'{facade}: no artifact wrote the public facade')
            infer(source, '', False)
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
