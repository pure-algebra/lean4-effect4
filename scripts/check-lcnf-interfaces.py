#!/usr/bin/env python3
"""Finite compiler controls for the production staged interface publisher.

Properties: a stale interface cannot block a changed root; a refused later artifact
leaves every published file unchanged. Both use the production staging function and
real OCaml compiler. Only Lean fixture emission is supplied by this control.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile
import sys

from lib.lcnf_interfaces import generate

repository = Path(__file__).resolve().parents[1]

def main():
    with tempfile.TemporaryDirectory(prefix='effect4-interface-controls-') as directory:
        root = Path(directory)
        build = root / 'ocaml/_build'
        build.parent.mkdir(parents=True)
        build.symlink_to(repository / 'ocaml/_build', target_is_directory=True)
        outputs = ['ocaml/gen/first.ml', 'ocaml/gen/second.ml']
        recipe = {'artefacts': [{'out': path, 'import': []} for path in outputs]}
        (root / 'recipe.json').write_text(json.dumps(recipe))
        fixture = ['type memo = int list\nlet empty : memo = []\n',
                   'let root = 7\n']
        for output in outputs:
            destination = root / output
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text('let old = 0\n')
            destination.with_suffix('.mli').write_text('val impossible_old_root : string\n')
        def run(command):
            if command[:2] == ['lake', 'build'] or command[:2] == ['opam', 'exec'] and 'dune' in command:
                return
            if command[:3] == ['lake', 'exe', 'lcnfgen']:
                stage = Path(command[command.index('--stage') + 1])
                index = int(command[command.index('--one') + 1])
                source = stage / outputs[index]
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text(fixture[index])
                source.with_suffix('.tsv').write_text(f'fixture\t{index}\n')
                metadata = {'roots': ['empty' if index == 0 else 'root'],
                            'abstract': ['memo'] if index == 0 else []}
                Path(str(source) + '.interface.json').write_text(json.dumps(metadata))
                return
            subprocess.run(command, cwd=root, check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        def install(source, destination, checking):
            if checking:
                assert source.read_bytes() == destination.read_bytes()
                return
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
        generate(root, 'recipe.json', root, False, run, install)
        first_interface = (root / outputs[0]).with_suffix('.mli').read_text()
        assert 'val empty : memo' in first_interface
        assert 'impossible_old_root' not in first_interface
        published = [root / output for output in outputs]
        published += [path.with_suffix(suffix) for path in published for suffix in ['.mli', '.tsv']]
        before = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in published}
        comparison = root / 'valid-comparison'
        generate(root, 'recipe.json', comparison, True, run, install)
        for path in published:
            assert (comparison / path.relative_to(root)).read_bytes() == path.read_bytes()
        for name, suffix, target_suffix in [('implementation', '.ml', '.ml'),
                                             ('interface', '.mli', '.mli'),
                                             ('manifest', '.tsv', '.tsv'),
                                             ('cross-artifact', '.mli', '.mli')]:
            comparison = root / ('alias-' + name)
            alias = (comparison / outputs[0]).with_suffix(suffix)
            alias.parent.mkdir(parents=True, exist_ok=True)
            target = (root / outputs[1 if name == 'cross-artifact' else 0]).with_suffix(target_suffix)
            alias.symlink_to(target)
            try:
                generate(root, 'recipe.json', comparison, True, run, install)
            except ValueError as error:
                assert 'output aliases repository destination' in str(error), str(error)
            else:
                raise AssertionError(f'{name}: repository alias was accepted')
            assert not any(path.is_file() and not path.is_symlink() for path in comparison.rglob('*'))
            assert before == {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in published}
            print('PASS comparison-output alias refused:', name)
        fixture[0] += 'let changed_before_refusal = 9\n'
        fixture[1] += 'let malformed : int = "refuse"\n'
        try:
            generate(root, 'recipe.json', root, False, run, install)
        except subprocess.CalledProcessError as error:
            assert error.returncode == 2, error.returncode
            print(error.stdout.decode())
        else:
            raise AssertionError('invalid staged implementation unexpectedly compiled')
        after = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in published}
        assert before == after
        print('PASS: stale interface replacement and whole-family retention after native refusal')
    return 0

if __name__ == '__main__':
    sys.exit(main())
