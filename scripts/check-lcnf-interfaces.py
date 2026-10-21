#!/usr/bin/env python3
"""Finite compiler controls for the production staged interface publisher.

Properties: a stale interface cannot block a changed root; a refused later artifact
leaves every published file unchanged; a used unit exports what a later unit links (L8),
and without the link the later unit does not compile and nothing is published. All use
the production staging function and real OCaml compiler. Only Lean fixture emission is
supplied by this control.
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


def scratch(directory, outputs):
    """A repository root for a fixture recipe of `outputs`, over the real OCaml build."""
    root = Path(directory)
    build = root / 'ocaml/_build'
    build.parent.mkdir(parents=True)
    build.symlink_to(repository / 'ocaml/_build', target_is_directory=True)
    recipe = {'artifacts': [{'out': path, 'import': []} for path in outputs]}
    (root / 'recipe.json').write_text(json.dumps(recipe))
    return root


def stub(root, outputs, sources, metadata):
    """The producer's runner, with Lean's emission supplied: `lcnfgen --one i` stages
    `sources[i]` with the interface data `metadata(i)`, and the builds are skipped."""
    def run(command, capture=False):
        if command[:2] == ['lake', 'build'] or command[:2] == ['opam', 'exec'] and 'dune' in command:
            return
        if command[:3] == ['lake', 'exe', 'lcnfgen']:
            stage = Path(command[command.index('--stage') + 1])
            index = int(command[command.index('--one') + 1])
            source = stage / outputs[index]
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(sources[index])
            source.with_suffix('.tsv').write_text(f'fixture\t{index}\n')
            Path(str(source) + '.interface.json').write_text(json.dumps(metadata(index)))
            return
        result = subprocess.run(command, cwd=root, check=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        # The production runner answers a captured command's output (the Zarith directory).
        return result.stdout.decode() if capture else None
    return run


def install(source, destination, checking):
    if checking:
        assert source.read_bytes() == destination.read_bytes()
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)


def digests(paths):
    return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def staleness():
    outputs = ['ocaml/gen/first.ml', 'ocaml/gen/second.ml']
    with tempfile.TemporaryDirectory(prefix='effect4-interface-controls-') as directory:
        root = scratch(directory, outputs)
        fixture = ['type memo = int list\nlet empty : memo = []\n',
                   'let root = 7\n']
        for output in outputs:
            destination = root / output
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text('let old = 0\n')
            destination.with_suffix('.mli').write_text('val impossible_old_root : string\n')
        run = stub(root, outputs, fixture,
                   lambda index: {'roots': ['empty' if index == 0 else 'root'],
                                  'abstract': ['memo'] if index == 0 else []})
        generate(root, 'recipe.json', root, False, run, install)
        first_interface = (root / outputs[0]).with_suffix('.mli').read_text()
        assert 'val empty : memo' in first_interface
        assert 'impossible_old_root' not in first_interface
        published = [root / output for output in outputs]
        published += [path.with_suffix(suffix) for path in published for suffix in ['.mli', '.tsv']]
        before = digests(published)
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
            assert before == digests(published)
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
        assert before == digests(published)
        print('PASS: stale interface replacement and whole-family retention after native refusal')


def links():
    # L8: the later unit links `helper`, which is no root of the used unit; its interface data
    # says so, and the used unit's interface exports it. The red control drops the link.
    outputs = ['ocaml/gen/used.ml', 'ocaml/gen/user.ml']
    with tempfile.TemporaryDirectory(prefix='effect4-interface-links-') as directory:
        root = scratch(directory, outputs)
        fixture = ['let helper = 41\nlet root_a = helper + 1\n',
                   'let root = Used.helper + 1\n']
        linked = ['helper']
        def metadata(index):
            if index == 0:
                return {'roots': ['root_a'], 'abstract': []}
            return {'roots': ['root'], 'abstract': [], 'links': {'Used': list(linked)}}
        run = stub(root, outputs, fixture, metadata)
        generate(root, 'recipe.json', root, False, run, install)
        used_interface = (root / outputs[0]).with_suffix('.mli').read_text()
        assert 'val helper : int' in used_interface, used_interface
        assert 'val root_a : int' in used_interface, used_interface
        print('PASS: a used unit exports its root and the binding its user links (L8)')
        published = [root / output for output in outputs]
        published += [path.with_suffix('.mli') for path in published]
        before = digests(published)
        linked.clear()
        try:
            generate(root, 'recipe.json', root, False, run, install)
        except subprocess.CalledProcessError as error:
            assert error.returncode == 2, error.returncode
            text = error.stdout.decode()
            assert 'Used.helper' in text, text
            print(text)
        else:
            raise AssertionError('a user compiled against a binding its used unit hides')
        assert before == digests(published)
        print('PASS: without the link the user does not compile, and nothing is published')


def main():
    staleness()
    links()
    return 0


if __name__ == '__main__':
    sys.exit(main())
