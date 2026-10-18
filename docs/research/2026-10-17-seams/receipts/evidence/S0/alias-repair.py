from pathlib import Path
r=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
p=r/'scripts/lib/lcnf_interfaces.py'
s=p.read_text()
old="""        if checking:
            for source in prepared:
                install(source, root / source.relative_to(stage), True)
"""
new="""        if checking:
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
"""
assert old in s
p.write_text(s.replace(old,new))
p=r/'scripts/check-lcnf-interfaces.py'
s=p.read_text().replace("source.write_text(fixture[index])", "source.write_text(fixture[index])\n                source.with_suffix('.tsv').write_text(f'fixture\\t{index}\\n')")
s=s.replace("            assert not checking\n            destination.parent", "            if checking:\n                assert source.read_bytes() == destination.read_bytes()\n                return\n            destination.parent")
s=s.replace("        published += [path.with_suffix('.mli') for path in published]", "        published += [path.with_suffix(suffix) for path in published for suffix in ['.mli', '.tsv']]")
needle="        fixture[0] += 'let changed_before_refusal = 9\\n'"
insert="""        comparison = root / 'valid-comparison'
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
"""
assert needle in s
p.write_text(s.replace(needle,insert+needle))
p=r/'ocaml/engine/e4_instance.ml'
s=p.read_text()
s=s.replace('The result has no\n   signature of its own: it is the generated engine itself plus the adapter, and the tests read\n   generated declarations through an instance (`sh_spawn`, `fork_record`, the timer store).', 'The result exposes the generated roots and the adapter projections through e4_instance.mli.\n   Tests also read retained prelude declarations through an instance (`sh_spawn`, `fork_record`,\n   the timer store).')
s=s.replace('  let step (table : Row.t list)', '  (* stepChecked rebuilds interpOf p table. The old interpreter argument remains\n     for INSTANCE compatibility; test_seams_step also supplies a mismatched interpreter. *)\n  let step (table : Row.t list)')
p.write_text(s)
p=r/'ocaml/engine/test/api_gen_inst.ml'
s=p.read_text().replace('let step (table : Row.t list)', '(* stepChecked rebuilds interpOf p table. The old interpreter argument remains\n   for INSTANCE compatibility; test_seams_step also supplies a mismatched interpreter. *)\nlet step (table : Row.t list)')
p.write_text(s)
