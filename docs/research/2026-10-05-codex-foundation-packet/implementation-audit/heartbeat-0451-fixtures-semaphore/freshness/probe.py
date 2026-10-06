"""Run extracted Python fixture checker functions; every Lean command is mocked."""
import ast
import json
from pathlib import Path
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'sources/scripts/generate.py'
NAMES = {'install', 'fixture_lanes', 'fixtures'}
tree = ast.parse(SOURCE.read_text())
extracted = ast.Module(body=[node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name in NAMES], type_ignores=[])
assert {node.name for node in extracted.body} == NAMES
compiled = compile(extracted, str(SOURCE), 'exec')
results = []


def case(name, mutation, checking=True, alias=False, expect_error=None, expect_changed=False):
    with tempfile.TemporaryDirectory(prefix='fixture-checker-', dir=HERE) as tmp:
        root = Path(tmp) / 'repo'
        lane = root / 'ocaml/engine/test/queue'
        other = root / 'ocaml/engine/test/scenarios'
        lane.mkdir(parents=True)
        other.mkdir(parents=True)
        (lane / 'write.lean').write_text('import Test.Program.QueueScenarios\n')
        (other / 'write.lean').write_text('import Test.Dogfood.Scenario.Tape\n')
        fixture = lane / 'queue.txt'
        fixture.write_bytes(b'GOOD QUEUE\n')
        (other / 'routing.txt').write_bytes(b'GOOD ROUTING\n')
        mutation(root)
        before = {str(p.relative_to(root)): p.read_bytes().hex() for p in root.rglob('*.txt')}
        requests = []
        def mocked_run(args):
            requests.append(args)
            assert args[:2] in (['lake', 'build'], ['lake', 'env'])
            if args[:2] == ['lake', 'build']:
                return None
            assert args[:5] == ['lake', 'env', 'lean', '-M4096', '--run']
            target = Path(args[-1])
            if args[-2] == 'ocaml/engine/test/queue/write.lean':
                (target / 'queue.txt').write_bytes(b'GOOD QUEUE\n')
            elif args[-2] == 'ocaml/engine/test/scenarios/write.lean':
                (target / 'routing.txt').write_bytes(b'GOOD ROUTING\n')
            else:
                raise AssertionError(args)
        env = {'ROOT': root, 'FIXTURE_LANES': 'ocaml/engine/test', 'run': mocked_run}
        exec(compiled, env)
        output = root if alias else Path(tmp) / 'output'
        error = None
        try:
            env['fixtures'](output, checking)
        except ValueError as exc:
            error = str(exc)
        after = {str(p.relative_to(root)): p.read_bytes().hex() for p in root.rglob('*.txt')}
        if expect_error is None:
            assert error is None, (name, error)
        else:
            assert error is not None and expect_error in error, (name, error)
        assert (before != after) == expect_changed, (name, before, after)
        results.append({'name': name, 'checking': checking, 'output_aliases_repo': alias, 'error': error, 'repository_fixture_bytes_changed': before != after, 'before': before, 'after': after, 'mocked_requests_only': requests})

noop = lambda root: None
def edit(root):
    (root / 'ocaml/engine/test/queue/queue.txt').write_bytes(b'WRONG QUEUE\n')
def missing(root):
    (root / 'ocaml/engine/test/queue/queue.txt').unlink()
def extra(root):
    (root / 'ocaml/engine/test/queue/extra.txt').write_bytes(b'EXTRA\n')
def orphan(root):
    p = root / 'ocaml/engine/test/orphan/retained.txt'
    p.parent.mkdir()
    p.write_bytes(b'ORPHAN\n')
def remove_writer(root):
    (root / 'ocaml/engine/test/queue/write.lean').unlink()

case('unchanged check accepts and preserves', noop)
case('changed known fixture refused', edit, expect_error='is not what Lean emits')
case('missing known fixture refused', missing, expect_error='is not what Lean emits')
case('extra known-lane fixture refused', extra, expect_error='no writer writes extra.txt')
case('write mode repairs changed known fixture', edit, checking=False, expect_changed=True)
case('writerless-lane fixture silently accepted', orphan)
case('removed writer leaves former-lane fixture unchecked', remove_writer)
case('check output alias overwrites then accepts changed fixture', edit, alias=True, expect_changed=True)
case('check output alias deletes extra fixture then accepts', extra, alias=True, expect_changed=True)
report={'source': str(SOURCE), 'method': 'Extracted unchanged install/fixture_lanes/fixtures AST; mocked all run calls. No Lean, generator, compiler, build or runtime executed.', 'count': len(results), 'results': results}
(HERE / 'probe-results.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'controls': len(results), 'all_expectations_pass': True, 'actual_subprocesses': 0}, indent=2))
