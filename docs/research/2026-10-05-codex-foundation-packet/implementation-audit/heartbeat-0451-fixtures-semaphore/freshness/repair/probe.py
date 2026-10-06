"""Actual extracted repaired checker; all requested commands mocked."""
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


def case(name, mutation, checking=True, output_mode='separate', expect_error=None, expect_changed=False, expect_requests=None):
    with tempfile.TemporaryDirectory(prefix='repair-checker-', dir=HERE) as tmp:
        base = Path(tmp)
        root = base / 'repo'
        lane = root / 'ocaml/engine/test/queue'
        other = root / 'ocaml/engine/test/scenarios'
        lane.mkdir(parents=True)
        other.mkdir(parents=True)
        (lane / 'write.lean').write_text('import Test.Program.QueueScenarios\n')
        (other / 'write.lean').write_text('import Test.Dogfood.Scenario.Tape\n')
        (lane / 'queue.txt').write_bytes(b'GOOD QUEUE\n')
        (other / 'routing.txt').write_bytes(b'GOOD ROUTING\n')
        mutation(root)
        before = {str(p.relative_to(root)): p.read_bytes().hex() for p in root.rglob('*') if p.is_file()}
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
        output = base / 'output'
        if output_mode == 'self':
            output = root
        elif output_mode == 'symlink_root':
            output.symlink_to(root, target_is_directory=True)
        elif output_mode == 'symlink_lane':
            q = output / 'ocaml/engine/test/queue';q.parent.mkdir(parents=True)
            q.symlink_to(lane, target_is_directory=True)
        elif output_mode == 'symlink_second_lane':
            q = output / 'ocaml/engine/test/scenarios';q.parent.mkdir(parents=True)
            q.symlink_to(other, target_is_directory=True)
        elif output_mode == 'symlink_scratch':
            scratch = base / 'valid-output';scratch.mkdir()
            output.symlink_to(scratch, target_is_directory=True)
        elif output_mode == 'cross_lane':
            q = output / 'ocaml/engine/test/queue';q.parent.mkdir(parents=True)
            q.symlink_to(other, target_is_directory=True)
        elif output_mode != 'separate':
            raise AssertionError(output_mode)
        error = None
        try:
            env['fixtures'](output, checking)
        except ValueError as exc:
            error = str(exc)
        after = {str(p.relative_to(root)): p.read_bytes().hex() for p in root.rglob('*') if p.is_file()}
        if expect_error is None:
            assert error is None, (name, error)
        else:
            assert error is not None and expect_error in error, (name, error)
        assert (before != after) == expect_changed, (name, before, after)
        if expect_requests is not None:
            assert len(requests) == expect_requests, (name, requests)
        results.append({'name': name, 'checking': checking, 'output_mode': output_mode, 'error': error, 'repository_bytes_changed': before != after, 'before': before, 'after': after, 'mocked_requests_only': requests})

noop = lambda root: None
def edit(root):
    (root / 'ocaml/engine/test/queue/queue.txt').write_bytes(b'WRONG QUEUE\n')
def missing(root):
    (root / 'ocaml/engine/test/queue/queue.txt').unlink()
def extra(root):
    (root / 'ocaml/engine/test/queue/extra.txt').write_bytes(b'EXTRA\n')
def orphan(root):
    p = root / 'ocaml/engine/test/orphan/retained.txt';p.parent.mkdir();p.write_bytes(b'ORPHAN\n')
def remove_writer(root):
    (root / 'ocaml/engine/test/queue/write.lean').unlink()

case('unchanged accepts and preserves', noop)
case('changed known fixture refuses', edit, expect_error='is not what Lean emits')
case('missing known fixture refuses', missing, expect_error='is not what Lean emits')
case('extra known-lane fixture refuses', extra, expect_error='no writer writes extra.txt')
case('write mode repairs known fixture', edit, checking=False, expect_changed=True)
case('writerless fixture folder refuses before commands', orphan, expect_error='folder with no writer', expect_requests=0)
case('removed writer refuses before commands', remove_writer, expect_error='folder with no writer', expect_requests=0)
case('root alias refuses without changes or commands', edit, output_mode='self', expect_error='output aliases', expect_requests=0)
case('root alias extra fixture remains on refusal', extra, output_mode='self', expect_error='output aliases', expect_requests=0)
case('root symlink alias refuses without changes or commands', edit, output_mode='symlink_root', expect_error='output aliases', expect_requests=0)
case('lane symlink alias refuses without changes or commands', edit, output_mode='symlink_lane', expect_error='output aliases', expect_requests=0)
case('second-lane symlink preflight refuses before first-lane commands', noop, output_mode='symlink_second_lane', expect_error='output aliases', expect_requests=0)
case('symlink to independent scratch is accepted', noop, output_mode='symlink_scratch')
case('write mode self-alias also refuses before commands', edit, checking=False, output_mode='self', expect_error='output aliases', expect_requests=0)
case('cross-lane alias modifies repository before later refusal', noop, output_mode='cross_lane', expect_error='no writer writes queue.txt', expect_changed=True)
report={'source': str(SOURCE), 'method': 'Extracted unchanged repaired install/fixture_lanes/fixtures AST; all run requests mocked. No subprocesses.', 'count': len(results), 'results': results}
(HERE / 'probe-results.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'controls': len(results), 'all_expectations_pass': True, 'actual_subprocesses': 0}, indent=2))
