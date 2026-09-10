"""Bounded comparison of reflected shapes; proof, bytes and policy remain separate.

This module never writes a retained baseline. Extraction reads an immutable Git
revision plus a separately provenance-checked Lean reflection result. Normal
checking writes only a requested report. Unknown shapes and policy entries fail.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = '66ee465730126048ad90d99d24ce4f12f5bb2982'
FORMAT = 'effect4-compatibility-snapshot-v1'
ROOT = Path(__file__).resolve().parents[2]
IMPORTS = ['Effect4.Program.Native', 'Effect4.Schema.Document', 'Effect4.Store.Pin', 'Effect4.Store.Node']
LAYOUT_INPUTS = ['src/Effect4/Store/Kind.lean', 'src/Effect4/Machine/Value.lean',
                 'src/Effect4/Store/Val.lean', 'src/Effect4/Store/Digits.lean',
                 'tools/Effect4Gen/manifest.json', 'src/OCaml5/Tools/EffWire.lean',
                 'src/OCaml5/Eff/World.lean']
BUILD_INPUTS = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n'


def git_bytes(root, revision, path):
    return subprocess.check_output(['git', 'show', f'{revision}:{path}'], cwd=root)


def resolve_revision(root, revision):
    return subprocess.check_output(['git', 'rev-parse', '--verify', revision + '^{commit}'], cwd=root, text=True).strip()


def unique(items, label):
    if len(items) != len(set(items)):
        raise ValueError(f'{label}: duplicate identity')


def validate_type(t, where, bound_depth=0):
    if not isinstance(t, dict) or not t:
        raise ValueError(f'{where}: malformed reflected type')
    keys = set(t)
    if keys == {'constant', 'levels'}:
        if not isinstance(t['constant'], str) or not t['constant'] or not isinstance(t['levels'], list):
            raise ValueError(f'{where}: malformed constant')
        for level in t['levels']:
            validate_level(level, where)
    elif keys in ({'apply'}, {'forall', 'binder'}, {'lambda', 'binder'}):
        key = next(x for x in ('apply', 'forall', 'lambda') if x in t)
        if not isinstance(t[key], list) or len(t[key]) != 2:
            raise ValueError(f'{where}: malformed application or binder')
        if key != 'apply' and (not isinstance(t['binder'], str) or not t['binder']):
            raise ValueError(f'{where}: missing binder policy')
        validate_type(t[key][0], where, bound_depth)
        validate_type(t[key][1], where, bound_depth + (key != 'apply'))
    elif keys == {'sort'}:
        validate_level(t['sort'], where)
    elif keys in ({'bound'}, {'nat'}):
        if type(next(iter(t.values()))) is not int or next(iter(t.values())) < 0:
            raise ValueError(f'{where}: invalid natural')
        if 'bound' in t and t['bound'] >= bound_depth:
            raise ValueError(f'{where}: escaping bound variable')
    elif keys == {'string'}:
        if not isinstance(t['string'], str):
            raise ValueError(f'{where}: invalid literal')
    elif keys == {'projection'}:
        p = t['projection']
        if not isinstance(p, list) or len(p) != 3 or not isinstance(p[0], str) or type(p[1]) is not int or p[1] < 0:
            raise ValueError(f'{where}: malformed projection')
        validate_type(p[2], where, bound_depth)
    else:
        raise ValueError(f'{where}: unsupported type keys {sorted(keys)}')


def validate_level(level, where):
    if level == 'zero':
        return
    if not isinstance(level, dict) or len(level) != 1:
        raise ValueError(f'{where}: unresolved universe')
    key, value = next(iter(level.items()))
    if key == 'parameter' and isinstance(value, str) and value:
        return
    if key == 'succ':
        validate_level(value, where)
        return
    if key in ('max', 'imax') and isinstance(value, list) and len(value) == 2:
        for child in value:
            validate_level(child, where)
        return
    raise ValueError(f'{where}: malformed universe')


def validate(snapshot):
    if snapshot.get('format') != FORMAT:
        raise ValueError('snapshot: unknown format')
    fs = snapshot.get('families')
    if not isinstance(fs, list) or not fs:
        raise ValueError('snapshot: empty family inventory')
    unique([canonical(f['instance']) for f in fs], 'family instances')
    roots = snapshot.get('roots')
    if not isinstance(roots, list) or not roots or not all(isinstance(x, str) and x for x in roots):
        raise ValueError('snapshot: invalid root inventory')
    unique(roots, 'roots')
    if [f['family'] for f in fs[:len(roots)]] != roots:
        raise ValueError('snapshot: roots differ from leading family inventory')
    for f in fs:
        if set(f) != {'family', 'instance', 'kind', 'mutual', 'fields', 'constructors'}:
            raise ValueError('family: malformed fields')
        name = f['family']
        if not isinstance(name, str) or not name or f['kind'] not in ('structure', 'inductive'):
            raise ValueError('family: invalid identity or kind')
        validate_type(f['instance'], name)
        head = f['instance']
        while 'apply' in head:
            head = head['apply'][0]
        if head.get('constant') != name:
            raise ValueError(name + ': instance and family identity disagree')
        if not isinstance(f['mutual'], list) or not all(isinstance(x, str) and x for x in f['mutual']) or name not in f['mutual']:
            raise ValueError(f'{name}: absent from own mutual block')
        if not isinstance(f['fields'], list) or not all(isinstance(x, str) and x for x in f['fields']):
            raise ValueError(f'{name}: malformed field identities')
        unique(f['mutual'], name + '.mutual')
        unique(f['fields'], name + '.fields')
        cs = f['constructors']
        if not isinstance(cs, list) or not cs:
            raise ValueError(f'{name}: empty constructor inventory')
        unique([c['name'] for c in cs], name)
        if f['kind'] == 'structure' and (len(cs) != 1 or len(f['fields']) != len(cs[0]['arguments'])):
            raise ValueError(f'{name}: structure field inventory mismatch')
        if f['kind'] == 'inductive' and f['fields']:
            raise ValueError(f'{name}: inductive has structure fields')
        for i, c in enumerate(cs):
            if set(c) != {'name', 'ordinal', 'arguments'} or not isinstance(c['name'], str) or not c['name'] or not isinstance(c['arguments'], list):
                raise ValueError(f'{name}: malformed constructor')
            if type(c['ordinal']) is not int or c['ordinal'] != i:
                raise ValueError(f'{name}.{c["name"]}: non-positional ordinal')
            for field_index, a in enumerate(c['arguments']):
                if set(a) != {'name', 'type', 'proof'} or not isinstance(a['name'], str) or type(a['proof']) is not bool:
                    raise ValueError(f'{name}: malformed argument')
                validate_type(a['type'], name + '.' + c['name'], field_index)
    maps = snapshot['byte_maps']
    if set(maps) != {'Kind', 'HandleKind', 'Tag'}:
        raise ValueError('byte_maps: incomplete inventory')
    for label, rows in maps.items():
        if not isinstance(rows, list) or not rows:
            raise ValueError(label + ': empty byte map')
        if any(set(r) != {'name', 'byte'} or not isinstance(r['name'], str) or not r['name'] for r in rows):
            raise ValueError(label + ': malformed byte map')
        unique([r['name'] for r in rows], label)
        unique([r['byte'] for r in rows], label + '.bytes')
        if any(type(r['byte']) is not int or not 0 <= r['byte'] <= 255 for r in rows):
            raise ValueError(label + ': byte out of range')
    if not snapshot.get('framing') or not snapshot.get('consumers'):
        raise ValueError('framing or consumer inventory missing')
    for name, values in snapshot['consumers'].items():
        if not isinstance(name, str) or not name or not isinstance(values, list) or not values or not all(isinstance(x, str) and x for x in values):
            raise ValueError(name + ': empty consumer selection')
        unique(values, name)


def compare(old, new, policy=None):
    """Structural judgment only. Explicit policy does not turn tests into proofs."""
    validate(old)
    validate(new)
    policy = policy or {}
    if set(policy) - {'constructor_appends', 'consumer_appends'}:
        raise ValueError('unknown structural policy field')
    for name, entries in policy.items():
        if not isinstance(entries, list) or not all(isinstance(x, str) and x for x in entries):
            raise ValueError(name + ': expected named policy entries')
        unique(entries, name)
    allowed = set(policy.get('constructor_appends', []))
    allowed_consumers = set(policy.get('consumer_appends', []))
    used, used_consumers, errors, changes = set(), set(), [], []
    nf = {canonical(f['instance']): f for f in new['families']}
    for before in old['families']:
        name = before['family']
        after = nf.get(canonical(before['instance']))
        if after is None:
            errors.append(name + ': removed family')
            continue
        for key in ('instance', 'kind', 'mutual', 'fields'):
            if before[key] != after[key]:
                errors.append(f'{name}: changed {key}')
        a, b = before['constructors'], after['constructors']
        if len(b) < len(a):
            errors.append(name + ': removed constructor')
        for i, ctor in enumerate(a):
            if i >= len(b):
                break
            path = name + '.' + ctor['name']
            if ctor['name'] != b[i]['name']:
                errors.append(path + ': reordered or renamed constructor')
            elif ctor['arguments'] != b[i]['arguments']:
                errors.append(path + ': changed payload or field shape')
        for ctor in b[len(a):]:
            path = name + '.' + ctor['name']
            if before['kind'] != 'inductive' or path not in allowed:
                errors.append(path + ': undeclared constructor append')
            else:
                used.add(path)
                changes.append(path + ': declared append')
    for f in new['families']:
        if canonical(f['instance']) not in {canonical(x['instance']) for x in old['families']}:
            errors.append(f['family'] + ': unreviewed family selection addition')
    if old.get('roots') != new.get('roots'):
        errors.append('roots: changed requested family selection')
    for label in old['byte_maps']:
        old_map, new_map = old['byte_maps'][label], new['byte_maps'][label]
        if old_map != new_map:
            errors.append(label + ': changed explicit byte map')
    if old['framing'] != new['framing']:
        errors.append('framing: changed encoding policy')
    if set(old['consumers']) != set(new['consumers']):
        errors.append('consumers: changed consumer set')
    for name, before in old['consumers'].items():
        after = new['consumers'].get(name, [])
        if after[:len(before)] != before:
            errors.append(name + ': removed or reordered consumer selection')
        for addition in after[len(before):]:
            key = name + ':' + addition
            if key in allowed_consumers:
                used_consumers.add(key)
                changes.append(key + ': declared consumer append')
            else:
                errors.append(key + ': undeclared consumer append')
    if used != allowed or used_consumers != allowed_consumers:
        errors.append('policy: unused or stale permission')
    return {'status': 'fail' if errors else 'pass', 'errors': errors, 'changes': changes,
            'judgment': 'retained reflected shapes and explicit layout policy only'}


def policy_delta(before, after, allowed, dimension):
    """Compare observed verdict/permission rows, with exact named expected deltas."""
    if dimension not in ('admission', 'execution_permission'):
        raise ValueError('unknown policy dimension')
    if set(before) != set(after):
        raise ValueError(dimension + ': changed case inventory')
    actual = {key: {'before': before[key], 'after': after[key]}
              for key in before if before[key] != after[key]}
    return {'dimension': dimension, 'status': 'pass' if actual == allowed else 'fail',
            'changes': actual, 'expected': allowed,
            'judgment': 'comparison of supplied observations, not evidence of their execution'}


def source_closure(read, roots=IMPORTS):
    """Exact source closure of the imports built for reflection; no type parsing."""
    from generated_inputs import imports
    found = {}
    def visit(module):
        if not module.startswith('Effect4.') or module in found:
            return
        path = 'src/' + module.replace('.', '/') + '.lean'
        data = read(path)
        found[module] = {'path': path, 'sha256': digest(data)}
        for dep in imports(data):
            visit(dep)
    for root in roots:
        visit(root)
    return [found[n] for n in sorted(found)]


def body(source, start, stop):
    text = source.decode()
    if text.count(start) != 1 or stop not in text.split(start, 1)[1]:
        raise ValueError('unrecognized source form: ' + start)
    return text.split(start, 1)[1].split(stop, 1)[0].strip()


def layout(read):
    maps = {}
    for label, path, start, stop in [
        ('Kind', 'src/Effect4/Store/Kind.lean', 'def byte : Kind → UInt8', '/--'),
        ('HandleKind', 'src/Effect4/Machine/Value.lean', 'def byte : HandleKind → UInt8', '/--'),
    ]:
        text = body(read(path), start, stop)
        rows = []
        for line in text.splitlines():
            match = re.fullmatch(r'\s*\|\s*\.?([\w«»]+)\s*=>\s*(\d+)\s*', line)
            if not match:
                raise ValueError(label + ': unsupported byte assignment')
            rows.append({'name': match[1].strip('«»'), 'byte': int(match[2])})
        maps[label] = rows
    tags = body(read('src/Effect4/Store/Val.lean'), 'namespace Tag\n', 'end Tag')
    maps['Tag'] = [{'name': n, 'byte': int(b)} for n, b in
                   re.findall(r'^def (\w+) : UInt8 := (\d+)$', tags, re.M)]
    if len(maps['Tag']) != len(re.findall(r'^def \w+ : UInt8\b', tags, re.M)):
        raise ValueError('Tag: unsupported byte assignment')
    framing = {
        'frame_definition': body(read('src/Effect4/Store/Val.lean'),
            'def framed (tag : UInt8) (payload : Bytes) : Bytes :=', '/-!'),
        'length_definition': body(read('src/Effect4/Store/Digits.lean'),
            'def be64 (n : Nat) : Bytes :=', '/--'),
        'digits_definition': body(read('src/Effect4/Store/Digits.lean'),
            'def toDigits : Nat → Nat → Bytes', '/--'),
        'nat_definition': body(read('src/Effect4/Store/Digits.lean'),
            'def natBytes (n : Nat) : Bytes :=', '/-!'),
        'digit_count_definition': body(read('src/Effect4/Store/Digits.lean'),
            'def digitCount (n : Nat) : Nat :=', '/--'),
    }
    manifest = json.loads(read('tools/Effect4Gen/manifest.json'))
    consumers = {'deriving:' + g['Name']: g['Types'] for g in manifest['groups']}
    wire = body(read('src/OCaml5/Tools/EffWire.lean'), 'let families : List Lean.Name := [', ']')
    consumers['wire'] = re.findall(r'`([\w.]+)', wire)
    world = body(read('src/OCaml5/Eff/World.lean'), 'def blocks : List (List Spec) :=', 'def allSpecs')
    consumers['ocaml-world'] = re.findall(r'⟨`([\w.]+),', world)
    return maps, framing, consumers


def extract(root, revision, reflection, build_receipt, inventory):
    revision = resolve_revision(root, revision)
    read = lambda path: git_bytes(root, revision, path)
    closure = source_closure(read)
    # The wrapper owns this receipt only after a build of the frozen checkout.
    if build_receipt != {'revision': revision, 'toolchain': read('lean-toolchain').decode().strip(),
                          'source_closure': closure, 'reflection_sha256': digest(canonical(reflection).encode())}:
        raise ValueError('reflection provenance differs from requested frozen source closure')
    return assemble(reflection, build_receipt, inventory, read, require_retained_names=True)


def assemble(reflection, build_receipt, inventory, read, require_retained_names=False):
    """Assemble metadata after the driver has checked captured build provenance."""
    if reflection.get('format') != 'effect4-reflected-shapes-v1':
        raise ValueError('unknown reflection format')
    families = reflection['families']
    roots = [f['family'] for f in inventory['families']]
    if reflection.get('roots') != roots or [f['family'] for f in families[:len(roots)]] != roots:
        raise ValueError('reflection family selection differs from retained inventory')
    for old, new in zip(inventory['families'], families):
        if require_retained_names and (old['constructors'] != [c['name'] for c in new['constructors']] or old['fields'] != new['fields'] or old['mutual'] != new['mutual']):
            raise ValueError(old['family'] + ': reflection disagrees with retained names/order')
    maps, framing, consumers = layout(read)
    result = {'format': FORMAT, 'source': build_receipt, 'roots': roots, 'families': families,
              'byte_maps': maps, 'framing': framing, 'consumers': consumers}
    validate(result)
    return result
