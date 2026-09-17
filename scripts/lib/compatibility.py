"""Bounded comparison of reflected shapes; proof, bytes and policy remain separate.

This module never writes a retained baseline. Extraction reads an immutable Git
revision plus a separately provenance-checked Lean reflection result. Normal
checking writes only a requested report. Unknown shapes and policy entries fail.

A constructor has two numbers. Its ordinal is its declaration position, which the
compiled layout follows. Its wire tag is the number it carries in the canonical
bytes, read from the one assignment `tools/Effect4Gen/wire-tags.json`. The first
snapshot format has no tags: there a tag is the ordinal. The second format records
both, and the retired tags of every family. The comparison is by tag and name.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = '66ee465730126048ad90d99d24ce4f12f5bb2982'
FORMAT = 'effect4-compatibility-snapshot-v1'
FORMAT_TAGGED = 'effect4-compatibility-snapshot-v2'
TAGS_FORMAT = 'effect4-wire-tags-v1'
POLICY_FORMAT = 'effect4-compatibility-policy-v1'
TAGS = 'tools/Effect4Gen/wire-tags.json'
PROGRAM_STRUCTURE = 'tools/Tools/ProgramStructure.lean'
ROOT = Path(__file__).resolve().parents[2]
IMPORTS = ['Effect4.Program.Native', 'Effect4.Schema.Document', 'Effect4.Store.Pin', 'Effect4.Store.Node']
LAYOUT_INPUTS = ['src/Effect4/Store/Kind.lean', 'src/Effect4/Machine/Value.lean',
                 'src/Effect4/Store/Val.lean', 'src/Effect4/Store/Digits.lean',
                 'tools/Effect4Gen/manifest.json', 'src/OCaml5/Tools/EffWire.lean',
                 'src/OCaml5/Eff/World.lean']
# Present at a later revision only: the family selection's new home and the tag
# assignment. A revision without them is read by the older source forms.
OPTIONAL_LAYOUT_INPUTS = [PROGRAM_STRUCTURE, TAGS]
BUILD_INPUTS = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n'


def git_bytes(root, revision, path):
    # Captured, not printed: a path a revision does not have yet is an ordinary answer here.
    return subprocess.run(['git', 'show', f'{revision}:{path}'], cwd=root, check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout


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


def optional(read, path):
    """The bytes of a path that a revision may not have yet."""
    try:
        return read(path)
    except (OSError, subprocess.CalledProcessError):
        return None


def wire_tags(read):
    """The tag assignment, checked for its own rules. None when the revision has no file."""
    data = optional(read, TAGS)
    if data is None:
        return None
    def pairs(items):
        # A JSON object that names one key twice would silently keep the last row.
        unique([key for key, _ in items], 'wire tags: a key given twice')
        return dict(items)
    doc = json.loads(data, object_pairs_hook=pairs)
    if not isinstance(doc, dict) or set(doc) - {'format', 'comment', 'families'}:
        raise ValueError('wire tags: unknown key')
    if doc.get('format') != TAGS_FORMAT or not isinstance(doc.get('families'), dict):
        raise ValueError('wire tags: unknown format')
    for family, row in doc['families'].items():
        if not isinstance(row, dict) or set(row) != {'active', 'retired'}:
            raise ValueError(f'wire tags: {family}: expected active and retired rows')
        for part in ('active', 'retired'):
            if not isinstance(row[part], dict) or any(
                    type(tag) is not int or tag < 0 or not name for name, tag in row[part].items()):
                raise ValueError(f'wire tags: {family}.{part}: malformed rows')
        if not row['active']:
            raise ValueError(f'wire tags: {family}: no active constructor')
        unique(list(row['active']) + list(row['retired']), f'wire tags: {family} names')
        unique(list(row['active'].values()) + list(row['retired'].values()), f'wire tags: {family} tags')
    return doc['families']


def apply_tags(families, tags):
    """Give every reflected constructor its wire tag and every family its retired rows."""
    known = {f['family'] for f in families}
    for family in tags:
        if family not in known:
            raise ValueError(f'wire tags: {family}: listed but not a reflected family')
    for f in families:
        row = tags.get(f['family'])
        declared = [c['name'] for c in f['constructors']]
        if row is None:
            for c in f['constructors']:
                c['tag'] = c['ordinal']
            f['retired'] = []
            continue
        if f['kind'] != 'inductive':
            raise ValueError(f'wire tags: {f["family"]}: a structure may not be listed')
        if set(row['active']) != set(declared):
            raise ValueError(f'wire tags: {f["family"]}: active rows differ from the declared constructors')
        if set(row['retired']) & set(declared):
            raise ValueError(f'wire tags: {f["family"]}: a retired constructor is still declared')
        for c in f['constructors']:
            c['tag'] = row['active'][c['name']]
        f['retired'] = [{'name': name, 'tag': tag}
                        for name, tag in sorted(row['retired'].items(), key=lambda item: item[1])]


def tagged(snapshot):
    """A copy in which every constructor has a tag: the first format's tag is its ordinal."""
    result = json.loads(json.dumps(snapshot))
    if result.get('format') == FORMAT:
        for f in result['families']:
            for c in f['constructors']:
                c['tag'] = c['ordinal']
            f['retired'] = []
    return result


def validate(snapshot):
    if snapshot.get('format') not in (FORMAT, FORMAT_TAGGED):
        raise ValueError('snapshot: unknown format')
    with_tags = snapshot['format'] == FORMAT_TAGGED
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
        family_keys = {'family', 'instance', 'kind', 'mutual', 'fields', 'constructors'}
        if set(f) != (family_keys | {'retired'} if with_tags else family_keys):
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
        ctor_keys = {'name', 'ordinal', 'arguments'}
        if with_tags:
            retired = f['retired']
            if not isinstance(retired, list) or any(
                    not isinstance(r, dict) or set(r) != {'name', 'tag'} or not isinstance(r['name'], str)
                    or not r['name'] or type(r['tag']) is not int or r['tag'] < 0 for r in retired):
                raise ValueError(f'{name}: malformed retired rows')
            if any(type(c.get('tag')) is not int or c['tag'] < 0 for c in cs):
                raise ValueError(f'{name}: malformed wire tag')
            # Sparse tags are valid; a tag or a name given twice is not.
            unique([c['tag'] for c in cs] + [r['tag'] for r in retired], name + '.tags')
            unique([c['name'] for c in cs] + [r['name'] for r in retired], name + '.names')
            if f['kind'] == 'structure' and (retired or cs[0]['tag'] != 0):
                raise ValueError(f'{name}: a structure is constructor 0 and retires nothing')
            ctor_keys = ctor_keys | {'tag'}
        for i, c in enumerate(cs):
            if set(c) != ctor_keys or not isinstance(c['name'], str) or not c['name'] or not isinstance(c['arguments'], list):
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


NAME_LISTS = ('constructor_additions', 'constructor_retirements', 'family_additions',
              'consumer_additions', 'vector_removals', 'vector_migrations')
POLICY_NOTES = ('format', 'baseline', 'comment')


def read_policy(policy):
    """A policy names every permitted difference. An unknown field or a malformed row refuses."""
    policy = dict(policy or {})
    if set(policy) - set(NAME_LISTS) - set(POLICY_NOTES) - {'historical_renumbering'}:
        raise ValueError('unknown structural policy field')
    if 'format' in policy and policy['format'] != POLICY_FORMAT:
        raise ValueError('policy: unknown format')
    for name in NAME_LISTS:
        entries = policy.setdefault(name, [])
        if not isinstance(entries, list) or not all(isinstance(x, str) and x for x in entries):
            raise ValueError(name + ': expected named policy entries')
        unique(entries, name)
    rows = policy.setdefault('historical_renumbering', [])
    if not isinstance(rows, list):
        raise ValueError('historical_renumbering: expected a list of exemptions')
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'family', 'commit', 'reason', 'removed', 'moved', 'reused'}:
            raise ValueError('historical_renumbering: malformed exemption')
        if not all(isinstance(row[k], str) and row[k] for k in ('family', 'commit', 'reason')):
            raise ValueError('historical_renumbering: an exemption names its family, commit and reason')
        for kind in ('removed', 'reused'):
            if not isinstance(row[kind], dict) or any(type(t) is not int for t in row[kind].values()):
                raise ValueError(f'historical_renumbering: {kind} rows are name to tag')
        if not isinstance(row['moved'], dict) or any(
                not isinstance(m, list) or len(m) != 2 or any(type(t) is not int for t in m) or m[0] == m[1]
                for m in row['moved'].values()):
            raise ValueError('historical_renumbering: moved rows are name to [old tag, new tag]')
    unique([row['family'] for row in rows], 'historical_renumbering')
    return policy


def compare(old, new, policy=None):
    """Structural judgment only. Explicit policy does not turn tests into proofs.

    A retained constructor keeps its name, its wire tag and its fields. A constructor leaves
    only by retirement: its row moves to the retired rows at the same tag, and the policy names
    it. A new constructor is named by the policy and takes a tag that no constructor of the
    baseline, active or retired, ever held. The one other route is a historical exemption,
    which names a removal or a move that happened before tags were assigned. Every permission
    must be used, and every difference must have one.
    """
    validate(old)
    validate(new)
    policy = read_policy(policy)
    old, new = tagged(old), tagged(new)
    errors, changes = [], []
    used = {name: set() for name in NAME_LISTS}
    used_exemptions = set()
    exemptions = {row['family']: row for row in policy['historical_renumbering']}

    def permit(kind, key, note):
        if key in policy[kind]:
            used[kind].add(key)
            changes.append(f'{key}: {note}')
            return True
        return False

    if old.get('source', {}).get('toolchain') != new.get('source', {}).get('toolchain'):
        errors.append('toolchain: changed or missing core-container identity pin')
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
        exemption = exemptions.get(name, {'removed': {}, 'moved': {}, 'reused': {}})
        active = {c['name']: c for c in after['constructors']}
        retired = {r['name']: r['tag'] for r in after['retired']}
        held = {c['tag']: c['name'] for c in before['constructors']}
        held.update({r['tag']: r['name'] for r in before['retired']})
        excused = set()
        for ctor in before['constructors']:
            path = name + '.' + ctor['name']
            now = active.get(ctor['name'])
            if now is not None:
                if now['tag'] != ctor['tag']:
                    if exemption['moved'].get(ctor['name']) == [ctor['tag'], now['tag']]:
                        used_exemptions.add((name, 'moved', ctor['name']))
                        excused.add(ctor['name'])
                        changes.append(f'{path}: historical move from tag {ctor["tag"]} to {now["tag"]}')
                    else:
                        errors.append(f'{path}: changed wire tag {ctor["tag"]} to {now["tag"]}')
                if now['arguments'] != ctor['arguments']:
                    errors.append(path + ': changed payload or field shape')
            elif ctor['name'] in retired:
                if retired[ctor['name']] != ctor['tag']:
                    errors.append(f'{path}: retired at tag {retired[ctor["name"]]}, held {ctor["tag"]}')
                elif not permit('constructor_retirements', path, f'declared retirement of tag {ctor["tag"]}'):
                    errors.append(path + ': undeclared retirement')
            elif exemption['removed'].get(ctor['name']) == ctor['tag']:
                used_exemptions.add((name, 'removed', ctor['name']))
                excused.add(ctor['name'])
                changes.append(f'{path}: historical removal at tag {ctor["tag"]}')
            else:
                errors.append(path + ': removed constructor (a constructor leaves by retirement)')
        for row in before['retired']:
            if retired.get(row['name']) != row['tag']:
                errors.append(f'{name}.{row["name"]}: retired row dropped or changed')
        known = {c['name'] for c in before['constructors']} | {r['name'] for r in before['retired']}
        for ctor in after['constructors']:
            path = name + '.' + ctor['name']
            owner = held.get(ctor['tag'])
            if owner is not None and owner != ctor['name']:
                # A tag is taken twice only where the exemption vacated it and names the taker.
                if owner in excused and ctor['name'] in excused:
                    pass
                elif owner in excused and exemption['reused'].get(ctor['name']) == ctor['tag']:
                    used_exemptions.add((name, 'reused', ctor['name']))
                    changes.append(f'{path}: historical reuse of tag {ctor["tag"]} of {owner}')
                else:
                    errors.append(f'{path}: reused wire tag {ctor["tag"]} of {owner}')
            if ctor['name'] in {r['name'] for r in before['retired']}:
                errors.append(path + ': retired constructor declared again')
            elif ctor['name'] not in known:
                if before['kind'] != 'inductive' or not permit('constructor_additions', path, f'declared addition at tag {ctor["tag"]}'):
                    errors.append(path + ': undeclared constructor addition')
        for row in after['retired']:
            path = name + '.' + row['name']
            if row['name'] in known:
                continue
            # Added and retired between two baselines: still a reviewed event, still no reuse.
            owner = held.get(row['tag'])
            if owner is not None:
                errors.append(f'{path}: reused wire tag {row["tag"]} of {owner}')
            if not permit('constructor_retirements', path, f'declared retirement of tag {row["tag"]}'):
                errors.append(path + ': undeclared retirement')
    old_instances = {canonical(x['instance']) for x in old['families']}
    for f in new['families']:
        if canonical(f['instance']) not in old_instances:
            if not permit('family_additions', f['family'], 'declared family addition'):
                errors.append(f['family'] + ': unreviewed family selection addition')
    if old.get('roots') != new.get('roots'):
        errors.append('roots: changed requested family selection')
    for label in old['byte_maps']:
        old_map, new_map = old['byte_maps'][label], new['byte_maps'][label]
        if old_map != new_map:
            errors.append(label + ': changed explicit byte map')
    if old['framing'] != new['framing']:
        errors.append('framing: changed encoding policy')
    # A consumer selection is a set: the order in which a tool lists families moves no byte.
    for name, before in old['consumers'].items():
        after = new['consumers'].get(name)
        if after is None:
            errors.append(name + ': removed consumer')
        elif set(before) - set(after):
            errors.append(name + ': removed consumer selection')
    for name, after in new['consumers'].items():
        for addition in [x for x in after if x not in old['consumers'].get(name, [])]:
            key = name + ':' + addition
            if not permit('consumer_additions', key, 'declared consumer addition'):
                errors.append(key + ': undeclared consumer addition')
    for row in policy['historical_renumbering']:
        for kind in ('removed', 'moved', 'reused'):
            for ctor in row[kind]:
                if (row['family'], kind, ctor) not in used_exemptions:
                    errors.append(f'policy: unused exemption {row["family"]}.{ctor} ({kind})')
    for kind in ('constructor_additions', 'constructor_retirements', 'family_additions', 'consumer_additions'):
        for key in sorted(set(policy[kind]) - used[kind]):
            errors.append(f'policy: unused or stale permission {kind}:{key}')
    return {'status': 'fail' if errors else 'pass', 'errors': errors, 'changes': changes,
            'judgment': 'retained reflected shapes and explicit layout policy only'}


def retained_vectors(digests, root, policy=None):
    """Every retained canonical byte vector keeps its bytes.

    `digests` is the text of a retained `shasum -a 256` listing and `root` the directory its
    paths are relative to. Only `.hex` and `.bin` rows are canonical bytes; the other rows of
    the listing (printed JSON, typing verdicts, inventories) are not wire vectors. A vector
    may be absent, or differ, only when the policy names it, and a named vector that is still
    present and unchanged is a stale permission.
    """
    policy = read_policy(policy)
    errors, changes, checked = [], [], 0
    seen = set()
    for line in digests.splitlines():
        if not line.strip():
            continue
        expected, _, path = line.partition('  ')
        if not path or len(expected) != 64:
            raise ValueError('retained vectors: malformed digest row')
        if not path.endswith(('.hex', '.bin')):
            continue
        seen.add(path)
        target = Path(root) / path
        actual = digest(target.read_bytes()) if target.is_file() else None
        if path in policy['vector_removals']:
            if actual is not None:
                errors.append(f'policy: stale vector removal {path}')
            else:
                changes.append(f'{path}: declared removal')
        elif path in policy['vector_migrations']:
            if actual is None or actual == expected:
                errors.append(f'policy: stale vector migration {path}')
            else:
                changes.append(f'{path}: declared migration')
        elif actual is None:
            errors.append(f'{path}: retained vector removed')
        elif actual != expected:
            errors.append(f'{path}: retained vector changed its bytes')
        else:
            checked += 1
    for kind in ('vector_removals', 'vector_migrations'):
        for path in policy[kind]:
            if path not in seen:
                errors.append(f'policy: unknown vector {kind}:{path}')
    return {'status': 'fail' if errors else 'pass', 'errors': errors, 'changes': changes,
            'unchanged': checked,
            'judgment': 'retained byte vectors compared by digest; no decoder was run'}


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


def imports(data):
    """The module names a Lean source imports, read off its header (comments skipped)."""
    import re
    text, result, pos = data.decode(), [], 0
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end + 1
        elif text.startswith('/-', pos):
            depth, pos = 1, pos + 2
            while depth and pos < len(text):
                if text.startswith('/-', pos):
                    depth, pos = depth + 1, pos + 2
                elif text.startswith('-/', pos):
                    depth, pos = depth - 1, pos + 2
                else:
                    pos += 1
            if depth:
                raise ValueError('unterminated Lean header comment')
        else:
            match = re.match(r'(?:(?:public|private) )?import ([A-Za-z0-9_.]+)', text[pos:])
            marker = re.match(r'(?:prelude|module)\b', text[pos:])
            if match:
                result.append(match[1])
                pos += match.end()
            elif marker:
                pos += marker.end()
            else:
                break
    return result


def source_closure(read, roots=IMPORTS):
    """Exact source closure of the imports built for reflection; no type parsing."""
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
    # A group with its own `Tool` writes no codec; only the codec groups consume the wire.
    consumers = {'deriving:' + g['Name']: g['Types'] for g in manifest['groups'] if 'Tool' not in g}
    selection = optional(read, PROGRAM_STRUCTURE)
    if selection is not None:
        # The family selection's one home since the program structure tool: the wire manifest
        # and the OCaml world both read `Tools.ProgramStructure.blocks`.
        names = re.findall(r'⟨`([\w.]+),', body(selection, 'def blocks : List (List Spec) :=', 'def allSpecs'))
        if not names:
            raise ValueError('program structure: empty family selection')
        consumers['wire'] = list(names)
        consumers['ocaml-world'] = list(names)
    else:
        wire = body(read('src/OCaml5/Tools/EffWire.lean'), 'let families : List Lean.Name := [', ']')
        consumers['wire'] = re.findall(r'`([\w.]+)', wire)
        world = body(read('src/OCaml5/Eff/World.lean'), 'def blocks : List (List Spec) :=', 'def allSpecs')
        consumers['ocaml-world'] = re.findall(r'⟨`([\w.]+),', world)
    return maps, framing, consumers


def baseline_name(name):
    """A baseline is named once: lower-case words and digits joined by hyphens."""
    if not isinstance(name, str) or not re.fullmatch(r'[0-9a-f]{8}(-[a-z0-9]+)+', name):
        raise ValueError('promotion: a baseline name is eight revision digits, then hyphenated words')
    return name


def extract(root, revision, reflection, build_receipt, inventory):
    revision = resolve_revision(root, revision)
    read = lambda path: git_bytes(root, revision, path)
    closure = source_closure(read)
    # The wrapper owns this receipt only after a build of the frozen checkout.
    if build_receipt != {'revision': revision, 'toolchain': read('lean-toolchain').decode().strip(),
                          'source_closure': closure, 'reflection_sha256': digest(canonical(reflection).encode())}:
        raise ValueError('reflection provenance differs from requested frozen source closure')
    # The retained inventory names the constructors of the original revision only. A later
    # revision keeps the inventory's family selection and brings its own constructors.
    return assemble(reflection, build_receipt, inventory, read, require_retained_names=revision == BASE)


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
    tags = wire_tags(read)
    if tags is not None:
        apply_tags(families, tags)
    # A revision from before the assignment keeps the first format: there a tag is the ordinal.
    result = {'format': FORMAT if tags is None else FORMAT_TAGGED, 'source': build_receipt,
              'roots': roots, 'families': families,
              'byte_maps': maps, 'framing': framing, 'consumers': consumers}
    validate(result)
    return result
