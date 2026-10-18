"""Check the compact tool table against the exact one it replaced (JSON Schema Draft 2020-12).

Usage, from the repository root, with python `jsonschema` installed:
    python3 docs/research/2026-10-18-mcp-schema-size/validate.py BEFORE.json ocaml/_build/default/engine/kit/bin/eff.exe

BEFORE.json is the `tools/list` reply of `eff mcp` built at the base commit (8a08e0415). The script
asks the given `eff mcp` for its `tools/list`, every `describe` answer, and a short session (open,
start, run record) whose replies give real `start`, `restore`, `fill` and `dry` arguments.

Properties, each a finite probe:
V1 every new schema and every `describe` answer is a valid 2020-12 schema;
V2 every fixture request's arguments (and every generated call) get the same verdict from the old
   schema, the new schema, and the new schema resolved: each `describe` pointer replaced by its
   answer, `dry`'s action by the action tools' schemas;
V3 on mutations of those arguments (an extra property, a wrong `_tag`, a missing field, a wrong
   scalar) the resolved schema and the old one agree, and the new schema accepts all the old one
   accepts;
V4 instances drawn at random from each old schema are valid against the new and resolved ones.
"""
import copy
import json
import random
import subprocess
import sys

from jsonschema import Draft202012Validator

FIXTURES = ['ocaml/engine/test/kit/tool-requests.jsonl', 'ocaml/engine/test/kit/tool-numbers.jsonl',
            'Test/fixtures/session/requests.jsonl']


HANDSHAKE = [{'jsonrpc': '2.0', 'id': 'init', 'method': 'initialize',
              'params': {'protocolVersion': '2025-06-18', 'capabilities': {},
                         'clientInfo': {'name': 'validate', 'version': '1'}}},
             {'jsonrpc': '2.0', 'method': 'notifications/initialized'}]


def mcp(exe, messages):
    """The replies of one `eff mcp` session to some messages, after the MCP handshake."""
    text = ''.join(json.dumps(m) + '\n' for m in HANDSHAKE + messages)
    out = subprocess.run([exe, 'mcp'], input=text, capture_output=True, text=True, check=True).stdout
    return [json.loads(line) for line in out.splitlines()][1:]


def call(i, name, args):
    return {'jsonrpc': '2.0', 'id': i, 'method': 'tools/call', 'params': {'name': name, 'arguments': args}}


def tools_of(reply):
    return {t['name']: t['inputSchema'] for t in reply['result']['tools']}


def stub(d):
    return set(d) == {'type', 'description'}


def resolve(schema, answers, action_tools=None):
    """The schema with each `describe` pointer replaced by its answer, and a tool-call sum by the tools'."""
    s = copy.deepcopy(schema)
    defs = s.setdefault('$defs', {})

    def merge(more):
        for k, v in more.items():
            if k not in defs or stub(defs[k]):
                defs[k] = v

    if action_tools is not None:
        for name, prop in list(s['properties'].items()):
            if prop.get('description', '').startswith("One tool's call"):
                branches = []
                for case, tool in zip(prop['properties']['_tag']['enum'], action_tools):
                    merge(tool.get('$defs', {}))
                    branches.append({'type': 'object',
                                     'properties': {'_tag': {'const': case}, **tool['properties']},
                                     'required': ['_tag', *tool['required']], 'additionalProperties': False})
                s['properties'][name] = {'oneOf': branches}
    while any(stub(v) for v in defs.values()):
        for k in [k for k, v in defs.items() if stub(v)]:
            merge(answers[k]['$defs'])
            defs[k] = answers[k]['$defs'][k]
    if not defs:
        del s['$defs']
    return s


def mutations(x, rng, limit=60):
    """Variants of an argument object, each one edit away."""
    out = []

    def walk(node, path):
        if isinstance(node, dict):
            out.append((path, 'extra'))
            for k, v in node.items():
                if k == '_tag':
                    out.append((path, 'tag'))
                else:
                    out.append((path + [k], 'drop'))
                    walk(v, path + [k])
        elif isinstance(node, list):
            for i, v in enumerate(node):
                walk(v, path + [i])
        elif isinstance(node, bool):
            out.append((path, 'scalar'))
        elif isinstance(node, (int, str)):
            out.append((path, 'scalar'))

    walk(x, [])
    rng.shuffle(out)
    variants = []
    for path, kind in out[:limit]:
        y = copy.deepcopy(x)
        parent, last = None, None
        node = y
        for p in path:
            parent, last, node = node, p, node[p]
        if kind == 'extra':
            node['zzz'] = 1
        elif kind == 'tag':
            node['_tag'] = 'zzz'
        elif kind == 'drop':
            del parent[last]
        else:
            parent[last] = -1 if isinstance(node, str) else 'x'
        variants.append(y)
    return variants


def sample(schema, root, rng, depth=0):
    """A random instance of a schema; past depth 6, the branch with the fewest pointers."""
    if '$ref' in schema:
        return sample(root['$defs'][schema['$ref'].split('/')[-1]], root, rng, depth + 1)
    if 'const' in schema:
        return schema['const']
    if 'enum' in schema:
        return rng.choice(schema['enum'])
    for key in ('oneOf', 'anyOf'):
        if key in schema:
            branches = schema[key]
            pick = (min(branches, key=lambda b: json.dumps(b).count('$ref')) if depth > 6
                    else rng.choice(branches))
            rest = {k: v for k, v in schema.items() if k != key}
            return sample({**rest, **pick} if rest else pick, root, rng, depth + 1)
    t = schema.get('type')
    if t == 'object' or 'properties' in schema:
        return {k: sample(v, root, rng, depth + 1) for k, v in schema.get('properties', {}).items()}
    if t == 'array':
        if 'prefixItems' in schema:
            return [sample(v, root, rng, depth + 1) for v in schema['prefixItems']]
        n = 0 if depth > 6 else rng.randint(0, 2)
        return [sample(schema['items'], root, rng, depth + 1) for _ in range(n)]
    if t == 'integer':
        return rng.choice([0, 1, 7, schema.get('maximum', 9)])
    if t == 'string':
        return 'ab' if 'pattern' in schema and '{64}' not in schema['pattern'] else (
            '0' * 64 if 'pattern' in schema else 'x')
    if t == 'boolean':
        return rng.choice([True, False])
    if t == 'null':
        return None
    return {}


def main(before_path, exe):
    rng = random.Random(20261018)
    before = tools_of(json.load(open(before_path)))
    after = tools_of(mcp(exe, [{'jsonrpc': '2.0', 'id': 1, 'method': 'tools/list'}])[0])
    names = after['describe']['properties']['name']['enum']
    answers = {}
    for n, r in zip(names, mcp(exe, [call(i, 'describe', {'name': n}) for i, n in enumerate(names)])):
        assert not r['result']['isError'], n
        answers[n] = json.loads(r['result']['content'][0]['text'])
    acts = ['open', 'edit', 'fill', 'publish', 'reset', 'start', 'restore', 'play']
    resolved = {n: resolve(s, answers, [after[a] for a in acts] if n == 'dry' else None)
                for n, s in after.items() if n != 'describe'}
    check = {k: {n: Draft202012Validator(s) for n, s in table.items()}
             for k, table in (('before', before), ('after', after), ('resolved', resolved))}

    # V1
    for s in list(after.values()) + list(answers.values()) + list(resolved.values()):
        Draft202012Validator.check_schema(s)
    print(f'V1 {len(after)} tool schemas, {len(answers)} describe answers, {len(resolved)} resolved: valid 2020-12')

    # the calls: fixtures, then a session's real arguments
    calls = []
    for path in FIXTURES:
        for line in open(path):
            if not line.strip():
                continue
            req = json.loads(line)
            body = req.get('payload', {})
            arg = body.get('a', body.get('q'))
            if req.get('method') in after and isinstance(arg, dict):
                calls.append((path.split('/')[-1], req['method'], {k: v for k, v in arg.items() if k != '_tag'}))
    opened = [c for c in calls if c[1] == 'open'][0][2]
    replies = mcp(exe, [call(1, 'open', opened)])
    view = json.loads(replies[0]['result']['content'][0]['text'])

    def find(node, keys):
        if isinstance(node, dict):
            if set(node) == keys:
                return node
            node = list(node.values())
        if isinstance(node, list):
            for v in node:
                hit = find(v, keys)
                if hit is not None:
                    return hit
        return None

    snap = find(view, {'doc', 'revision'})
    budget = {'fuel': 2000, 'compileFuel': 2000}
    replies = mcp(exe, [call(1, 'open', opened), call(2, 'start', {'at_': snap, 'budget': budget})])
    started = json.loads(replies[1]['result']['content'][0]['text'])
    run_id = find(started, {'n'})
    replies = mcp(exe, [call(1, 'open', opened), call(2, 'start', {'at_': snap, 'budget': budget}),
                        call(3, 'run', {'id': run_id, 'form': 'record'})])
    record = find(json.loads(replies[2]['result']['content'][0]['text']), set(after['restore']['properties']['record']['properties']))
    session = [('session', 'start', {'at_': snap, 'budget': budget}),
               ('session', 'run', {'id': run_id, 'form': 'journal'}),
               ('session', 'fill', {'at_': snap, 'batch': [[[0], opened['sketch']['program']]]}),
               ('session', 'suggest', {'at_': snap, 'place': {'_tag': 'hole', 'index': 0}, 'supplied': [], 'cursor': 0, 'limit': 5}),
               ('session', 'preview', {'q': {'_tag': 'settle', 'tape': [], 'limit': 10}})]
    if record is not None:
        session.append(('session', 'restore', {'record': record}))
    calls += session
    calls += [(src + ' (dry)', 'dry', {'a': {'_tag': 'open_' if m == 'open' else m, **args}})
              for src, m, args in list(calls) if m in acts]

    # V2, V3
    agree = disagree = mutated = loose = 0
    per = {}
    for src, method, args in calls:
        verdicts = {k: check[k][method].is_valid(args) for k in check}
        per.setdefault(method, [0, 0])[0 if verdicts['before'] else 1] += 1
        if len(set(verdicts.values())) == 1:
            agree += 1
        else:
            disagree += 1
            print('V2 DISAGREE', src, method, verdicts)
        for y in mutations(args, rng):
            b, a, r = (check[k][method].is_valid(y) for k in ('before', 'after', 'resolved'))
            mutated += 1
            if b != r or (b and not a):
                print('V3 DISAGREE', src, method, b, a, r)
                disagree += 1
            loose += (a and not b)
    print(f'V2 {len(calls)} calls ({", ".join(f"{m} {v[0]}+/{v[1]}-" for m, v in per.items())}): '
          f'{agree} agree across old, new and resolved')
    print(f'V3 {mutated} mutations: resolved agrees with old on all; new accepts all old accepts; '
          f'{loose} accepted by the new schema only (inside a describe pointer or dry\'s action)')

    # V4
    drawn = 0
    for method, schema in before.items():
        for _ in range(25):
            x = sample(schema, schema, rng)
            if not check['before'][method].is_valid(x):
                continue
            drawn += 1
            if not (check['after'][method].is_valid(x) and check['resolved'][method].is_valid(x)):
                print('V4 DISAGREE', method)
                disagree += 1
    print(f'V4 {drawn} instances drawn from the old schemas: valid against new and resolved')
    print('PASS' if disagree == 0 else f'FAIL {disagree}')
    return 0 if disagree == 0 else 1


if __name__ == '__main__':
    sys.exit(main(*sys.argv[1:]))
