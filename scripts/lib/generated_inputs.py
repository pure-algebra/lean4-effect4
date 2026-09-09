"""Read the generated-file map and recompute the Lean stamp protocol without Lean."""
import functools
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DEFERRED_ARTIFACTS = {'ocaml/avatar/deep_stores.ml', 'ocaml/avatar/deep_layer.ml',
                      'ocaml/avatar/deep_context.ml', 'ocaml/avatar/deep_forkflow.ml',
                      'generated/schema-structural-assurance.tsv'}


def inventory():
    for line in (ROOT / 'docs/GENERATED.md').read_text().splitlines():
        if not line.startswith('| `'):
            continue
        fields = [s.strip() for s in line.strip('|').split('|')]
        if len(fields) == 8 and fields[7] == 'yes':
            yield fields[0].strip('`'), fields[2]


def data_recipe(family):
    if family == 'Archived daemon inputs':
        manifest = 'ocaml/server/generated/archived-from.tsv'
        outputs = [manifest] + ['ocaml/server/' + row.split('\t')[0]
                                for row in (ROOT / manifest).read_text().splitlines()[1:]]
        source = 'ocaml/server/tools/vendor-archived-inputs.sh'
        inputs = outputs
    else:
        census = family == 'Runtime census'
        outputs = ['generated/' + ('effect-runtime-census.tsv' if census else 'schema-structural-assurance.tsv')]
        source = 'scripts/generate-' + ('effect-runtime-census.sh' if census else 'schema-structural-assurance.sh')
        inputs = outputs + [field for line in (ROOT / outputs[0]).read_text().splitlines()
                            for field in line.split('\t')
                            if re.fullmatch(r'[A-Za-z0-9_./-]+', field) and (ROOT / field).is_file()]
    return source, [], sorted(set(inputs + ['scripts/generate-data-stamps.py'])), outputs


@functools.lru_cache(None)
def recipe(path, family):
    if family.startswith('Derived '):
        group = next(g for g in json.loads((ROOT/'tools/Effect4Gen/manifest.json').read_text())['groups']
                     if g['Name'] == family.removeprefix('Derived '))
        return 'tools/Effect4Gen/Main.lean', group['Imports'].split(','), ['tools/Effect4Gen/manifest.json', group['Guards'].replace('\\', '/')]
    if family in ['Eff', 'Eff goldens']:
        return 'src/OCaml5/Tools/EffGen.lean', ['Effect4.Program.Native'], []
    if family == 'Wire goldens':
        return 'src/OCaml5/Tools/EffWire.lean', [], []
    if family == 'CAS goldens':
        return 'src/OCaml5/Tools/CasGoldens.lean', [], []
    if family == 'TypeScript':
        return 'tools/Tools/TsGen.lean', ['Effect4.Program.Native'], ['lakefile.toml', 'src/Effect4/Codegen/Print.lean']
    if family == 'Avatar descriptions':
        return 'src/OCaml5/Tools/Describe.lean', ['Effect4.Machine.' + n for n in ['Fibers', 'Stores', 'Context', 'Scope', 'Key']], []
    if family == 'Avatar blocks':
        return 'src/OCaml5/Tools/RenderDeep.lean', [], []
    if family == 'Truth':
        return 'harness/truth/Truth.lean', [], ['harness/truth/run-truth.ts', 'harness/truth/prelude.ts', 'ts/eff/package.json', 'ts/eff/bun.lock']
    if family == 'Schema TypeScript':
        source = {'Person': 'EmitFixture', 'AllRepresentations': 'EmitCoverageFixture', 'TwoRoots': 'EmitMultiFixture'}[Path(path).name.split('.')[0]]
        return 'harness/schema-generation/' + source + '.lean', [], []
    if family in ['Runtime census', 'Schema assurance', 'Archived daemon inputs']:
        source, modules, files, _ = data_recipe(family)
        return source, modules, files
    raise ValueError(f'No stamp recipe for {path}: {family}')


@functools.lru_cache(None)
def read(path):
    return Path(path).read_bytes()


def imports(data):
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


@functools.lru_cache(None)
def trace(name):
    tail = Path(*name.split('.')).with_suffix('.trace')
    candidates = [ROOT/'.lake/build/lib/lean'/tail]
    candidates += [p/'.lake/build/lib/lean'/tail for p in (ROOT/'.lake/packages').iterdir() if p.is_dir()]
    path = next((p for p in candidates if p.is_file()), None)
    if path is None:
        raise ValueError(f'missing Lake trace for {name}; build its imports')
    value = json.loads(read(path))
    source = next((p for p, _ in value['inputs'] if p.endswith('.lean')), None)
    if source is None:
        raise ValueError(f'Lake trace has no source input: {path}')
    return value['depHash'], read(source)


@functools.lru_cache(None)
def digest(source, modules, files):
    pending = (imports(read(ROOT/source)) if source.endswith(".lean") else []) + list(modules)
    seen, rows = set(), []
    while pending:
        name = pending.pop()
        if name.split('.')[0] in {'Lean', 'Init', 'Std'} or name in seen:
            continue
        seen.add(name)
        if len(seen) > 8192:
            raise ValueError('stamp import closure exceeds 8192 entries')
        dep, data = trace(name)
        rows.append(f'trace {name} {dep} source={hashlib.sha256(data).hexdigest()}\n')
        pending += imports(data)
    rows.sort()
    for path in sorted(set([source] + [p.replace('\\', '/') for p in files])):
        rows.append(f'file {path} {hashlib.sha256(read(ROOT/path)).hexdigest()}\n')
    return hashlib.sha256(''.join(rows).encode()).hexdigest()


def expected(path, family):
    source, modules, files = recipe(path, family)
    return digest(source, tuple(modules), tuple(files))


def recorded(path):
    p = ROOT/path
    if not p.is_file():
        raise ValueError(f'missing generated artifact: {path}')
    sidecar = Path(str(p) + '.cut-from')
    data = read(sidecar) if sidecar.is_file() else read(p)
    matches = re.findall(rb'(?m)^(?:// |-- |\(\* |<!-- |)?cut-from: rev=\S+ toolchain=(\S+) inputs=([0-9a-f]{64})(?: \*\)| -->)?$', data)
    if len(matches) != 1:
        raise ValueError(f'{path}: expected exactly one provenance stamp')
    return tuple(x.decode() for x in matches[0])
