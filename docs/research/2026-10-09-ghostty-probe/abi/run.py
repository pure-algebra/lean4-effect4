#!/usr/bin/env python3
"""Bounded public-header signature probe; no linking, execution or native build."""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import urllib.request

PIN = '246f702876b924a1cb7cade1e99274d1470302fc'
ROOTS = ('include/ghostty/vt/terminal.h', 'include/ghostty/vt/render.h')
OPERATIONS = (
    'ghostty_terminal_new', 'ghostty_terminal_free', 'ghostty_terminal_vt_write',
    'ghostty_terminal_resize', 'ghostty_terminal_get',
    'ghostty_render_state_new', 'ghostty_render_state_free',
    'ghostty_render_state_update', 'ghostty_render_state_get', 'ghostty_render_state_clean',
)
INCLUDES = '#include <ghostty/vt/terminal.h>\n#include <ghostty/vt/render.h>\n'
HERE = pathlib.Path(__file__).resolve().parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

def save_json(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')

def call(command):
    return subprocess.run(command, text=True, capture_output=True, check=False)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cache', type=pathlib.Path, default=pathlib.Path('/private/tmp/ghostty-abi-246f7028'))
    ap.add_argument('--clang', default='clang')
    ap.add_argument('--offline', action='store_true', help='Refuse absent headers; verify cached bytes against retained manifest.')
    args = ap.parse_args()
    cache = args.cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    manifest_path = HERE / 'manifest.generated.json'
    old = json.loads(manifest_path.read_text()) if manifest_path.exists() else None
    if old is not None:
        assert old['upstream_pin'] == PIN
    elif args.offline:
        raise RuntimeError('offline replay requires the retained manifest')
    seen = {}
    todo = list(ROOTS)
    while todo:
        path = todo.pop(0)
        if path in seen:
            continue
        assert re.fullmatch(r'include/ghostty/vt/[a-z_]+\.h', path), path
        assert len(seen) < 40, 'bounded closure exceeded'
        dst = cache / path
        if not args.offline:
            url = f'https://raw.githubusercontent.com/ghostty-org/ghostty/{PIN}/{path}'
            with urllib.request.urlopen(url, timeout=30) as response:
                data = response.read(500001)
            assert len(data) <= 500000, 'header byte bound exceeded'
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(data)
        data = dst.read_bytes()
        digest = sha(data)
        if old is not None:
            assert path in old['headers'], f'unexpected header: {path}'
            assert digest == old['headers'][path]['sha256'], f'changed header: {path}'
        seen[path] = {
            'sha256': digest, 'bytes': len(data),
            'url': f'https://raw.githubusercontent.com/ghostty-org/ghostty/{PIN}/{path}',
        }
        todo.extend('include/' + inc for inc in re.findall(
            r'^\s*#\s*include\s*[<"](ghostty/vt/[^>"]+)[>"]', data.decode(), re.M))
    if old is not None:
        assert set(seen) == set(old['headers']), 'header closure changed'

    version = call([args.clang, '--version'])
    target = call([args.clang, '-dumpmachine'])
    assert version.returncode == target.returncode == 0
    flags = [args.clang, '-std=c11', '-Wall', '-Wextra', '-Werror', '-I', str(cache / 'include')]
    unit = cache / 'input.c'
    unit.write_text(INCLUDES)
    ast_command = flags + ['-Xclang', '-ast-dump=json', '-fsyntax-only', str(unit)]
    ast_result = call(ast_command)
    assert ast_result.returncode == 0, ast_result.stderr
    ast = json.loads(ast_result.stdout)
    declarations = {}
    for node in ast['inner']:
        if node.get('kind') != 'FunctionDecl' or node.get('name') not in OPERATIONS:
            continue
        name = node['name']
        assert name not in declarations, f'duplicate declaration: {name}'
        begin = node['range']['begin'].get('expansionLoc', node['range']['begin'])
        end = node['range']['end'].get('expansionLoc', node['range']['end'])
        source = pathlib.Path(begin['file'])
        relative = source.relative_to(cache).as_posix()
        assert relative in seen
        raw = source.read_bytes()[begin['offset']:end['offset'] + end['tokLen']]
        params = [{'name': p['name'], 'type': p['type']['qualType']}
                  for p in node.get('inner', []) if p['kind'] == 'ParmVarDecl']
        qual = node['type']['qualType']
        result, rest = qual.split(' (', 1)
        assert rest.endswith(')')
        assert rest[:-1] == ', '.join(p['type'] for p in params), 'unsupported signature shape'
        declarations[name] = {
            'type': qual, 'result': result, 'parameters': params,
            'header': relative, 'line': begin['line'],
            'declaration': raw.decode(), 'declaration_sha256': sha(raw),
        }
    assert set(declarations) == set(OPERATIONS), 'omitted operation'
    manifest = {
        'upstream_pin': PIN, 'headers': seen,
        'roots': list(ROOTS), 'operations': declarations,
        'generator': 'run.py, Clang JSON FunctionDecl/ParmVarDecl extraction',
        'target': target.stdout.strip(),
        'scope': 'C header signature checks only; not linked or executed',
        'manual_selector_profile': {
            'GHOSTTY_TERMINAL_DATA_COLS': 'uint16_t *',
            'GHOSTTY_RENDER_STATE_DATA_COLS': 'uint16_t *',
        },
    }
    if old is not None:
        assert manifest == old, 'generated manifest changed; inspect before replacing evidence'
    save_json(manifest_path, manifest)
    banner = '/* Generated by run.py from the pinned public Clang AST. Do not edit. */\n'
    positive = banner + INCLUDES
    for name in OPERATIONS:
        row = declarations[name]
        params = ', '.join(p['type'] for p in row['parameters']) or 'void'
        positive += f'typedef {row["result"]} (*abi_{name})({params});\n'
        positive += f'abi_{name} const check_{name} = &{name};\n'
        positive += f'_Static_assert(__builtin_types_compatible_p(__typeof__(&{name}), abi_{name}), "{name}");\n'
    negative = banner + INCLUDES + '''/* Independently chosen defect: vt_write returns void, not GhosttyResult. */
GhosttyResult (*const wrong_feed_result)(GhosttyTerminal, const uint8_t *, size_t) = &ghostty_terminal_vt_write;
'''
    # Selector types are manually taken from public enum documentation, not the void* prototype.
    typed = '''/* Generated by run.py from the explicitly manual two-selector profile. */
#ifndef GHOSTTY_PROBE_TYPED_GETTERS_H
#define GHOSTTY_PROBE_TYPED_GETTERS_H
''' + INCLUDES + '''static inline GhosttyResult probe_terminal_cols(GhosttyTerminal t, uint16_t *out) {
    return ghostty_terminal_get(t, GHOSTTY_TERMINAL_DATA_COLS, out);
}
static inline GhosttyResult probe_render_cols(GhosttyRenderState s, uint16_t *out) {
    return ghostty_render_state_get(s, GHOSTTY_RENDER_STATE_DATA_COLS, out);
}
#endif
'''
    controls = banner + '#include "typed-getters.generated.h"\n' + '''GhosttyResult probe_good_terminal(GhosttyTerminal t, uint16_t *out) {
    return probe_terminal_cols(t, out);
}
GhosttyResult probe_good_render(GhosttyRenderState s, uint16_t *out) {
    return probe_render_cols(s, out);
}
/* Deliberately incorrect storage type: accepted through void*, never run. */
GhosttyResult probe_raw_bad_terminal(GhosttyTerminal t, uint8_t *out) {
    return ghostty_terminal_get(t, GHOSTTY_TERMINAL_DATA_COLS, out);
}
GhosttyResult probe_raw_bad_render(GhosttyRenderState s, uint8_t *out) {
    return ghostty_render_state_get(s, GHOSTTY_RENDER_STATE_DATA_COLS, out);
}
'''
    negative_selector = banner + '#include "typed-getters.generated.h"\n' + '''GhosttyResult probe_bad_typed_terminal(GhosttyTerminal t, uint8_t *out) {
    return probe_terminal_cols(t, out);
}
'''
    products = {
        'signatures.generated.c': positive,
        'negative-signature.generated.c': negative,
        'typed-getters.generated.h': typed,
        'selector-controls.generated.c': controls,
        'negative-selector.generated.c': negative_selector,
    }
    for file, text in products.items():
        dst = HERE / file
        if old is not None and dst.exists():
            assert dst.read_text() == text, f'generated bytes changed: {file}'
        dst.write_text(text)
    results = {}
    expectations = {
        'signatures.generated.c': (0, None),
        'negative-signature.generated.c': (1, 'ghostty_terminal_vt_write'),
        'selector-controls.generated.c': (0, None),
        'negative-selector.generated.c': (1, 'probe_terminal_cols'),
    }
    for file, (expected, symbol) in expectations.items():
        command = flags + ['-c', str(HERE / file), '-o', str(cache / (file + '.o'))]
        result = call(command)
        log_name = file + '.diagnostics.txt'
        (HERE / log_name).write_text(result.stdout + result.stderr)
        assert (result.returncode == 0) == (expected == 0), (file, result.stderr)
        if expected:
            assert 'incompatible' in result.stderr and symbol in result.stderr, result.stderr
            assert re.search(r'1 error generated\.', result.stderr), 'unexpected additional diagnostic'
        else:
            assert not result.stdout and not result.stderr, 'unexpected positive diagnostics'
            assert (cache / (file + '.o')).stat().st_size > 0
        results[file] = {
            'command': command, 'exit_code': result.returncode,
            'expected': 'compile succeeds' if expected == 0 else 'incompatible type refusal',
            'source_sha256': sha((HERE / file).read_bytes()),
            'diagnostics_sha256': sha((HERE / log_name).read_bytes()),
        }
    receipt = {
        'upstream_pin': PIN, 'generator_sha256': sha(pathlib.Path(__file__).read_bytes()),
        'compiler': version.stdout.strip(),
        'target': target.stdout.strip(), 'ast_command': ast_command,
        'header_count': len(seen), 'operation_count': len(declarations),
        'manifest_sha256': sha(manifest_path.read_bytes()), 'results': results,
        'generated_hashes': {name: sha((HERE / name).read_bytes()) for name in products},
        'limits': [
            'No Ghostty library linked or executed; no observed terminal behavior.',
            'No Lean theorem or production binding; only selected C declarations.',
            'No GPU, font, window, macOS internal API, Zig or full application build.',
            'Selector/output relations are manual public-documentation inputs, not inferred by Clang.',
            'Compile success does not prove lifetime, aliasing, threading, ABI implementation or allocator contracts.',
            'Only the recorded host target checked; public API explicitly unstable.',
        ],
    }
    save_json(HERE / 'compiler-run.json', receipt)
    print(f'PASS: {len(declarations)} signatures, {len(seen)} headers; two positives and two expected type refusals.')

if __name__ == '__main__':
    main()
