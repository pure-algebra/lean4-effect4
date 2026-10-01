#!/usr/bin/env python3
"""Read-only row-39 checks. JSON to stdout; exit 1 on any failed check."""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

REGISTER = 'Test/Counterexamples/REGISTER.md'
ARCHIVE = 'Test/Counterexamples/Archive/REGISTER.md'
SCAN_ROOTS = ('src', 'Test', 'tools', 'harness')
SKIP_DIRS = {'.git', '.lake', 'node_modules', '_build', 'build', 'dist'}
ROW = re.compile(r'^\| `(E4-[^`]+)` \|')
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')
DUPLICATE_NOTES = {
    'E4-TYPED-CE-003': 'Different attacks: current StrongCause/Die shape-defect exclusion versus historical loss of nonnumeric failure payloads during compilation.',
    'E4-SCHED-CE-004': 'Different attacks: current race source-location premise versus historical bind-based interruption cleanup distinction.',
    'E4-PROV-CE-005': 'Different attacks: current layer-build environment isolation versus historical middleware provider/consumer order.',
    'E4-PROV-CE-006': 'Different attacks: current layer value/service carrier fit versus historical string deployment law and binding-row disagreement.',
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, *args):
    return subprocess.check_output(['git', *args], cwd=repo, stderr=subprocess.PIPE)


def strip_comments_strings(text):
    """Mask nested Lean comments and quoted strings, retaining line positions."""
    out = list(text)
    i, depth = 0, 0
    while i < len(text):
        start = i
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
        elif text.startswith('/-', i): depth = 1; i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            raw = re.match(r'r(#+)?"', text[i:]) if text[i] == 'r' and (i == 0 or not (text[i-1].isalnum() or text[i-1] == '_')) else None
            char = re.match(r"'(?:\\.|[^'\\\n])'", text[i:]) if text[i] == "'" else None
            if raw:
                close = '"' + (raw.group(1) or '')
                end = text.find(close, i + len(raw.group()))
                i = len(text) if end < 0 else end + len(close)
            elif text[i] == '"':
                i += 1
                while i < len(text):
                    if text[i] == '\\': i += 2
                    elif text[i] == '"': i += 1; break
                    else: i += 1
            elif char: i += len(char.group())
            else: i += 1; continue
        for j in range(start, min(i, len(text))):
            if out[j] != '\n': out[j] = ' '
    return ''.join(out)


def imports(text):
    found = []
    for line_no, line in enumerate(strip_comments_strings(text).splitlines(), 1):
        m = re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+)$', line)
        if m:
            found.extend((name, line_no) for name in MODULE.findall(m.group(1)))
    return found


def module_name(path):
    if path.startswith('src/'): path = path[4:]
    elif path.startswith('tools/'): path = path[6:]
    return path[:-5].replace('/', '.')


def table_rows(text):
    result = defaultdict(list)
    for line_no, line in enumerate(text.splitlines(), 1):
        if m := ROW.match(line): result[m.group(1)].append({'line': line_no, 'row': line})
    return dict(result)


class View:
    def __init__(self, repo, overrides=None):
        self.repo, self.overrides = repo, overrides or {}

    def read(self, path):
        if path in self.overrides: return self.overrides[path]
        p = self.repo / path
        return p.read_bytes() if p.is_file() else None

    def lean_paths(self):
        paths = set()
        for folder in SCAN_ROOTS:
            for p in (self.repo / folder).rglob('*.lean'):
                rel = p.relative_to(self.repo)
                if not any(part in SKIP_DIRS for part in rel.parts): paths.add(rel.as_posix())
        paths.update(p for p in self.overrides if p.endswith('.lean') and p.split('/')[0] in SCAN_ROOTS)
        return sorted(p for p in paths if self.read(p) is not None)


def validate(repo, bundle, overrides=None):
    view = View(repo, overrides)
    series = json.loads((bundle/'series.json').read_text())
    baseline = json.loads((bundle/'prechange-byte-baseline/manifest.json').read_text())
    migration = json.loads((bundle/'register-closure/manifest.json').read_text())
    originals = json.loads((bundle/'register-closure/original-rows.json').read_text())
    report = {'kind':'row39_read_only_static_validation', 'view':'test_projection' if overrides else 'live_worktree',
              'head':git(repo,'rev-parse','HEAD').decode().strip(), 'source_base':series['base'],
              'scope':'Live src/Test/tools/harness only; docs/research and copied historical evidence are excluded from import scanning.',
              'limits':'Byte/source/import/register checks only. No compiler, generator, proof, host execution, or semantic equivalence claim.',
              'checks':{}, 'failures':[]}
    def check(name, ok, details):
        report['checks'][name]={'ok':bool(ok), **details}
        if not ok: report['failures'].append(name)

    artifacts=[]
    for a in baseline['artifacts']:
        current=view.read(a['path'])
        pinned=git(repo,'cat-file','blob',f"{baseline['base_commit']}:{a['path']}")
        blob=git(repo,'rev-parse',f"{baseline['base_commit']}:{a['path']}").decode().strip()
        copied=(bundle/'prechange-byte-baseline'/a['path']).read_bytes() if a['copied'] else None
        ok=(current is not None and len(current)==a['bytes'] and digest(current)==a['sha256']
            and digest(pinned)==a['sha256'] and blob==a['git_blob'] and current==pinned
            and (not a['copied'] or copied==pinned))
        artifacts.append({'path':a['path'],'ok':ok,'bytes':len(current) if current is not None else None,
                          'expected_sha256':a['sha256'],'actual_sha256':digest(current) if current is not None else None,
                          'pinned_blob':blob,'retained_copy_checked':a['copied']})
    check('prechange_artifact_bytes',all(a['ok'] for a in artifacts),{'count':len(artifacts),'artifacts':artifacts})

    expected={}
    for stage in series['stages']:
        for row in stage['changes']: expected[row['path']]=row['new_sha256']
    for stage in migration['stages']:
        for row in stage['changes']: expected[row['path']]=row['new_sha256']
    hashes=[]
    for path,want in sorted(expected.items()):
        data=view.read(path);actual=digest(data) if data is not None else None
        hashes.append({'path':path,'expected_sha256':want,'actual_sha256':actual,'ok':actual==want,
                       'expected_state':'deleted' if want is None else 'present'})
    check('final_source_hashes',all(row['ok'] for row in hashes),{'count':len(hashes),'paths':hashes})
    deleted={p for p,want in expected.items() if want is None}
    deleted_modules={module_name(p) for p in deleted if p.endswith('.lean')}

    live_data=view.read(REGISTER);archive_data=view.read(ARCHIVE)
    live=live_data.decode() if live_data is not None else ''
    archive=archive_data.decode() if archive_data is not None else ''
    tables={REGISTER:table_rows(live),ARCHIVE:table_rows(archive)}
    counts=Counter({id:len(rows) for id,rows in tables[REGISTER].items()})
    counts.update({id:len(rows) for id,rows in tables[ARCHIVE].items()})
    moved=[]
    for item in originals:
        id=item['id'];rows=tables[ARCHIVE].get(id,[])
        moved.append({'id':id,'ok':counts[id]==1 and id not in tables[REGISTER] and len(rows)==1 and rows[0]['row']==item['original_row']})
    mixed=[]
    for item in migration['mixed_rows']:
        id=item['id'];rows=tables[REGISTER].get(id,[])
        mixed.append({'id':id,'ok':counts[id]==1 and len(rows)==1 and rows[0]['row']==item['proposed_row']})
    residual=[]
    for id,rows in tables[REGISTER].items():
        for row in rows:
            for token in re.findall(r'`([^`]+)`',row['row']):
                if token in deleted: residual.append({'id':id,'line':row['line'],'path':token})
    pins=[]
    for stage in migration['stages']:
        for p in stage['source_pins']:
            ref=f"{p['revision']}:{p['path']}"
            actual=git(repo,'rev-parse',ref).decode().strip()
            pin=f'git:{ref}'
            pins.append({'path':p['path'],'ok':actual==p['blob'] and pin in archive,'revision':p['revision'],'blob':actual})
    for item in migration['mixed_rows']:
        ref=f"{item['revision']}:{item['retired_path']}"
        git(repo,'cat-file','-e',ref)
    check('retired_registered_witnesses',all(r['ok'] for r in moved+mixed+pins) and not residual,
          {'moved_count':len(moved),'moved':moved,'retained_mixed_rows':mixed,'source_pins':pins,'bare_deleted_paths_in_live_rows':residual})

    oldcounts=Counter()
    for path in (REGISTER,ARCHIVE):
        old=table_rows(git(repo,'show',f"{migration['captured_head']}:{path}").decode())
        oldcounts.update({id:len(rows) for id,rows in old.items()})
    oldduplicates={id:n for id,n in sorted(oldcounts.items()) if n>1}
    duplicates={id:n for id,n in sorted(counts.items()) if n>1}
    debt=[]
    for id,n in duplicates.items():
        attacks=[]
        for path,table in tables.items():
            for row in table.get(id,[]):
                attacks.append({'register':path,'line':row['line'],'attacked_statement':row['row'].split('|')[3].strip()})
        debt.append({'id':id,'count':n,'assessment':DUPLICATE_NOTES.get(id,'Unclassified duplicate: not in reviewed row39 baseline.'),'attacks':attacks})
    check('no_new_duplicate_id_multiplicity',duplicates==oldduplicates,
          {'baseline_revision':migration['captured_head'],'baseline_duplicates':oldduplicates,'current_duplicates':duplicates,
           'preexisting_registry_debt':debt,'global_uniqueness_claimed':False})

    graph={};import_records=[]
    for path in view.lean_paths():
        edges=imports(view.read(path).decode())
        graph[module_name(path)]=[name for name,_ in edges]
        import_records.extend({'path':path,'line':line,'module':name} for name,line in edges)
    stale=[r for r in import_records if r['module'] in deleted_modules]
    check('no_imports_of_deleted_modules',not stale,{'scanned_lean_files':len(graph),'roots':list(SCAN_ROOTS),
          'deleted_modules':sorted(deleted_modules),'references':stale})
    start='Effect4.Store.Domain.Shape';seen=set();stack=[start];unresolved=[]
    while stack:
        name=stack.pop()
        if name in seen: continue
        seen.add(name)
        if name.startswith('Effect4') and name not in graph: unresolved.append(name)
        stack.extend(graph.get(name,[]))
    schema=sorted(name for name in seen if name=='Effect4.Schema' or name.startswith('Effect4.Schema.'))
    check('pure_shape_schema_free_closure',start in graph and not schema and not unresolved,
          {'root':start,'schema_modules':schema,'unresolved_effect4_modules':sorted(unresolved),'closure':sorted(seen)})
    report['ok']=not report['failures']
    return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,default=Path('/Users/pooks/Dev/lean4-effect4-slice6'))
    p.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parent.parent)
    args=p.parse_args()
    try:
        result=validate(args.repo.resolve(),args.bundle.resolve())
    except Exception as error:
        result={'kind':'row39_read_only_static_validation','ok':False,'failures':['validator_error'],
                'error_type':type(error).__name__,'error':str(error)}
    print(json.dumps(result,indent=2,ensure_ascii=False))
    return 0 if result['ok'] else 1


if __name__=='__main__': sys.exit(main())
