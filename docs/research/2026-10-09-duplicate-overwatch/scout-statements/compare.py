"""Read-only replay of the completed 06:47 source review. Outputs go beside this script."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path('/Users/pooks/Dev/lean4-effect4')
BASE = '7b73d59cb2ae5b290c87c7f0ba9a6aa77a71fa04'
HEAD = '7334f1197cf5b535541ce1dfc7789a5082c07115'
OUT = Path(__file__).resolve().parent

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

def headers(source):
    result = {}
    for match in re.finditer(r'(?m)^\s*(?:(?:private|protected)\s+)?theorem\s+([^\s:{(]+)', source):
        tail = source[match.end():]
        result[match.group(1)] = re.sub(r'\s+', ' ', re.split(r':=|\n\s*\|', tail, maxsplit=1)[0]).strip()
    return result

files = git('diff', '--name-only', BASE, HEAD, '--', 'src/Effect4/Laws/Program').splitlines()
rows = []
removed = []
directives = []
for file in files:
    old = git('show', BASE + ':' + file)
    new = git('show', HEAD + ':' + file)
    before, after = headers(old), headers(new)
    matched = []
    changes = []
    for name in sorted(before.keys() & after.keys()):
        entry = {'name': name, 'before': before[name], 'after': after[name]}
        (matched if before[name] == after[name] else changes).append(entry)
    deleted = []
    for name in sorted(before.keys() - after.keys()):
        pattern = r'(?m)^\s*(?:(?:private|protected)\s+)?theorem\s+' + re.escape(name) + r'(?=[\s:{(])'
        match = re.search(pattern, old)
        prefix = old[max(0, match.start() - 160):match.start()]
        entry = {'name': name, 'before': before[name],
                 'nearby_attribute': bool(re.search(r'@\[[^]]*\]\s*$', prefix))}
        deleted.append(entry)
        removed.append({'file': file, **entry})
    diff = git('diff', BASE, HEAD, '--', file)
    for line in diff.splitlines():
        if line[:1] in '+-' and re.match(r'\s*(attribute\b|@\[|import\b)', line[1:]):
            directives.append({'file': file, 'line': line})
    rows.append({'file': file, 'matched_count': len(matched), 'matched_headers': matched,
                 'changed_headers': changes, 'deleted': deleted,
                 'diff_sha256': hashlib.sha256(diff.encode()).hexdigest()})

review_diff = subprocess.check_output(['git', 'diff', BASE, HEAD, '--',
    'src/Effect4/Laws/Program', 'Test/Program/RegistrationYield.lean'], cwd=ROOT)
# Replay the former current-tree rg scans against immutable commit content.
old_only = sorted(set(x['name'] for x in removed) - {'prepareExternalAnswer_sites', 'subN_never', 'mem_zip_self', 'complete_cells_length', 'bool_eq_false_of_not'})
refs = []
for name in old_only:
    command = ['git', 'grep', '-n', '-w', name, HEAD, '--', 'src', 'Test', 'tools', 'scripts', 'generated', 'docs/core']
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    refs.append({'name': name, 'command': command, 'exit_code': result.returncode,
                 'stdout': result.stdout, 'stderr': result.stderr})
qualified_pattern = r'AnswerDecision\.prepareExternalAnswer_sites|Typed\.(subN_never|mem_zip_self|complete_cells_length)|Sched\.bool_eq_false_of_not'
command = ['git', 'grep', '-n', '-E', qualified_pattern, HEAD, '--', 'src', 'Test', 'tools', 'scripts', 'generated', 'docs/core']
result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
refs.append({'name': 'deleted qualified names', 'command': command,
             'exit_code': result.returncode, 'stdout': result.stdout, 'stderr': result.stderr})
report = {
    'evidence_kind': 'source comparison; no Lean build or axiom audit',
    'base': BASE, 'head': HEAD, 'repository': str(ROOT),
    'scope': '21 changed Laws/Program files; Test/Program/RegistrationYield separately inspected',
    'files_reviewed': len(files),
    'surviving_theorem_headers_compared': sum(len(x['matched_headers']) + len(x['changed_headers']) for x in rows),
    'matched_theorem_headers': sum(x['matched_count'] for x in rows),
    'changed_headers': [x for row in rows for x in row['changed_headers']],
    'attribute_or_import_changes': directives,
    'review_diff_sha256': hashlib.sha256(review_diff).hexdigest(),
    'per_file': rows, 'removed_reference_scans': refs,
    'comparison_limit': 'Header text normalized only for whitespace. Semantic review additionally read replacement statements and proof bodies. Shared short names remain valid originals, so reference scans distinguish qualified deleted names.',
}
(OUT / 'comparison.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
(OUT / 'review.diff').write_bytes(review_diff)
summary = {key: value for key, value in report.items() if key not in ('per_file', 'removed_reference_scans')}
summary['per_file_counts'] = [{'file': x['file'], 'matched_count': x['matched_count']} for x in rows]
(OUT / 'summary.json').write_text(json.dumps(summary, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({key: report[key] for key in ('files_reviewed', 'surviving_theorem_headers_compared', 'matched_theorem_headers', 'changed_headers', 'attribute_or_import_changes', 'review_diff_sha256')}, indent=2))
