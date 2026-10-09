from pathlib import Path
import collections, hashlib, json, re, subprocess
ROOT = Path('/Users/pooks/Dev/lean4-effect4')
BASE = '7b73d59cb2ae5b290c87c7f0ba9a6aa77a71fa04'
HEAD = '7334f1197cf5b535541ce1dfc7789a5082c07115'
OUT = Path(__file__).parent

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
def source(rev, path):
    return git('show', f'{rev}:{path}')

a = source(BASE, 'generated/semantics.md')
b = source(HEAD, 'generated/semantics.md')
preplan = lambda s: re.sub(r'Tagged:.*?\n', '', s.split('## Plan\n')[0])
statuses = lambda s: set(re.findall(r'^\| (`[^`]+`) \| (proved|modulo|goal) \| ([^|]+) \|', s, re.M))
edges = lambda s: collections.Counter(re.findall(r'^  (\w+) --> (\w+)$', s, re.M))
labels = dict(re.findall(r'^  (\w+)\["([^<"]+)<br/>', b, re.M))
removed_edges = edges(a) - edges(b)
added_edges = edges(b) - edges(a)
paths = git('diff', '--name-only', BASE, HEAD).splitlines()
diff = git('diff', '--unified=0', BASE, HEAD, '--', 'src/Effect4/Laws')
metadata_lines = [line for line in diff.splitlines() if line[:1] in ('+', '-') and not line.startswith(('+++', '---')) and re.search(r'@\[|\battribute\b|\bproof_goal\b', line)]
removed = json.loads((OUT / 'removed-theorem-headers.json').read_text())
names = sorted({row[1] for row in removed})
pattern = r'\b(' + '|'.join(map(re.escape, names)) + r')\b'
pin_result = subprocess.run(['rg', '-n', pattern, 'Test/contracts', 'Test/Counterexamples', 'docs/core', 'tools/ProofGraph', 'src/Effect4/Laws/Auto'], cwd=ROOT, text=True, capture_output=True)
assert pin_result.returncode in (0, 1), pin_result.stderr
assert not pin_result.stdout, pin_result.stdout
assert source(BASE, 'tools/ProofGraph/Registry.lean') == source(HEAD, 'tools/ProofGraph/Registry.lean')
assert preplan(a) == preplan(b)
assert statuses(a) == statuses(b)
assert not removed_edges
assert not metadata_lines
assert git('diff', '--name-only', BASE, HEAD, '--', 'src/Effect4/Laws/Auto') == ''
result = {
    'base': BASE, 'head': HEAD, 'current_head': git('rev-parse', 'HEAD').strip(),
    'current_status': git('status', '--short'),
    'registry_identical': True, 'preplan_identical_except_population': True,
    'unique_status_and_rest_sets_identical': True,
    'removed_graph_edges': [],
    'added_graph_edges': [[labels.get(x,x), labels.get(y,y), n] for (x,y),n in added_edges.items()],
    'metadata_diff_lines': metadata_lines, 'auto_bank_sources_unchanged': True,
    'frozen_contract_counterexample_authority_registry_auto_pin_hits': [],
    'removed_theorem_headers': len(removed),
    'generated_semantics_sha256': hashlib.sha256(b.encode()).hexdigest(),
    'registry_sha256': hashlib.sha256(source(HEAD, 'tools/ProofGraph/Registry.lean').encode()).hexdigest(),
    'limit': 'Static exact-source review. No primary builds. Parent independently compiles four consumers.'
}
(OUT / 'graph-metadata-reference-audit.json').write_text(json.dumps(result, indent=2)+'\n')
(OUT / 'laws.diff').write_text(git('diff', BASE, HEAD, '--', 'src/Effect4/Laws'))
(OUT / 'generated-semantics.diff').write_text(git('diff', BASE, HEAD, '--', 'generated/semantics.md'))
print(json.dumps(result, indent=2))
