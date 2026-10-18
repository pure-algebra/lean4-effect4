"""Check only the seams plan amendment and its retained evidence; no production writes."""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote

ROOT = Path('/Users/pooks/Dev/lean4-effect4')
HERE = Path(__file__).resolve().parent
PLAN = HERE.parent
DOCS = [PLAN / name for name in ('README.md', 'cuts.md', 'ledger.md')]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> bytes:
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(ROOT), *args])


def tracked_fingerprint() -> tuple[int, str]:
    digest = hashlib.sha256()
    paths = sorted(path for path in git('ls-files', '-z').split(b'\0') if path)
    for raw in paths:
        path = ROOT / os.fsdecode(raw)
        if path.is_symlink():
            data = os.readlink(path).encode()
        elif path.is_file():
            data = path.read_bytes()
        else:
            data = b'<absent>'
        digest.update(raw + b'\0' + hashlib.sha256(data).digest())
    return len(paths), digest.hexdigest()


checks: dict[str, bool] = {}
details: dict[str, object] = {}
original = json.loads((HERE / 'baseline.json').read_text())
before = json.loads((HERE / 'amendment-baseline.json').read_text())
review = (PLAN / 'codex-review.md').read_text()
ledger = (PLAN / 'ledger.md').read_text()
readme = (PLAN / 'README.md').read_text()
cuts = (PLAN / 'cuts.md').read_text()

findings = re.findall(r'^\| (SM-C-\d+) \|', review, re.M)
dispositions = re.findall(r'^\| (SM-C-\d+) \|', ledger, re.M)
checks['all_findings_disposed_once'] = (
    len(findings) == len(set(findings)) == len(dispositions) == len(set(dispositions))
    and set(findings) == set(dispositions)
)
checks['all_dispositions_have_owner_and_acceptance'] = all(
    len(parts := line.strip('|').split('|')) == 5 and all(part.strip() for part in parts)
    for line in ledger.splitlines() if re.match(r'^\| SM-C-\d+ \|', line)
)
original_cut_rows = [line for line in (PLAN / 'cuts-v1.md').read_text().splitlines()
                     if re.match(r'^\| (Lean core|Lean laws|tools|OCaml engine|OCaml store|docs) \|', line)]
cut_ids = re.findall(r'^\| (K-\d+) \|', cuts, re.M)
checks['all_original_cuts_have_amended_rows'] = (
    len(original_cut_rows) == len(cut_ids)
    and cut_ids == [f'K-{number:02d}' for number in range(1, len(original_cut_rows) + 1)]
)
details['finding_ids'] = dispositions
details['cut_ids'] = cut_ids

missing_links = []
missing_paths = []
for doc in DOCS:
    text = doc.read_text()
    for target in re.findall(r'\]\(([^\s)]+)\)', text):
        if re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:', target) or target.startswith('#'):
            continue
        raw = unquote(target.split('#', 1)[0]).strip('<>')
        candidate = Path(raw) if raw.startswith('/') else doc.parent / raw
        if not candidate.exists():
            missing_links.append({'document': str(doc.relative_to(ROOT)), 'target': target})
    for target in re.findall(r'`((?:src|tools|scripts|Test|rocq|ocaml|review-probes)/[^`\s]+\.(?:lean|ml|mli|json|md|py|log))`', text):
        candidate = doc.parent / target if target.startswith('review-probes/') else ROOT / target
        if not candidate.exists() and candidate != HERE / 'amendment-checks.json':
            missing_paths.append({'document': str(doc.relative_to(ROOT)), 'path': target})
checks['local_links_exist'] = not missing_links
checks['cited_source_paths_exist'] = not missing_paths
details['missing_links'] = missing_links
details['missing_paths'] = missing_paths

phase_block = readme.split('## 9. Phases, slices, and acceptance', 1)[1].split('```mermaid', 1)[1].split('```', 1)[0]
node = r'([A-Za-z][A-Za-z0-9]*)(?:\["[^"\n]*"\])?'
edges = re.findall(node + r'\s*-->\s*' + node, phase_block)
graph: dict[str, set[str]] = {}
for source, target in edges:
    graph.setdefault(source, set()).add(target)
    graph.setdefault(target, set())


def reaches(source: str, target: str, seen: set[str] | None = None) -> bool:
    seen = set() if seen is None else seen
    if source in seen:
        return False
    seen.add(source)
    return target in graph.get(source, set()) or any(
        reaches(child, target, seen) for child in graph.get(source, set())
    )


checks['slice_graph_acyclic'] = not any(reaches(item, item) for item in graph)
required = [('S0', 'V1'), ('V1', 'S3a'), ('S1', 'S3a'), ('S2', 'S3a'), ('S4', 'S3a'),
            ('ST1a', 'ST1b'), ('ST1b', 'ST2'), ('ST1b', 'ST3'), ('V1', 'ST3'),
            ('ST2', 'ST4'), ('ST3', 'ST4'), ('S3b', 'ST4'), ('ST2', 'S6'), ('ST4', 'S6')]
checks['required_slice_dependencies_present'] = all(reaches(a, b) for a, b in required)
checks['cleanup_does_not_block_checker'] = not reaches('K', 'V1')
details['slice_edges'] = edges

snapshot_pairs = [('README-v1.md', 'README.md'), ('cuts-v1.md', 'cuts.md')]
checks['reviewed_drafts_retained_exactly'] = all(
    sha(PLAN / snapshot) == original['inputs'][str(PLAN / old)]
    for snapshot, old in snapshot_pairs
)
allowed_changed = {str((PLAN / name).relative_to(ROOT)) for name in ('README.md', 'cuts.md')}
changed_old = []
for relative, expected in before['seams_files'].items():
    if relative in allowed_changed:
        continue
    path = ROOT / relative
    if not path.exists() or sha(path) != expected:
        changed_old.append(relative)
checks['existing_review_designs_and_probes_unchanged'] = not changed_old
details['unexpected_changes_to_retained_files'] = changed_old

other_inputs = {path: digest for path, digest in original['inputs'].items()
                if str(Path(path).relative_to(ROOT)) not in allowed_changed}
changed_inputs = [path for path, digest in other_inputs.items()
                  if not Path(path).exists() or sha(Path(path)) != digest]
checks['earlier_plans_and_briefs_unchanged'] = not changed_inputs
details['unexpected_input_changes'] = changed_inputs

allowed_new = {
    'docs/research/2026-10-17-seams/ledger.md',
    'docs/research/2026-10-17-seams/review-probes/amendment-baseline.json',
    'docs/research/2026-10-17-seams/review-probes/check_amendment.py',
    'docs/research/2026-10-17-seams/review-probes/amendment-language.log',
    'docs/research/2026-10-17-seams/review-probes/amendment-checks.json',
    'docs/research/2026-10-17-seams/review-probes/amendment-probe.json',
    'docs/research/2026-10-17-seams/review-probes/concurrent-inputs.json',
    'docs/research/2026-10-17-seams/review-probes/TranscriptCarrierControl.lean',
    'docs/research/2026-10-17-seams/review-probes/TranscriptCarrierControl.log',
}
new_paths = {str(path.relative_to(ROOT)) for path in PLAN.rglob('*') if path.is_file()} - set(before['seams_files'])
# Other authors can create research files concurrently. Record those additions,
# rather than claiming this tool observes every author's writes.
concurrent_new = new_paths - allowed_new
details['amendment_files_since_baseline'] = sorted(new_paths & allowed_new)
details['concurrent_files_not_owned_by_amendment'] = sorted(concurrent_new)
details['new_file_scope_note'] = 'Named amendment outputs are tracked separately; other additions are observed, not attributed or edited.'
concurrent = json.loads((HERE / 'concurrent-inputs.json').read_text())
details['concurrent_inputs'] = {
    relative: {'read_sha256': info['sha256'], 'current_sha256': sha(ROOT / relative),
               'matches_read_version': sha(ROOT / relative) == info['sha256']}
    for relative, info in concurrent['files'].items()
}
probe = json.loads((HERE / 'amendment-probe.json').read_text())
checks['new_representation_probe_passed'] = (
    probe['exit'] == 0 and sha(HERE / 'TranscriptCarrierControl.lean') == probe['source_sha256']
    and sha(HERE / 'TranscriptCarrierControl.log') == probe['log_sha256']
)
checks['language_check_passed'] = (HERE / 'amendment-language.log').read_text().startswith('PASS check-language:')

probe_records = json.loads((HERE / 'results.json').read_text())
checks['retained_lean_evidence_matches_success_records'] = all(
    row['exit'] == 0
    and sha(HERE / (row['probe'] + '.lean')) == row['source_sha256']
    and sha(Path(row['log'])) == row['log_sha256']
    for row in probe_records
)
checks['host_test_log_unchanged'] = sha(HERE / 'host-probes.log') == before['seams_files'][str((HERE / 'host-probes.log').relative_to(ROOT))]

count, fingerprint = tracked_fingerprint()
state = {
    'head': git('rev-parse', 'HEAD').decode().strip(),
    'branch': git('branch', '--show-current').decode().strip(),
    'status': git('status', '--short', '--untracked-files=all').decode(),
    'tracked_paths': count,
    'tracked_bytes_sha256': fingerprint,
    'diff_sha256': hashlib.sha256(git('diff', 'HEAD', '--binary')).hexdigest(),
}
for key, value in state.items():
    checks['unchanged_' + key] = value == original[key]

result = {
    'checked_utc': datetime.now(timezone.utc).isoformat(),
    'command': ['python3', str(Path(__file__).relative_to(ROOT))],
    'checks': checks,
    'all_passed': all(checks.values()),
    'documents': {str(doc.relative_to(ROOT)): sha(doc) for doc in DOCS},
    'state': state,
    'details': details,
    'scope': 'Document structure and retained evidence integrity. No implementation or new theorem is tested.',
}
(HERE / 'amendment-checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'all_passed': result['all_passed'], 'checks': checks,
                  'findings': len(findings), 'cut_rows': len(cut_ids)}, indent=2))
if not result['all_passed']:
    print(json.dumps(details, indent=2))
raise SystemExit(0 if result['all_passed'] else 1)
