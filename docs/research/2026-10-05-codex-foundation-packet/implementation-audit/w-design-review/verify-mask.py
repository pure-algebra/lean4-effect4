import hashlib
import json
import pathlib
import subprocess

repo = pathlib.Path('/Users/pooks/Dev/lean4-effect4')
out = pathlib.Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-implementation-audit/w-design-review')
commit = '27ea7cb246191ccdec20ca4819446b2546084118'
release = pathlib.Path('/Users/pooks/.bun/install/cache/effect@4.0.1@@@1')
paths = [
    'docs/core/decisions.md',
    'docs/research/2026-10-05-claude-lead/waiting-design.md',
    'src/Effect4/Codegen/Forms.lean',
    'src/Effect4/Codegen/Templates.lean',
    'src/Effect4/Codegen/Print.lean',
    'src/Effect4/Codegen/Read.lean',
    'src/Effect4/Machine/Frames.lean',
    'src/Effect4/Program/Compile.lean',
    'src/Effect4/Program/Decision.lean',
    'tools/Effect4Gen/binders.json',
    'src/Effect4/Laws/Codegen/ReadPrint.lean',
    'src/Effect4/Laws/Codegen/Read.lean',
    'vendor/effect-4.0.0-rc.112/src/internal/effect.ts',
]
def git(*args):
    return subprocess.check_output(['git', '-C', str(repo), *args])
def digest(data):
    return hashlib.sha256(data).hexdigest()

sources = {p: git('show', f'{commit}:{p}') for p in paths}
text = {p: data.decode() for p, data in sources.items()}
forms = text['src/Effect4/Codegen/Forms.lean']
templates = text['src/Effect4/Codegen/Templates.lean']
draft = (repo / paths[1]).read_bytes()
rc = text['vendor/effect-4.0.0-rc.112/src/internal/effect.ts']
v401 = (release / 'src/internal/effect.ts').read_text()
def mask_body(code):
    tail = code.split('export const uninterruptibleMask =', 1)[1]
    return tail.split('/** @internal */', 1)[0].strip()

checks = {
    'row227_requires_escape_refusal': 'The first profile refuses a reference that escapes its mask' in text[paths[0]],
    'live_draft_requests_explicit_amendment': "This amends a ruled row, so it needs the owner's word" in draft.decode(),
    'form_expander_not_mask_ready': 'def Template.expand' in forms and 'getInterruptible' not in forms and 'uninterruptibleMask' not in forms,
    'print_uses_constructor_fold': 'Templates.printT sig n e' in text['src/Effect4/Codegen/Print.lean'],
    'row_selects_by_constructor': 'row.ctor == ctor' in templates,
    'boolean_choice_adds_no_binder': '| .bool => (0, 0)' in text['src/Effect4/Program/Decision.lean'],
    'read_print_returns_same_eff': 'readEff classes sig spell n x = .ok e' in text['src/Effect4/Laws/Codegen/ReadPrint.lean'],
    'read_exact_returns_same_syntax': 'print sig n e = .ok x' in text['src/Effect4/Laws/Codegen/Read.lean'],
    'masks_same_source_function': mask_body(rc) == mask_body(v401),
    'v401_manifest': json.loads((release / 'package.json').read_text())['version'] == '4.0.1',
}
assert all(checks.values()), checks
receipt = {
    'reviewed_commit': commit,
    'head_at_verification': git('rev-parse', 'HEAD').decode().strip(),
    'working_tree_status': git('status', '--short').decode(),
    'pinned_source_sha256': {p: digest(data) for p, data in sources.items()},
    'live_draft_sha256': digest(draft),
    'release_source_path': str(release / 'src/internal/effect.ts'),
    'release_source_sha256': digest((release / 'src/internal/effect.ts').read_bytes()),
    'checks': checks,
    'report_sha256': digest((out / 'mask-review.md').read_bytes()),
    'limits': 'Source assertions only; no Lean build, generator, install, runtime probe, or active-repository write.',
    'command': 'python3 /private/tmp/codex-effect4-overnight-monitor/2026-10-05-implementation-audit/w-design-review/verify-mask.py',
    'exit': 0,
}
(out / 'mask-verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'checks_passed': len(checks), 'pinned_files': len(sources), 'mask_source_identical': checks['masks_same_source_function'], 'head_at_verification': receipt['head_at_verification']}))
