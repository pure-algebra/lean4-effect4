import hashlib
import json
import pathlib
import subprocess

repo = pathlib.Path('/Users/pooks/Dev/lean4-effect4')
original = pathlib.Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review')
out = pathlib.Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-implementation-audit')
commit = '5ebacecc8631b9897652a86f67b7f1d3097dcffc'

def git(*args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True)

expected = {
    'contracts-and-literature.md': '2c4aa82918ff4ed8b4d0413fd17813dc06fa42ae34adf5400dce368e4a15d89f',
    'foundation-audit.md': '01f1e527f380842d543ed8110eadbfcbf9adedaf06189c0ddaa37a8d11723c93',
}
checks = {}
for name, digest in expected.items():
    scratch = (original / name).read_bytes()
    tracked_path = f'docs/research/2026-10-05-codex-foundation-packet/{name}'
    pinned = subprocess.check_output(['git', '-C', str(repo), 'show', f'{commit}:{tracked_path}'])
    assert scratch == pinned, name
    assert hashlib.sha256(scratch).hexdigest() == digest, name
    checks[name] = {'byte_identical': True, 'sha256': digest}

decisions = git('show', f'{commit}:docs/core/decisions.md')
registry = git('show', f'{commit}:tools/Tools/SemanticsRegistry.lean')
note = git('show', f'{commit}:docs/research/2026-10-05-claude-lead/foundation-contracts.md')
assertions = {
    'row222_winning_premise': 'When cancellation wins before consumption' in decisions,
    'registry_drops_winning_premise': 'a cancellation before consumption withdraws the request and consumes nothing' in registry,
    'four_observations_retained': "the commitment, the operation's exit, the entry of the caller's continuation, and the fiber's exit" in decisions,
    'target_agreement_stays_open': "row 80's version erasure and target agreement stay open" in decisions,
    'dynamic_access_tracking_retained': 'tracks every dynamic cell access' in decisions,
    'no_pretended_goals': 'No obligation here is a planned goal yet' in note,
    'queue_packet_still_owed': "The Queue's whole transition contract, as a packet in `Test/contracts/`, is still owed" in decisions,
    'clock_schedule_superseded': "The clock slice waits for T3b's merge" in decisions,
}
assert all(assertions.values()), assertions
receipt = {
    'reviewed_commit': commit,
    'head_at_verification': git('rev-parse', 'HEAD').strip(),
    'working_tree_status': git('status', '--short'),
    'accepted_packet_checks': checks,
    'assertions': assertions,
    'report_sha256': hashlib.sha256((out / 'rulings-review.md').read_bytes()).hexdigest(),
    'limits': 'Read-only source review; no builds, generators, runtime probes or active-repository writes.',
}
(out / 'rulings-verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({'assertions_passed': len(assertions), 'packet_pairs_identical': len(checks), 'reviewed_commit': commit, 'head_at_verification': receipt['head_at_verification'], 'working_tree_clean': receipt['working_tree_status'] == ''}))
