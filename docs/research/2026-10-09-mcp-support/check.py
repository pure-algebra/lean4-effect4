"""Validate the retained finite evidence and record its source boundary."""
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess

FOLDER = Path(__file__).resolve().parent
REPO = FOLDER.parents[2]
DESIGN = 'c4b6b795638399fcbd6026630c05afb8bd75b268'
REVIEWED = '28ed6727e1979b544a4d9c619cc837509511c0b6'

SESSION_NAMES = '''same-sketch-same-context-same-view
warm-undo-has-history
cold-undo-has-no-history
same-sketch-journals-differ
both-application-signatures-admitted
same-program-different-signature-answer
invalid-address-is-unchanged
raw-fold-continues-after-invalid-address
raw-fold-keeps-prior-change-before-invalid-address
empty-word-keeps-program
split-word-agrees-for-program
disjoint-edits-each-admitted-at-base
disjoint-edits-combined-refused
disjoint-edits-syntax-commutes
type-preserving-disjoint-edits-combine
opposite-omissions-both-admitted
opposite-omissions-append-opposite-orders
opposite-omissions-have-different-programs
duplicate-labels-remain-two-distinct-rows
duplicate-labels-program-uses-each-row-once'''.splitlines()
SCHEMA_NAMES = '''known-reference-schema
known-reference-reader
unknown-reference-schema
unknown-reference-reader
distinct-cases-tags-valid
distinct-cases-value-fits
distinct-cases-print-validates
distinct-cases-read-restores-value
duplicate-case-names-tags-valid
duplicate-case-names-value-fits
duplicate-case-names-print-validates
duplicate-case-names-read-restores-value
ascending-row-schema
ascending-row-carrier-reader
descending-row-schema
descending-row-shape-reader
descending-row-carrier-reader
single-named-binding-schema
single-named-binding-reader
named-alias-schema
named-alias-reader'''.splitlines()


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)


def read_json(name):
    return json.loads((FOLDER / name).read_text())


def check_lean_rows(name, names):
    rows = read_json(name)
    require([row['name'] for row in rows] == names, name + ': missing, duplicate or reordered controls')
    for row in rows:
        require(row['pass'] is True and row['actual'] == row['expected'], name + ': ' + row['name'])
    return len(rows)


session_count = check_lean_rows('session-output.json', SESSION_NAMES)
schema_count = check_lean_rows('schema-output.json', SCHEMA_NAMES)
number = read_json('number-output.json')
expected_numbers = [
    ('9007199254740991', '9007199254740991', True, True, True),
    ('9007199254740992', '9007199254740992', True, True, False),
    ('9007199254740993', '9007199254740992', False, True, False),
    ('9007199254740994', '9007199254740994', True, False, False),
]
require(len(number['rows']) == len(expected_numbers), 'number controls: wrong count')
for row, expected in zip(number['rows'], expected_numbers):
    actual = tuple(row[key] for key in ('token', 'decoded', 'exact', 'noteAdmits', 'safeAdmits'))
    require(row['pass'] is True and actual == expected, 'number control: ' + row['token'])
require(number['node'].startswith('v'), 'missing Node version')

manifest = read_json('schema-source.json')
require(manifest['designCommit'] == DESIGN and manifest['reviewedCommit'] == REVIEWED,
        'schema manifest commits changed')
source = (REPO / manifest['source']).read_bytes()
require(source == git('show', REVIEWED + ':' + manifest['source']), 'schema probe changed since review')
require(sha256(source).hexdigest() == manifest['sourceSha256'], 'schema source hash changed')
marker = b'\nend ProbeMcp\n'
require(source.count(marker) == 1, 'schema declaration boundary is ambiguous')
prefix = source.split(marker, 1)[0] + marker
require(sha256(prefix).hexdigest() == manifest['copiedDeclarationsSha256'], 'copied declarations changed')
expected_generated = (b'import Effect4.Store.Domain.RowCanonical\n' + prefix +
                      (FOLDER / 'schema-controls-tail.lean').read_bytes())
generated = (FOLDER / 'SchemaControls.lean').read_bytes()
require(generated == expected_generated, 'schema control generation drift')
require(sha256(generated).hexdigest() == manifest['generatedSha256'], 'generated control hash changed')
require(not git('diff', '--name-only', REVIEWED, '--', '.', ':!docs/research').strip(),
        'non-research tracked files differ from reviewed commit')

files = ['SessionControls.lean', 'session-output.json', 'SchemaControls.lean',
         'schema-controls-tail.lean', 'schema-output.json', 'prepare-schema.py',
         'schema-source.json', 'number-controls.mjs', 'number-output.json', 'check.py']
checkpoint = {
    'checkedAtUtc': datetime.now(timezone.utc).isoformat(),
    'designCommit': DESIGN,
    'reviewedCommit': REVIEWED,
    'evidence': 'finite Lean and JavaScript controls; no new theorem or production repair',
    'counts': {'session': session_count, 'schema': schema_count, 'javascript': len(number['rows'])},
    'allExpectedObservationsMatched': True,
    'nodeVersion': number['node'],
    'trackedProductionChangesSinceReviewedCommit': [],
    'openDesignCorrections': {
        'MCR-1': 'Separate structural schema validity from carrier codec admission.',
        'MCR-2': 'Include application context in snapshot identity; retain history separately.',
        'MCR-3': 'Specify checked script refusal and root publication above the raw edit fold.',
        'MCR-4': 'Separate syntactic commutation from checked replay; specify hole permutations.',
        'MCR-5': 'Use the correct declaration law, dependency projection and runtime data provider.'
    },
    'proposedObligations': ['O' + str(i) for i in range(1, 10)] +
                           ['author-transport-agrees', 'author-publish-base'],
    'limitations': [
        'The custom schema validator is not an independent external JSON Schema client.',
        'No TypeScript compiler, MCP server, HTTP adapter or full axiom sweep runs.',
        'Existing laws retain their premises; this receipt changes no registry status.'
    ],
    'sha256': {name: sha256((FOLDER / name).read_bytes()).hexdigest() for name in files},
}
(FOLDER / 'checkpoint.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
print(f'PASS: {session_count} session, {schema_count} schema, {len(number["rows"])} JavaScript controls; '
      'source and generation hashes match; production source unchanged.')
