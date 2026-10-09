#!/usr/bin/env python3
"""Retain compiler output and source pins for the isolated edit-session review."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PIN = 'fdbae937259f2516645147a045a2d7ce9beaee5e'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def function(text, name):
    start = re.search(r'LEAN_EXPORT lean_object\* ' + re.escape(name) + r'\([^\n]*\)\{', text)
    if start is None:
        raise RuntimeError(f'Missing compiled function: {name}')
    end = text.find('\nLEAN_EXPORT ', start.end())
    if end < 0:
        raise RuntimeError('Cannot delimit compiled function')
    return text[start.start():end] + '\n'


source = ROOT / '.lake/build/ir/Effect4/Program/Edit.c'
original = source.read_text()
candidate = (HERE / 'Probe.c').read_text()
old = function(original, 'lp_effect4_Effect4_Program_EditSession_feed___redArg')
new = function(candidate, 'l_EditOverwatch_feedDeferred___redArg')
annotation = 'lp_effect4_Effect4_Program_annotate___redArg('
lookup = 'lp_effect4_Effect4_Program_Table_typedAt('
subcheck = 'lp_effect4_Effect4_Program_Annotate_check___redArg('
splice = 'lp_effect4_Effect4_Program_Table_splice('
assert old.count(annotation) == new.count(annotation) == 1
assert old.index(annotation) < old.index(lookup) < old.index(subcheck) < old.index(splice)
assert new.index(lookup) < new.index(subcheck) < new.index(splice) < new.index(annotation)
labels = list(re.finditer(r'^(v_\w+):$', new[:new.index(annotation)], re.MULTILINE))
assert labels
fallback = labels[-1].group(1)
assert new.count('goto ' + fallback + ';') == 4
assert 'return ' in new[new.index(splice):labels[-1].start()]
assert 'lean_dec_ref(v_rechecked_' in old[old.index(subcheck):old.index(splice)]
(HERE / 'landed-feed.c.txt').write_text(old)
(HERE / 'candidate-feed.c.txt').write_text(new)

paths = [
    'src/Effect4/Program/Edit.lean', 'src/Effect4/Laws/Program/Edit.lean',
    'src/Effect4/Program/Typing/Splice.lean', 'src/Effect4/Laws/Program/Typing/Splice.lean',
    'src/Effect4/Author.lean', 'src/Effect4/Laws/Author.lean',
    'tools/ProofGraph/Registry.lean', 'Test/Program/EditControls.lean',
    'docs/core/decisions.md', 'docs/research/2026-10-08-seat-ORG-theory-map.md',
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
hashes = {}
for path in paths:
    actual = (ROOT / path).read_bytes()
    pinned = subprocess.check_output(['git', 'show', f'{PIN}:{path}'], cwd=ROOT)
    assert actual == pinned, f'Review source differs from pin: {path}'
    hashes[path] = digest(actual)

report = {
    'format': 'effect4-edit-session-overwatch-v1',
    'reviewedCommit': PIN,
    'featureCommit': 'ff87466d42813a02e5f89c2c9a653b15ebd1669c',
    'sourceHashes': hashes,
    'compiler': subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip(),
    'compiledOriginalSha256': digest(source.read_bytes()),
    'compiledCandidateSha256': digest((HERE / 'Probe.c').read_bytes()),
    'finiteGuardCount': (HERE / 'Probe.lean').read_text().count('\n#guard '),
    'compiledInspection': {
        'original': 'whole annotation before either table lookup, then subtree check; successful splice discards the full annotation result',
        'candidate': 'subtree check first; whole annotation only at the four fallback branches; successful splice returns before that block',
        'candidateFallbackLabel': fallback},
    'scope': 'Kernel equality and finite Lean controls; generated C inspection, not a latency benchmark or host/compiler theorem'}
(HERE / 'evidence.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'PASS: {len(paths)} source pins; {report["finiteGuardCount"]} finite guards; original eagerly annotates, candidate defers annotation to four fallback branches')
