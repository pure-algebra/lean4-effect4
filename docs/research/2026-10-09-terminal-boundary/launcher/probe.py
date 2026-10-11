#!/usr/bin/env python3
"""Isolated launcher dispatch control; fake lake only copies prerecorded text."""
import hashlib, json, os, shlex, subprocess, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
original = (HERE / 'launcher-original.sh').read_bytes()
old = b'"$here/build.sh"\ncase $mode in\n  text) cat "$out/frames.txt" ;;\n  png) for f in "$out"/*.draw; do "$here/draw" "$f" --png "${f%.draw}.png"; done; echo "$out" ;;\n  window) exec "$here/play" "$out" ;;'
new = b'case $mode in\n  text) cat "$out/frames.txt" ;;\n  png) "$here/build.sh"; for f in "$out"/*.draw; do "$here/draw" "$f" --png "${f%.draw}.png"; done; echo "$out" ;;\n  window) "$here/build.sh"; exec "$here/play" "$out" ;;'
assert original.count(old) == 1, 'Refuse an unexpected launcher shape'
candidate = original.replace(old, new)
(HERE / 'launcher-candidate.sh').write_bytes(candidate)
frame = 'fixture title\nfixture body\n'
(HERE / 'prerecorded-frames.txt').write_text(frame)
rows = []
with tempfile.TemporaryDirectory(prefix='effect4-terminal-launcher-') as temporary:
    base = Path(temporary)
    fakebin = base / 'bin'
    fakebin.mkdir()
    # No Lean process runs: this shell stub copies the prerecorded fixture.
    (fakebin / 'lake').write_text('#!/bin/sh\nset -eu\nprintf "fake-lake %s\\n" "$*" >> "$FIXTURE_LOG"\nfor out do :; done\nmkdir -p "$out"\ncp "$FIXTURE_FRAMES" "$out/frames.txt"\n')
    (fakebin / 'lake').chmod(0o755)
    for label, body in [('original', original), ('candidate', candidate)]:
        tree = base / label
        view = tree / 'tools/view'
        view.mkdir(parents=True)
        (view / 'v').write_bytes(body)
        (view / 'build.sh').write_text('#!/bin/sh\nprintf "BUILD_STUB_CALLED\\n" >> "$FIXTURE_LOG"\nprintf "DISTINCTIVE_GRAPHICAL_BUILD_FAILURE\\n" >&2\nexit 73\n')
        (view / 'play').write_text('#!/bin/sh\nprintf "UNEXPECTED_PLAY\\n" >> "$FIXTURE_LOG"\nexit 99\n')
        for p in [view / 'v', view / 'build.sh', view / 'play']:
            p.chmod(0o755)
        for mode in ['text', 'window', 'png']:
            args = {'text':['-t','fixture'], 'window':['fixture'], 'png':['-p','fixture']}[mode]
            log = base / f'{label}-{mode}.log'
            env = os.environ.copy()
            env.update(PATH=str(fakebin) + os.pathsep + env.get('PATH',''), FIXTURE_LOG=str(log), FIXTURE_FRAMES=str(HERE / 'prerecorded-frames.txt'))
            command = ['/bin/sh', str(view / 'v'), *args]
            result = subprocess.run(command, cwd=tree, env=env, text=True, capture_output=True)
            calls = log.read_text().splitlines() if log.exists() else []
            wanted = 0 if label == 'candidate' and mode == 'text' else 73
            assert result.returncode == wanted, (label, mode, result.returncode)
            assert result.stdout == (frame if wanted == 0 else ''), (label, mode, result.stdout)
            assert ('BUILD_STUB_CALLED' in calls) == (wanted == 73)
            assert 'UNEXPECTED_PLAY' not in calls
            rows.append(dict(variant=label, mode=mode, command=command, commandShell=shlex.join(command), exit=result.returncode, stdout=result.stdout, stderr=result.stderr, calls=calls, passControl=True))
record = dict(format='effect4-terminal-launcher-fixture-v1', sourcePin=(HERE / 'source-pin.txt').read_text().splitlines()[0], originalSha256=hashlib.sha256(original).hexdigest(), candidateSha256=hashlib.sha256(candidate).hexdigest(), invocation=['python3',str(HERE / 'probe.py')], limits=['Fixture evidence only; no real Lake, graphical dependency build, window, terminal emulator, or terminal conformance run.', 'Candidate changes only the final normal-mode build dispatch; looks mode is unchanged.'], rows=rows)
(HERE / 'evidence.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'controls':len(rows),'allPassed':True,'originalSha256':record['originalSha256'],'sourcePin':record['sourcePin']}))
