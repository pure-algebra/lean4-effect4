#!/bin/zsh
# Seat M0, 2026-10-05: the script that wrote the files of out/ (history, not authority).
# Its paths are the seat's own: S is the session's scratch folder, with the release install
# that the seat assembled by links, and W is the seat's worktree. It moves the two check
# markers aside and deletes nothing. $S/check-truth.base.log is the seat's run of the pinned
# lane at the base commit, before any change.
set -u
S=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e4a67264-1213-4b33-b3e2-68332653bd83/scratchpad/m0
W=/Users/pooks/Dev/lean4-effect4-m0
E=$W/docs/research/2026-10-05-seat-M0/out
SLOT=/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh
cd $W
export EFFECT4_EFFECT_NODE_MODULES=/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules
export EFFECT4_RELEASE_NODE_MODULES=$S/release/node_modules
m() { make -o build -o ts/eff/node_modules "$@"; }
mq() { make -o build -o ts/eff/node_modules -o .lake/check/truth "$@"; }
git rev-parse HEAD > $E/head.txt
: > $E/summary.new
[ -e $W/.lake/check/truth ] && mv $W/.lake/check/truth $W/.lake/check/truth.aside
[ -e $W/.lake/check/truth-release ] && mv $W/.lake/check/truth-release $W/.lake/check/truth-release.aside

# 1. the pinned lane, and its artifacts against the base
$SLOT make -o build -o ts/eff/node_modules check-truth > $E/check-truth.log 2>&1; echo "make check-truth: exit status $?" | tee -a $E/summary.new
{ echo "git diff --exit-code f3086de1 -- <the pinned lane's sources and committed artifacts>"
  git diff --exit-code f3086de1 -- harness/truth/corpus.json harness/truth/result.json harness/truth/result.md harness/truth/generated harness/truth/tapes harness/truth/prelude.ts harness/truth/prelude-atoms.gen.ts harness/truth/records.ts harness/truth/tuples.ts harness/truth/run-truth.ts harness/truth/tsconfig.json harness/truth/session harness/truth/Truth.lean scripts/check-truth.py scripts/check-corpus.py ts/eff
  echo "exit status $? (0: no byte differs)"
  echo "git diff --numstat f3086de1 -- scripts/lib/truth_host.py (added, removed):"; git diff --numstat f3086de1 -- scripts/lib/truth_host.py
  echo "git status --short, the seat's evidence folder aside:"; git status --short -- . ':!docs/research'; echo "(end)"; } > $E/pinned-artifacts.txt 2>&1

# The pinned lane's printed lines at the base (the seat's run before any change) against the head's.
sed '$d' $S/check-truth.base.log > $E/check-truth.at-base.log
norm() { sed -E 's/truth-check-[a-z0-9_]+/truth-check-XXXX/; s/\[[0-9.]+ms\]/[N ms]/' "$1"; }
{ echo; echo "The pinned lane's printed lines at the base f3086de1 (check-truth.at-base.log) against the head's (check-truth.log),"
  echo "with the temporary folder's name and the test time replaced:"
  if diff <(norm $E/check-truth.at-base.log) <(norm $E/check-truth.log); then echo "no line differs"; fi; } >> $E/pinned-artifacts.txt

# 2. the release lane
$SLOT make -o build -o ts/eff/node_modules check-truth-release > $E/check-truth-release.log 2>&1; echo "make check-truth-release: exit status $?" | tee -a $E/summary.new
cp .lake/truth-release/run.json $E/run.json
cp .lake/truth-release/release/harness/truth/result.md $E/result.release.md

# 3. the live red controls: change one committed file, run the lane, put the file back
flip() { python3 - "$@" <<'PY'
import sys
from pathlib import Path
name, column, old, new = sys.argv[1:5]
p = Path('harness/truth/build-ledger.tsv'); lines = p.read_bytes().decode('utf-8').split('\n')
header = next(l for l in lines if l.startswith('program\t')).split('\t')
i = next(k for k, l in enumerate(lines) if l.startswith(name + '\t'))
c = lines[i].split('\t'); j = header.index(column); assert c[j] == old, (c[j], old)
c[j] = new; lines[i] = '\t'.join(c); p.write_bytes('\n'.join(lines).encode('utf-8'))
print(f'changed {name} | {column}: "{old}" -> "{new}"')
PY
}
# Each control changes one committed file after a copy of it is kept, and puts the copy back.
keep() { git diff --quiet -- "$1" && cp "$1" $S/kept.copy; }
back() { cp $S/kept.copy "$1" && git diff --quiet -- "$1" && echo "$1 is put back from the kept copy: git diff is empty"; }
# The marker is moved aside first: make 3.81 compares whole seconds, and a file changed in the
# second of the marker's own touch would not rerun the lane (seen once, 2026-10-05).
MARK=/Users/pooks/Dev/lean4-effect4-m0/.lake/check/truth-release
stale() { [ -e $MARK ] && mv $MARK $MARK.aside; true; }
run() { stale; mq check-truth-release 2>&1 | grep "FAIL\|PASS truth-release\|finding(s)\|Error"; echo "make exit status: ${pipestatus[1]}"; }
keep harness/truth/build-ledger.tsv; { echo "RED CONTROL A (the brief's): one entry of the ledger is flipped"; flip p42 "4.0.1 exit" yes "no: x"; run; back harness/truth/build-ledger.tsv; } > $E/red-control-A.flip-one-entry.txt 2>&1
keep harness/truth/build-ledger.tsv; { echo "RED CONTROL B (addendum 1): pProvideMerge keeps its schedule difference; its expected exit is altered"; flip pProvideMerge "4.0.1 exit" yes "no: machine success 2, host success 3"; grep "^pProvideMerge" harness/truth/build-ledger.tsv; run; back harness/truth/build-ledger.tsv; } > $E/red-control-B.exit-beside-schedule.txt 2>&1
keep harness/truth/build-ledger.run.json; { echo "RED CONTROL C: the run record names other modules and another runtime than this host run"; python3 - <<'PY'
from pathlib import Path
p = Path('harness/truth/build-ledger.run.json'); s = p.read_bytes().decode('utf-8')
old = '"sha256": "60a2893025fd06a11a662eac63e733b3fe266e9b0d6c7f0f5019d57b16dbf86e"'
assert s.count(old) == 1 and s.count('"bun": "1.4.2"') == 2
s = s.replace(old, '"sha256": "0000000000000000000000000000000000000000000000000000000000000000"')
i = s.rindex('"bun": "1.4.2"'); s = s[:i] + '"bun": "1.4.1"' + s[i + len('"bun": "1.4.2"'):]
p.write_bytes(s.encode('utf-8'))
print('changed builds.4.0.1.modules.sha256 and builds.4.0.1.runtime.bun in the record')
PY
run; back harness/truth/build-ledger.run.json; } > $E/red-control-C.run-record.txt 2>&1
keep harness/truth/build-ledger.tsv; { echo "RED CONTROL D: a promote over a ledger with a line that cannot be read"; python3 - <<'PY'
from pathlib import Path
p = Path('harness/truth/build-ledger.tsv'); lines = p.read_bytes().decode('utf-8').split('\n')
i = next(k for k, l in enumerate(lines) if l.startswith('pInterruptEscape\t'))
lines[i] = '\t'.join(lines[i].split('\t')[:5])
p.write_bytes('\n'.join(lines).encode('utf-8'))
print('cut the line of pInterruptEscape to five columns')
PY
echo "sha256 of the ledger before the promote: $(shasum -a 256 harness/truth/build-ledger.tsv | cut -c1-16)"
python3 scripts/check-truth-release.py --promote 2>&1 | grep "FAIL\|promoted"; echo "promote exit status: ${pipestatus[1]}"
echo "sha256 of the ledger after the promote:  $(shasum -a 256 harness/truth/build-ledger.tsv | cut -c1-16)"
back harness/truth/build-ledger.tsv; } > $E/red-control-D.promote-guard.txt 2>&1
keep harness/truth/build-ledger.tsv; { echo "GREEN CONTROL E: the ledger with its trailing empty columns trimmed, as an editor may leave it"; python3 - <<'PY'
from pathlib import Path
p = Path('harness/truth/build-ledger.tsv'); s = p.read_bytes().decode('utf-8')
t = '\n'.join(line.rstrip('\t') for line in s.split('\n'))
p.write_bytes(t.encode('utf-8'))
print('trimmed the trailing tabs of', sum(1 for a, b in zip(s.split('\n'), t.split('\n')) if a != b), 'lines')
PY
run; back harness/truth/build-ledger.tsv; } > $E/green-control-E.trimmed-ledger.txt 2>&1
stale; mq check-truth-release 2>&1 | tail -1 > $E/after-red-controls.txt; echo "after the red controls: $(cut -c1-60 $E/after-red-controls.txt)" | tee -a $E/summary.new

# 4. the red controls on real data, the kept controls, the lane with the network denied
python3 scripts/check-truth-release.py > $E/lane.direct.txt 2>&1; echo "the lane, direct: exit status $?" | tee -a $E/summary.new
python3 docs/research/2026-10-05-seat-M0/red-controls.py > $E/red-controls.real-data.txt 2>&1; echo "red-controls.py: exit status $?; $(tail -1 $E/red-controls.real-data.txt)" | tee -a $E/summary.new
python3 scripts/check-truth-release.py --self-test > $E/self-test.txt 2>&1; echo "--self-test: exit status $?; $(tail -1 $E/self-test.txt)" | tee -a $E/summary.new
{ echo "The sandbox denies every network operation: sandbox-exec -p '(version 1)(allow default)(deny network*)'"
  echo "--- its red control: a request to the package index inside the sandbox"
  sandbox-exec -p '(version 1)(allow default)(deny network*)' /usr/bin/curl -sS -m 5 -o /dev/null https://registry.npmjs.org/ 2>&1; echo "curl exit status: $?"
  echo "--- the release lane inside the sandbox, with the pinned lane's host tests"
  sandbox-exec -p '(version 1)(allow default)(deny network*)' python3 scripts/check-truth-release.py --host-tests harness/truth/records.test.ts harness/truth/catch-if.test.ts harness/truth/native-queries.test.ts harness/truth/prelude-inventory.test.ts 2>&1; echo "lane exit status: $?"; } > $E/no-network.txt 2>&1
grep "exit status" $E/no-network.txt | tee -a $E/summary.new

# 4b. six runs in a row, the selection's refusals, and the release result against the audit's
{ for i in 1 2 3 4 5 6; do python3 scripts/check-truth-release.py 2>&1 | tail -1 | cut -c1-58; shasum -a 256 .lake/truth-release/release/harness/truth/result.json | cut -c1-64; done; } > $E/six-runs.txt 2>&1
echo "six runs: $(grep -c '^PASS' $E/six-runs.txt) pass, $(grep -v '^PASS' $E/six-runs.txt | sort -u | wc -l | tr -d ' ') distinct SHA-256 of the release result" | tee -a $E/summary.new
{ echo "--- the variable unset"; env -u EFFECT4_RELEASE_NODE_MODULES python3 scripts/check-truth-release.py 2>&1; echo "exit status: $?"
  echo "--- the variable names the pin's install"; EFFECT4_RELEASE_NODE_MODULES=$EFFECT4_EFFECT_NODE_MODULES python3 scripts/check-truth-release.py 2>&1; echo "exit status: $?"
  echo "--- the variable names an install with effect@4.0.1 and no compiler"; EFFECT4_RELEASE_NODE_MODULES=$S/release-nocompiler/node_modules python3 scripts/check-truth-release.py 2>&1; echo "exit status: $?"; } > $E/selection-refusals.txt 2>&1
echo "selection refusals: $(grep -c '^FAIL truth-release' $E/selection-refusals.txt) of 3" | tee -a $E/summary.new
python3 - > $E/audit-comparison.txt <<'PY'
import json
audit = json.load(open('docs/research/2026-10-05-seat-A401/out/truth-401/result.v401.json'))
mine = json.load(open('.lake/truth-release/release/harness/truth/result.json'))
theirs = {r['program']: r for r in audit['rows']}
same = [r['program'] for r in mine['rows'] if r == theirs[r['program']]]
other = [r['program'] for r in mine['rows'] if r != theirs[r['program']]]
print(f'the audit: effect {audit["effect"]}, bun {audit["bun"]}, {len(theirs)} rows; this lane: effect {mine["effect"]}, bun {mine["bun"]}, {len(mine["rows"])} rows')
print(f'rows of this lane equal to the audit\'s in every field: {len(same)}; different: {len(other)} {other}')
print(f'rows of the audit only: {sorted(set(theirs) - {r["program"] for r in mine["rows"]})}')
PY
cat $E/audit-comparison.txt | tee -a $E/summary.new

# 5. the import scanner against oxc-parser on every source of the work copy
python3 - > $S/oxc/files.txt <<'PY'
import importlib.util
from pathlib import Path
root = Path('.').resolve()
spec = importlib.util.spec_from_file_location('lane', root / 'scripts/check-truth-release.py')
lane = importlib.util.module_from_spec(spec); spec.loader.exec_module(lane)
print('\n'.join(lane.closure(lane.read_repository, [lane.RUNNER] + lane.type_roots() + ['harness/truth/records.test.ts', 'harness/truth/catch-if.test.ts', 'harness/truth/native-queries.test.ts', 'harness/truth/prelude-inventory.test.ts'])))
PY
cp docs/research/2026-10-05-seat-M0/specifiers-against-oxc.ts $S/oxc/specs.ts
(cd $S/oxc && bun --no-install run specs.ts $(sed "s|^|$W/|" $S/oxc/files.txt) > $S/oxc/oxc.json)
python3 - > $E/specifiers-against-oxc.txt <<PY
import importlib.util, json
from pathlib import Path
root = Path('.').resolve()
spec = importlib.util.spec_from_file_location('lane', root / 'scripts/check-truth-release.py')
lane = importlib.util.module_from_spec(spec); spec.loader.exec_module(lane)
oxc = json.load(open('$S/oxc/oxc.json'))
bad = total = 0
for file, specs in oxc.items():
    rel = Path(file).relative_to(root).as_posix()
    mine = lane.specifiers(lane.read_repository(rel))
    total += len(specs)
    if mine != specs:
        bad += 1; print('DIFF', rel, 'scanner:', mine, 'parser:', specs)
print(f'{len(oxc)} sources, {total} static import and re-export specifiers by oxc-parser 0.147.0; the lane\'s scanner differs on {bad} source(s)')
PY
cat $E/specifiers-against-oxc.txt | tee -a $E/summary.new
mv $E/summary.new $E/summary.txt
git status --short -- . ':!docs/research'
