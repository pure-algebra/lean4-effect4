"""Replay the source searches cited by the review. No source writes."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path('/Users/pooks/Dev/lean4-effect4')
HERE = Path(__file__).resolve().parent
GROUPS = {
    'P': ('structure Live|opened|structure LiveRecord|version|session :|def restore|def feed|def commands|unresolved|def serve',
          ['src/Effect4/Run/Live.lean','src/Effect4/Run/LiveRecord.lean','src/Effect4/Run/Event.lean']),
    'C': ('certifiedB|def feed|rechecked|layersProgram|checkModule|checkLayers|firstRefFault|fromCache|SuggestResult|def suggest|supplied|structure Part|bodyNotDeclared',
          ['src/Effect4/Program/Typing','src/Effect4/Program/Checker.lean']),
    'F': ('Certified|fills_compose|materialize_refFree|materialize_congr|add_wf|materializeDoc|staleRevision|staleBase|structure FillSet',
          ['src/Effect4/Program/Typing/FillSet.lean','src/Effect4/Laws/Program/FillSet.lean']),
    'S': ('Store.get|Store.putNode|Store.putRoot|nextVersion|def putOr|RootKind|structure Tree|putNode_fresh_closed|holds_of_injective|wf_closed|wf_apply|wfFrom_apply|verify_sound.',
          ['src/Effect4/Store','rocq/StoreLaws.v']),
    'D': ('Unknown_tag|Oversize|Bad_pack|Store_error|check_pure|put_bytes|readmit_tail|add_node|wf_closed|E4_log|Store/[^ /]+.lean',
          ['ocaml/engine/cas/e4_cas.ml','ocaml/engine/cas/e4_cas.mli','ocaml/engine/cas/e4_index.ml','ocaml/engine/cas/e4_wal.mli']),
    'K': ('CascadingStore|Domain.Cascade|address_inj|holds_of_injective|wf_closed|putNode_fresh_closed|verify_sound.|Api.Author.buildIn|Store.putOr',
          ['src','Test','tools']),
    'N': ('E4_nat|E4_log.Vec|bench_array|Array.*list', ['ocaml']),
    'G': ('expected_command|record.get|def run|def prepare|result_path', ['scripts/lib/gate_cache.py']),
    'M': ('leadingIdent|ocamlMatchArms|allowedMatch|Ty_|ocaml-type-block|stripPrefix',
          ['tools/Conform/Manifest/Readers.lean','tools/Conform/Effect4/mirrors.json']),
}

# Checker moved into Typing on this branch; use its directory as the authority.
GROUPS['C'] = (GROUPS['C'][0], ['src/Effect4/Program/Typing'])
selected = sys.argv[1:] or list(GROUPS)
rows = []
for label in selected:
    pattern, paths = GROUPS[label]
    command = ['rg','-n',pattern,*paths]
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    rows.append({'id':label,'command':command,'exit':result.returncode,'output':result.stdout})
    if result.returncode > 1:
        raise RuntimeError(result.stdout)
if not sys.argv[1:]:
    (HERE/'source-readings.json').write_text(json.dumps(rows, indent=2)+'\n')
for row in rows:
    print(json.dumps({k:v for k,v in row.items() if k!='output'}))
    if sys.argv[1:]:
        print(row['output'])
