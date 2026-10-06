from pathlib import Path
import json,subprocess,hashlib
root=Path('/Users/pooks/Dev/lean4-effect4')
out=Path(__file__).parent
rev='4b57609c03ad0a38fd81cfc2c09ea5731dfe7ff0'
prior=Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-06-tree-control-review/typing/manifest.json')
paths=[x['path'] for x in json.loads(prior.read_text())['sources']]
paths += ['docs/STATE.md','docs/ARCHITECTURE.md','docs/core/machine-state.md','src/Effect4/Program/Authoring.lean','src/Effect4/Program/Authoring/Lifts.lean','src/Effect4/Program/Authoring/Loops.lean','src/Effect4/Program/Typing/Rules.lean','src/Effect4/Program/Typing/TermRefusal.lean','src/Effect4/Laws/Program/Typed/Contracts.lean','src/Effect4/Laws/Program/Typed/Residual.lean','src/Effect4/Laws/Program/Typed/Scheduler.lean','src/Effect4/Laws/Program/Typed/Commands/Clauses/Loop.lean','src/Effect4/Laws/Program/Typing/CheckInversion.lean','src/Effect4/Laws/Program/Typing/Inversion.lean','src/Effect4/Laws/Program/DenoteB.lean','src/Effect4/Laws/Program/LoopAgreement.lean','src/Effect4/Laws/Program/Agreement/Loop.lean','src/Effect4/Laws/Program/Iter.lean','src/Effect4/Laws/Program/IterLimit.lean','src/Effect4/Laws/Program/Folds/Denote.lean','src/Effect4/Laws/Program/ReferenceTyping.lean','src/Effect4/Codegen/Forms.lean','src/Effect4/Laws/Codegen/Forms.lean','tools/Effect4Gen/binders.json']
rows=[]
for path in dict.fromkeys(paths):
    data=subprocess.check_output(['git','show',f'{rev}:{path}'],cwd=root)
    p=out/'source'/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    rows.append({'path':path,'revision':rev,'git_blob':subprocess.check_output(['git','rev-parse',f'{rev}:{path}'],cwd=root,text=True).strip(),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'snapshot':str(p)})
(out/'manifest.json').write_text(json.dumps({'repository':str(root),'revision':rev,'initial_status':'clean','evidence':'committed source only, not new Lean acceptance','sources':rows},indent=2)+'\n')
print(json.dumps({'revision':rev,'files':len(rows)}))
