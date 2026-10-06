from pathlib import Path
import hashlib, json, subprocess
root=Path('/Users/pooks/Dev/lean4-effect4')
out=Path('/private/tmp/codex-effect4-overnight-monitor/heartbeats/2026-10-06T113637Z/questions')
head='2ee2aa91ef0edfacf4a2ab30f537b2fccf3b6620'
paths=['AGENTS.md','docs/STATE.md','docs/core/decisions.md','docs/RUNTIME-COVERAGE.md',
'docs/research/2026-10-05-seat-MASK-receipt.md',
'docs/research/2026-10-05-claude-lead/briefs/seat-pool-brief.md',
'docs/research/2026-10-05-claude-lead/module-cards/pool.md',
'docs/research/2026-10-05-claude-lead/module-cards/pool-probes/pool-lifecycle.ts',
'docs/research/2026-10-05-claude-lead/module-cards/pool-probes/pool-lifecycle.rc112.out',
'docs/research/2026-10-05-claude-lead/module-cards/pool-probes/pool-lifecycle.v401.out',
'scripts/generate-effect-runtime-census.sh','scripts/check-effect-runtime-census.sh',
'generated/effect-runtime-census.tsv','Test/Audit/RuntimeCoverage.lean',
'src/Effect4/Machine/Frames.lean','src/Effect4/Laws/Program/Typed/Mask.lean',
'Test/Program/MaskContract.lean','vendor/effect-4.0.0-rc.112/src/internal/effect.ts',
'vendor/effect-4.0.1/src/Pool.ts']
manifest=[]
for path in paths:
    b=subprocess.check_output(['git','show',f'{head}:{path}'],cwd=root)
    dest=out/'sources'/path; dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
    manifest.append(dict(path=path,commit=head,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),working_matches=(root/path).read_bytes()==b))
(out/'sources.json').write_text(json.dumps(manifest,indent=2)+'\n')
source=(out/'sources/vendor/effect-4.0.0-rc.112/src/internal/effect.ts').read_bytes()
lines=source.splitlines(keepends=True)
anchor=b'export const uninterruptibleMask = <A, E, R>(\n'
indices=[i for i,line in enumerate(lines) if line==anchor]
assert len(indices)==1
start=indices[0]; span=b''.join(lines[start:start+13]); (out/'mask-span.ts.txt').write_bytes(span)
span_receipt=dict(anchor=anchor.decode().rstrip(),anchor_occurrences=1,offsets=[0,12],line_span=[start+1,start+13],sha256=hashlib.sha256(span).hexdigest(),source_sha256=hashlib.sha256(source).hexdigest())
(out/'mask-span.json').write_text(json.dumps(span_receipt,indent=2)+'\n')
print(json.dumps(dict(sources=len(manifest),all_working_match=all(s['working_matches'] for s in manifest),mask_span=span_receipt),indent=2))
