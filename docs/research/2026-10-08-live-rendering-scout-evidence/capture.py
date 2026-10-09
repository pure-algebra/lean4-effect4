from pathlib import Path
import hashlib, json, subprocess

primary = Path('/Users/pooks/Dev/lean4-effect4')
worktree = Path.cwd()
out = worktree / 'docs/research/2026-10-08-live-rendering-scout-evidence'
source_paths = [
    'docs/research/2026-10-06-native-view.md',
    'docs/research/2026-10-06-native-view-p1.md',
    'docs/research/2026-10-07-native-view-forms.md',
    'docs/research/2026-10-07-native-view-schemas-and-lowering.md',
    'docs/research/2026-10-06-native-view-probe/Scene.lean',
    'docs/research/2026-10-06-native-view-probe/lower-run.txt',
]
rows = []
for relative in source_paths:
    source = primary / relative
    data = source.read_bytes()
    saved = out / (source.name + '.snapshot.txt')
    saved.write_bytes(data)
    rows.append({'source': str(source), 'saved': str(saved.relative_to(worktree)),
                 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
for relative in [
    'tools/Tools/Query.lean', 'tools/Drivers/Query.lean',
    'src/Effect4/Program/Sketch.lean', 'src/Effect4/Program/Typing/Parts.lean',
    'src/Effect4/Program/Typing/Focus.lean', 'src/Effect4/Program/Typing/Table.lean',
    'src/Effect4/Program/Typing/Annotate.lean', 'src/Effect4/Api/Author.lean',
    'src/Effect4/Api/Built.lean', 'src/Effect4/Api/HostSession.lean',
    'src/Effect4/Api/RunnerBytes.lean', 'src/Effect4/Run/Basic.lean',
    'src/Effect4/Laws/Program/Sketch.lean', 'src/Effect4/Laws/Program/Typing/Parts.lean',
    'src/Effect4/Laws/Api/ModuleReadable.lean',
    'docs/research/2026-10-08-live-authoring.md',
    'docs/research/2026-10-08-host-authoring-boundary.md',
    'docs/research/2026-10-07-session-api-design.md',
]:
    data = (worktree / relative).read_bytes()
    rows.append({'source': str(worktree / relative), 'bytes': len(data),
                 'sha256': hashlib.sha256(data).hexdigest()})
manifest = {'reviewed_head': subprocess.check_output(['git','rev-parse','HEAD'], cwd=worktree, text=True).strip(),
            'primary_observed_head': subprocess.check_output(['git','rev-parse','HEAD'], cwd=primary, text=True).strip(),
            'artifacts': rows}
(out / 'source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('PASS source capture:', len(rows), 'source pins;', len(source_paths), 'exact retained artifacts')
