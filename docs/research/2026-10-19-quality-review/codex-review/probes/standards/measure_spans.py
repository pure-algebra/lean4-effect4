#!/usr/bin/env python3
"""Measure exact existing function spans. No estimated replacement savings."""
from pathlib import Path
import json
root = Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4/ocaml/engine/cas')
out = Path(__file__).resolve().parent
spans = {}
for file, name in [('e4_pack.ml', 'fsync_dir'), ('e4_index.ml', 'fsync_dir'),
                   ('e4_wal.ml', 'fsync_dir'), ('e4_wal.ml', 'flush_buf'),
                   ('e4_wal.ml', 'open_'), ('e4_control.ml', 'commit')]:
    lines = (root / file).read_text().splitlines()
    begin = next(i for i, line in enumerate(lines) if line.startswith('let ' + name + ' '))
    end = next(i for i in range(begin, len(lines)) if lines[i] == ';;')
    spans[file + ':' + name] = end - begin + 1
(out / 'function-spans.json').write_text(json.dumps(spans, indent=2) + '\n')
print(json.dumps(spans, indent=2))
