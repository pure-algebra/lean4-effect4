#!/usr/bin/env python3
"""Seat F (2026-10-01, landing item 9): research notes cited by tracked files outside
docs/research but not tracked themselves, at a given commit.

Usage: untracked-citations.py REV [--docs] [EXT ...]
  REV     the commit to read (its tracked files and its index of tracked notes)
  --docs  scan only the documents: README.md, AGENTS.md, docs/*.md, docs/core/*.md, docs/design/*.md
  EXT     file extensions to scan (default: md)
Prints each untracked cited note, whether it exists on disk in the main checkout, and the
tracked files that cite it.
"""
import re, subprocess, sys, os
REPO = '/Users/pooks/Dev/lean4-effect4-seat-F'
DISK = '/Users/pooks/Dev/lean4-effect4'   # where the untracked notes live (read only)
rev = sys.argv[1] if len(sys.argv) > 1 else 'HEAD'
docs_only = '--docs' in sys.argv[2:]
exts = tuple('.' + e for e in ([a for a in sys.argv[2:] if a != '--docs'] or ['md']))
def in_scope(f):
    if not docs_only:
        return True
    return f in ('README.md', 'AGENTS.md') or (f.startswith('docs/') and f.count('/') == 1) or \
        f.startswith('docs/core/') or f.startswith('docs/design/')
files = subprocess.run(['git', '-C', REPO, 'ls-tree', '-r', '--name-only', rev],
                       capture_output=True, text=True).stdout.split('\n')
tracked = set(f for f in files if f)
pat = re.compile(r'(?:docs/research/|\.\./research/|research/)([A-Za-z0-9_.\-/]+?\.(?:md|lean|py|sh|json|txt|log|ts|tsv|ml))')
cited = {}
for f in sorted(tracked):
    if f.startswith('docs/research/') or not f.endswith(exts) or not in_scope(f):
        continue
    text = subprocess.run(['git', '-C', REPO, 'show', f'{rev}:{f}'], capture_output=True, text=True).stdout
    for m in pat.finditer(text):
        note = 'docs/research/' + m.group(1).rstrip('.')
        cited.setdefault(note, set()).add(f)
untracked = {n: s for n, s in cited.items() if n not in tracked}
print(f"rev {rev}, extensions {exts}, documents only {docs_only}: {len(cited)} cited research paths, {len(untracked)} untracked")
for n in sorted(untracked):
    on_disk = os.path.exists(os.path.join(DISK, n))
    print(f"{'on disk' if on_disk else 'MISSING'}\t{n}\t<- {', '.join(sorted(untracked[n]))}")
