#!/usr/bin/env python3
"""Read the fifteen named branches through Git and retain pinned review inputs."""
from pathlib import Path
import json
import subprocess

WT = Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
HERE = Path(__file__).resolve().parent / 'backlog'
HERE.mkdir(exist_ok=True)
BRANCHES = ['codex/vessel-dogfood','codex/abstraction-probes','codex/vessel-model',
 'codex/vessel-fmi','codex/vessel-step','codex/probe-canonical-image','probe/sexp-face',
 'claude/laughing-northcutt-cd0311','claude/math-d3','claude/sad-williamson-6d3b65',
 'seat/schema-interop','claude/codec-arm-lemmas','claude/gracious-shamir-5b34bd',
 'codex/probe-pull-dispatch','codex/probe-source-resolution']
def git(*args):
    return subprocess.check_output(['git','-C',str(WT),*args],text=True)

rows=[]
for branch in BRANCHES:
    head=git('rev-parse',branch).strip()
    slug=branch.replace('/','--')
    log=git('log','--format=%h %s',f'HEAD..{head}')
    names=git('diff','--name-status',f'HEAD...{head}')
    diff=git('diff',f'HEAD...{head}')
    stat=git('diff','--stat',f'HEAD...{head}')
    (HERE/(slug+'.patch')).write_text(diff)
    (HERE/(slug+'.log')).write_text(log+'\n'+stat+'\n'+names)
    rows.append({'branch':branch,'head':head,'commits':int(git('rev-list','--count',f'HEAD..{head}')),
                 'log':log.splitlines(),'files':names.splitlines(),'diff_bytes':len(diff.encode())})
(HERE/'branches.json').write_text(json.dumps(rows,indent=2)+'\n')
for row in rows:
    print(row['branch'],row['head'],row['commits'],'commits',len(row['files']),'paths',row['diff_bytes'],'diff bytes')
    print('\n'.join(row['log']))
