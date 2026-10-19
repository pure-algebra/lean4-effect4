from pathlib import Path
import csv,json,re
P=Path(__file__).resolve().parent;C=Path('/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-18-slices/w2-engine-mutants');W=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4')
a=json.loads((P/'test-times.json').read_text());b=json.loads((P/'test-rechecks.json').read_text());tests={r['test']:r for r in a['rows']};tests.update({r['test']:r for r in b['rows']})
rows=list(csv.DictReader((C/'results-B.tsv').open(),delimiter='\t'));mutants={r['id']:r for r in rows};kills={}
for id,r in mutants.items():
 for test in r['failing tests'].split(','):
  if test not in ['','-','stm_admit']:kills.setdefault(test,[]).append(id)
zero=[t for t in tests if t.startswith('engine/') and Path(t).stem not in kills]
survivors=[k for k,r in mutants.items() if not set(r['failing tests'].split(',')) - {'','-','stm_admit'}]
count1=re.search(r'  check\n    \(Printf\.sprintf "C2 tools/list lists.*?\(List.length names = 20\);', (W/'ocaml/engine/test/kit/test_mcp.ml').read_text(),re.S).group(0)
count2='  require (List.length E4_kind.all = 23) "kind census";'
out={'timed_binaries':len(tests),'all_passed':all(r['status']==0 for r in tests.values()),'seconds_sum':sum(r['seconds'] for r in tests.values()),'slowest':sorted(tests.values(),key=lambda r:r['seconds'],reverse=True)[:12], 'campaign_unique_mutants':len(mutants),'campaign_survivors_including_unrelated_stm_failure':survivors,'test_kills':kills,'no_C4_kill':zero,'no_C4_kill_count':len(zero),'delete_count_checks_lines':len(count1.splitlines())+len(count2.splitlines()),'additive_tool_control':{'before':{'count_check':20==20,'table_check':list(range(20))==list(range(20))},'after_one_generated_method_added':{'count_check':21==20,'table_check':list(range(21))==list(range(21))}}}
(P/'test-analysis.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k not in ['test_kills','no_C4_kill']},indent=2))
