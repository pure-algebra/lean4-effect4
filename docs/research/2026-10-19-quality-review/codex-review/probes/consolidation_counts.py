from pathlib import Path
import json,re
W=Path('/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4'); P=Path(__file__).parent
blocks=[]
for f,names in {'src/Effect4/Store/Domain/Word.lean':['except_bind_ok'],'src/Effect4/Store/Domain/JsonText.lean':['except_bind_ok','except_map_ok'],'src/Effect4/Laws/Store/ShapeRead.lean':['except_bind_ok','except_map_ok'],'src/Effect4/Store/Domain/ShapeRead.lean':['unseenDefs','unseenDefs_cons_lt'],'src/Effect4/Program/TyExpand.lean':['unseen','unseen_lt','unseen_cons_lt']}.items():
 ls=(W/f).read_text().splitlines()
 for n in names:
  i=next(i for i,l in enumerate(ls) if re.match(r'(?:private )?(?:def|theorem) '+n+r'\b',l));j=i+1
  while j<len(ls) and ls[j].strip():j+=1
  blocks.append({'path':f,'declaration':n,'lines':j-i})
(P/'consolidation-counts.json').write_text(json.dumps(blocks,indent=2));print(json.dumps(blocks,indent=2))
