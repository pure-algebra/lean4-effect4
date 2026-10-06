import subprocess,re,json,pathlib
out=pathlib.Path(__file__).resolve().parent
seat='/Users/pooks/Dev/lean4-effect4-qtypes'
old='00a37ffc';new='525c78b3'
def read(rev,path):return subprocess.check_output(['git','-C',seat,'show',rev+':'+path],text=True)
def header(s,name):
 m=re.search(r'(?m)^\s*(?:private )?(?:theorem|proof_goal) '+re.escape(name)+r'\b',s)
 assert m is not None,name
 block=s[m.start():];end=re.search(r'\s:=\s',block)
 assert end is not None,name
 return block[:end.start()].strip()
def norm(s):return ' '.join(s.split())
items=[]
for path,name,removed in [
 ('src/Effect4/Laws/Program/ReferenceTyping.lean','typeOfProgram_expandRefs','    (hempty : (p.expandRefs.refSites []).isEmpty = true)\n'),
 ('src/Effect4/Laws/Program/CheckedTyping.lean','checkTypedProgram_of_hasTy','    (expanded : program.expandRefs.refSites [] = [])\n'),
 ('src/Effect4/Laws/Program/ReferenceExpansion.lean','expanded_refs_nil_of_wf',''),
 ('src/Effect4/Laws/Program/PathOrder.lean','lt_append_of_lt',''),
 ('src/Effect4/Laws/Program/PathOrder.lean','countP_lt_countP',''),
 ('src/Effect4/Laws/Program/PathOrder.lean','rank_lt_length',''),
 ('src/Effect4/Laws/Program/PathOrder.lean','rank_lt_rank','')]:
 a=header(read(old,path),name);b=header(read(new,path),name)
 # The deleted premise is followed by the conclusion colon on that same line.
 stripped=a.replace(removed.rstrip('\n'),'').replace('\n :','\n    :') if removed else a
 assert norm(stripped)==norm(b),(name,stripped,b)
 items.append({'path':path,'name':name,'before':a,'after':b,'only_deleted_premise':removed.strip() or None,'expected_statement_change_matches':True})
controls={'changed_assumption_refused':norm(items[0]['after'].replace('p.layerRefsWF = true','p.layerRefsWF = false'))!=norm(items[0]['after']),
'changed_conclusion_refused':norm(items[0]['after'].replace('= typeOfProgram sig p','≠ typeOfProgram sig p'))!=norm(items[0]['after'])}
assert all(controls.values())
r={'before_revision':old,'after_revision':new,'comparisons':items,'controls':controls,'method':'Starts at declaration keyword, excludes body assignment; every binder and complete conclusion retained.'}
(out/'statement-comparison.json').write_text(json.dumps(r,indent=2)+'\n')
print('Seven full statement comparisons and two changed-statement controls passed.')
