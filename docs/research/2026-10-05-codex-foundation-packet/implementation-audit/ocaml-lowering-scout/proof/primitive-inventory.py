from pathlib import Path
import re, json
root=Path('/Users/pooks/Dev/lean4-effect4')
def matched_names(path, start, end):
    text=(root/path).read_text().split(start,1)[1].split(end,1)[0]
    result=[]
    for line in text.splitlines():
        if line.lstrip().startswith('| ') and '=>' in line:
            result += re.findall(r'`([A-Za-z0-9_!.]+)',line.split('=>',1)[0])
    return set(result)
actual=matched_names('src/OCaml5/Lcnf/Translate.lean','def builtin?', '\n/--')
clock=matched_names('src/OCaml5/Lcnf/Clock.lean','def builtin?', '\nend OCaml5')
source=(root/'tools/Conform/Effect4/Lcnf.lean').read_text().split('def fidelityTable :',1)[1].split('def fidelityTableCovers',1)[0]
rows=set(re.findall(r'⟨`([A-Za-z0-9_!.]+)',source))
assert {'Nat.add','Nat.div','String.length','Array.mkEmpty'} <= actual & rows
assert 'Effect4.ClockMillis.add' in clock - rows
assert 'Nat.add' in (actual | clock) - (rows - {'Nat.add'})
result={'kind':'bounded source inventory, not Lean reflection or runtime evidence','main_literals':len(actual),'delegated_clock_literals':len(clock),'fidelity_names':len(rows),'missing_literal_names':sorted((actual|clock)-rows),'positive_controls':['Nat.add','Nat.div','String.length','Array.mkEmpty'],'negative_control':'dropping Nat.add from copied fidelity inventory creates missing Nat.add'}
print(json.dumps(result,indent=2))
