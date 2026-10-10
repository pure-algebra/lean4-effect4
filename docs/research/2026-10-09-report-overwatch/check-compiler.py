from pathlib import Path
import hashlib,json,re
r=Path(__file__).resolve().parent; logs=r/"checks"
text=(logs/"ClosureControls.c").read_text(); rows=[]
for name,table in [("l_ReviewClosure_rebuilt",True),("l_ReviewClosure_instSizeOfRebuilt",True),("l___private_ClosureControls_0__ReviewClosure_privateRebuilt",True),("l_ReviewClosure_proofOnly",False),("l_ReviewClosure_asData",False)]:
    match=re.search(r"LEAN_EXPORT [^\n]*\b"+re.escape(name)+r"\([^\n]*\)\{",text)
    assert match,name
    start=match.end()-1;depth=0;end=start
    for end in range(start,len(text)):
        if text[end]=="{":depth+=1
        elif text[end]=="}":
            depth-=1
            if depth==0:break
    body=text[match.start():end+1]
    assert ("l_List_range(" in body)==table,name
    if name=="l_ReviewClosure_proofOnly":
        assert not re.search(r"\bl_[A-Za-z0-9_]+\(",body.split("{",1)[1]),body
    rows.append({"name":name,"range_call_present":table,"body":body})
(logs/"compiler-controls.json").write_text(json.dumps({"command":["python3",str(r/"check-compiler.py")],"source_sha256":hashlib.sha256((r/"ClosureControls.lean").read_bytes()).hexdigest(),"c_sha256":hashlib.sha256(text.encode()).hexdigest(),"functions":rows,"matched":True},indent=2)+"\n")
print("PASS: all three table variants compile to table construction; proof-only function calls no compiled Lean function")
