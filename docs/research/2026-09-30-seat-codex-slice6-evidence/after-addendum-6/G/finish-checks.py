import pathlib,subprocess,sys
here=pathlib.Path(__file__).resolve().parent
root=here.parents[4]
steps=[
('tests-2',['lake','build','Test.Program.ProvisionContract','Test.Program.AuthorContract','Test.Program.CheckerRulesRed','Test.Counterexamples.Machine.Semantics.LayerValue']),
('layer-controls',['lake','env','lean','-DwarningAsError=true','Test/Counterexamples/Machine/Semantics/LayerValue.lean']),
('axioms',['lake','env','lean','-DwarningAsError=true',str(here/'candidate/Axioms.lean')]),
('printer',['lake','env','lean','-DwarningAsError=true','Test/Codegen/TemplatesContract.lean']),
('corpus',['make','corpus'])]
for name,cmd in steps:
 r=subprocess.run([sys.executable,str(here/'check.py'),name,'.',*cmd],cwd=root)
 if r.returncode:raise SystemExit(r.returncode)
