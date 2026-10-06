from pathlib import Path
import json, hashlib, subprocess, datetime
p=Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-06-capability-design/interop')
m=json.loads((p/'source-manifest.json').read_text()); rev=m['commit']
def write(n,o): (p/n).write_text(json.dumps(o,indent=2)+'\n')
obligations=[
 {'id':'located-checked-context','priority':1,'status':'proposed; uncompiled; no theorem stated',
  'concept':'residual-program-typing','required_property':'A computed located context gives the existing local typing judgment at the context in the admitted whole-program derivation.',
  'requirements':['R1','R4','R8'],'registry_relation':'Proposed connector serving rebuild-admission and the readable/typed face part of R8; operation-data-scoped supplies the separate scope facts. Do not claim a current registry entry.',
  'consumers':['Routing Boolean-select printer','inspectAt expected-type view','same-sort checked edit'],
  'statement_shape':'inspectChecked b selection = ok view implies that selection resolves to the exact node, view erases to that node, and the existing sort-specific judgment holds at view.environment/mode under b.table. The source-versus-expanded occurrence relation is an explicit premise or computed witness.',
  'premises':['Exact admitted Built and ordered table','Named structural path scheme and matching node sort','Correct local environment and inLoop flag where required','Explicit reference occurrence mapping, or an initial reference-free domain','No arbitrary source closure invariance'],
  'observations':['Selected syntax unchanged','Exact local type and binder environment','Located refusal outside the domain'],
  'reuse':[{'name':'TypedProgram.hasTy','path':'src/Effect4/Laws/Program/CheckedTyping.lean'}, {'name':'checkTypedProgram_sound','path':'src/Effect4/Laws/Program/CheckedTyping.lean'}, {'name':'checkStmt/checkStmts and sort-specific checks','path':'src/Effect4/Program/Checker.lean'}, {'name':'Node.replaceAt_spec','path':'src/Effect4/Laws/Program/References.lean'}],
  'prerequisite':'Choose the first concrete view domain and source/expanded occurrence convention. Reuse binder metadata and checker derivation rather than add a second checker.',
  'exclusions':['No target typechecking theorem','No semantic rewrite theorem','No whole-run safety','No typed holes or minimum explanation claim'],
  'controls':['Bind/Ref/loop environments positive','One-binder deletion and fold-binder-order mutants','Duplicated reference occurrence refusal or exact mapping']},
 {'id':'versioned-checked-edit','priority':2,'status':'proposed facade over existing laws',
  'concept':'initial-algebras-folds; residual-program-typing','required_property':'A request edits exactly its selected old node, and successful whole rebuilding admits the exact resulting candidate.',
  'requirements':['R1','R8'],'registry_relation':'Wrapper helpers of addressed-replacement and rebuild-admission; those existing statements do not need duplicate goals.',
  'consumers':['External checked editor','Program manipulation API'],
  'statement_shape':'edit b request = ok b2 implies exact base/selected-node equality, Node.replaceAt root path replacement = some candidate, b2.program=candidate, b2.table=b.table, b2.rowNames=b.rowNames, and b2.admitted is indexed by those fields. On refusal, the held b is unchanged.',
  'premises':['Exact artifact resolution, not digest equality alone','Same structural sort','Supported schema/path version','Whole candidate checked against unchanged table'],
  'observations':['Exact program/table/name map before and after','Existing located BuildRefusal'],
  'reuse':[{'name':'Node.replaceAt_spec/replaceAt_self/replaceAt_overwrite/at_replaceAt_disjoint','path':'src/Effect4/Laws/Program/References.lean'}, {'name':'Authoring.rebuild_spec/rebuild_admitted','path':'src/Effect4/Laws/Program/Author.lean'}],
  'prerequisite':'First editor caller and finite base-selection record; exact Node wrapper codec only when that record crosses a wire.',
  'exclusions':['No raw-subtree move without relocation','No type equality requirement','No behavior equivalence','No hash collision axiom'],
  'controls':['Fresh selection succeeds','Stale base and wrong sort refuse','Same-typed capture mutation is not certified as a behavior-preserving edit']},
 {'id':'bundle-and-envelope-codecs','priority':2,'status':'proposed data instances; generic laws already exist',
  'concept':'exact-codecs','required_property':'New finite transport records form an exact canonical image, with a supported version/profile checked separately from decoding.',
  'requirements':['R1','R3','R8','R13'],'registry_relation':'Helper of the exact-codecs carrier property and the consuming admission/replay claim. Propose a registry placement in the implementing slice only if the new property is not already covered.',
  'consumers':['Host-validated program loading','Selection/edit transport','Replay prefix transport'],
  'statement_shape':'For a new Canonical carrier E, decode(encode e)=some e under (toVal e).WF; decode bytes=some e implies bytes=encode e. Loading decoded bundle succeeds only with the actual AdmittedProgram at its exact rows and supported profile.',
  'premises':['Canonical class laws','Framing WF under 2^64','Current Built domain ⟨rows, []⟩','Unsupported versions/extensions explicitly refused'],
  'observations':['Exact bytes/data','Named decode/admission refusal'],
  'reuse':[{'name':'Canonical.decode_encode/decode_exact/encode_injective','path':'src/Effect4/Store/Domain/Canonical.lean'}, {'name':'Author.Internal.finishBuild','path':'src/Effect4/Api/Author.lean'}, {'name':'admitProgram','path':'src/Effect4/Program/Admission.lean'}],
  'prerequisite':'One actual external caller; generated instance in current generated group; distinguish transport/profile checks from shape acceptance.',
  'exclusions':['No raw-codec-to-admission implication','No hash injectivity','No general JSON exactness','No arbitrary service declaration admission'],
  'controls':['Program with its true table loads','Same program and reordered table cannot reuse a certificate','Retired tags/unknown schema/unsupported extension refuse']},
 {'id':'replay-prefix-access','priority':3,'status':'API composition of existing theorems; new adapters uncompiled',
  'concept':'host-session-protocol; translation-simulation','required_property':'The requested prefix replays exactly from the same admitted inputs, preserving attempted decoded commands and phases.',
  'requirements':['R6','R12','R13'],'registry_relation':'Uses R13 journal_replays; raw-machine projection uses journal-machine-replay or journal-position-replay only with their exact premises. Do not restate them as a new ledger.',
  'consumers':['Time-travel inspection','Host script debugging','Checkpoint cache validation'],
  'statement_shape':'observe((Run.open b id budget profile).play prefix) is the named response; for reached s, reopening with s.built/id/budget/profile and s.journal reconstructs s. A validated checkpoint is equal to this replay result.',
  'premises':['Exact bundle','Both budget fields','Same session id/profile','All decoded commands including refused/frontier commands','Reached for reconstructing an arbitrary supplied Run','Separate malformed-byte-row transcript'],
  'observations':['Full Run equality for journal law','Only the named projection when crossing a target boundary'],
  'reuse':[{'name':'Run.play_append/journal_replays/drive_eq_play','path':'src/Effect4/Laws/Run.lean'}, {'name':'RunnerBytes.replayRows/stepRow','path':'src/Effect4/Api/RunnerBytes.lean'}],
  'prerequisite':'Initial request replays from the beginning; cached checkpoints optional later. External start-domain policy must name Run.open versus HostSession.start.',
  'exclusions':['No original host execution','No truth of external answers','No general budget-additive resumption','No resource release/liveness'],
  'controls':['Split-prefix reconstruction','Dropped refused command mutant','Changed compile budget refusal','Malformed byte row leaves runner unchanged']},
 {'id':'named-observation-provenance','priority':3,'status':'proposed adapter contract, not target agreement',
  'concept':'translation-simulation','required_property':'A reported observation is exactly the named existing projection, with its measurement or replay provenance.',
  'requirements':['R6','R8','R13'],'registry_relation':'Serves existing named face/profile and journal projection claims; any new target agreement is a separate placed obligation.',
  'consumers':['TypeScript host comparisons','OCaml api_replay adapter','Clock and scheduler inspector'],
  'statement_shape':'Each response tag fixes one payload schema and producer projection; a target agreement result additionally supplies the named relation and satisfied premises. No unrepresented session field is counted as independently measured.',
  'premises':['Exact observation version','Exact bundle/prefix/target profile','Numeric representability for target carrier','Independent field provenance when a comparison mixes sources'],
  'observations':['HostProtocol.State OR Run.Observation OR explicit machine projection','Terminal exit and stores only under completed-fragment profile'],
  'reuse':[{'name':'RunnerBytes.observeBytes/schemaOf','path':'src/Effect4/Api/RunnerBytes.lean'}, {'name':'Run.observe/Run.work','path':'src/Effect4/Run.lean'}, {'name':'api_replay','path':'ocaml/engine/api_engine.ml'}, {'name':'Conform.Report','path':'tools/Conform/Core/Report.lean'}],
  'prerequisite':'Name the first finite projection and target relation; use real row table and both budgets for the general OCaml entry point.',
  'exclusions':['No HostSession ledger in raw engine replay','No invented whole observation coverage','No full stores/traces in Run.Observation','No host-object revival from handle key'],
  'controls':['Session-state and run-observation schema separation','Lean-ledger-copy negative control','Target numeric boundary refusal']},
 {'id':'straight-loop-completed-observation','priority':3,'status':'existing theorem reuse, not a new universal theorem',
  'concept':'translation-simulation','required_property':'One completed exit-and-stores observation can be consumed through the existing straight or Looped agreement law.',
  'requirements':['R8'],'registry_relation':'Existing loop-agreement and run_eq_meaning. Keep R10 module expansions separate.',
  'consumers':['Proof-applicability display','Certified rewrite comparison','Run completion inspector'],
  'statement_shape':'Given Looped e=true and meaningB k e [] Stores.empty=(some x,s), loopAgreement yields a bound beyond which Api.run finishes with x and s. Straight e uses meaningB_straight/loopAgreement_of_straight.',
  'premises':['Named fragment','Completed budgeted meaning','Empty initial environment/stores in the public LoopAgreement statement','Machine fuel at least the supplied existential bound'],
  'observations':['Exit and full final stores'],
  'reuse':[{'name':'meaningB_straight/loopAgreement_of_straight/LoopAgreement','path':'src/Effect4/Laws/Program/LoopAgreement.lean'}, {'name':'Agreement.loopAgreement','path':'src/Effect4/Laws/Program/Agreement/Loop.lean'}, {'name':'StraightEq','path':'src/Effect4/Laws/Program/MeaningEq.lean'}],
  'prerequisite':'Named completion evidence, not just equal fuel. For rewriting, separately prove the relevant all-environment/store relation.',
  'exclusions':['No loop termination guarantee','No equal finite-prefix/fuel claim','No Queue/Pool wrapper membership inferred from sequential callers','No typed error from unfinished meaning'],
  'controls':['Straight positive through bridge','Terminating Looped positive','Unfinished meaning preserves its partial stores']},
 {'id':'proof-application-boundary','priority':4,'status':'proposed tooling adapter; existing proof machinery retained',
  'concept':'translation-simulation (consumer placement); exact-codecs for request carrier only','required_property':'The reported theorem application is about the exact submitted subjects, under discharged or explicitly outstanding premises.',
  'requirements':['R1','R8','R13'],'registry_relation':'Each adapter belongs to its existing consumer claim. This is a tooling correctness condition, not another semantic registry or a generic prove endpoint.',
  'consumers':['Selected edit explanation','Fragment agreement applicability','Inspection explanation with real premises'],
  'statement_shape':'A successful application response reconstructs the expected proposition in the current environment, validates the theorem and universes/axioms, checks the application, and reports actual transitive goal status. Undischarged premises or missing adapters remain unresolved/refused.',
  'premises':['Fixed environment and source identities','Closed application with exact finite adapter parameters','Independent expected-proposition reconstruction','Existing transitive axiom ceiling and Plan dependency accounting'],
  'observations':['Existing report status/evidence','Actual theorem proposition and named premises','Separate authored placement and measured dependency edges'],
  'reuse':[{'name':'ProofRef.validate/checked_theorem%','path':'tools/ProofGraph/Proof.lean'}, {'name':'Plan','path':'tools/ProofGraph/Plan.lean'}, {'name':'Conform.Report','path':'tools/Conform/Core/Report.lean'}],
  'prerequisite':'One current claim-specific adapter; do not serialize Expr as runtime program data.',
  'exclusions':['No proof from declaration name','No proof from JSON status','No goal/modulo treated as proved','No universal theorem application without premises'],
  'controls':['Exact valid closed application','Changed proposition/universe/axiom mutant','Missing premise and unresolved goal controls']}
]
write('obligations.json',{'status':'research proposals and reuse routes; not ratified or proved','commit':rev,'items':obligations})
source_map=[
 {'capability':'load/check','data':['Api.Program','RowTable','Built','AdmittedProgram'], 'owners':['src/Effect4/Api/Built.lean','src/Effect4/Api/Author.lean','src/Effect4/Program/Admission.lean'], 'law_owner':['src/Effect4/Laws/Program/Author.lean','src/Effect4/Laws/Program/CheckedTyping.lean'], 'gap':'Exact transport bundle and an external checked host operation; current Built service declarations remain empty.'},
 {'capability':'select/context/edit','data':['Node NativeOp','List Nat','TyEnv','EffTy','GenTy','LayerTy','StmtTy'], 'owners':['src/Effect4/Program/NodeLenses.lean','src/Effect4/Program/Checker.lean','src/Effect4/Program/Typing/Rules.lean'], 'law_owner':['src/Effect4/Laws/Program/References.lean','src/Effect4/Laws/Program/CheckedTyping.lean'], 'gap':'Computed located checker context plus source/expanded occurrence relation; version-bound edit facade.'},
 {'capability':'exact data exchange','data':['Canonical','ShapeDoc','Ty','Representation','Val'], 'owners':['src/Effect4/Store/Domain/Canonical.lean','src/Effect4/Store/Domain/Derived/Program.lean','src/Effect4/Schema/Representation.lean','src/Effect4/Schema/Codec.lean'], 'law_owner':['src/Effect4/Laws/Schema/Codec.lean'], 'gap':'Finite wrapper instances only when called for; no second algebra.'},
 {'capability':'session/replay','data':['HostSession.Header','Runner.Command','Run','Run.Observation','Api.Budget'], 'owners':['src/Effect4/Api/HostSession.lean','src/Effect4/Api/Runner.lean','src/Effect4/Api/RunnerBytes.lean','src/Effect4/Run.lean'], 'law_owner':['src/Effect4/Laws/Run.lean','src/Effect4/Laws/Api/RunnerBytes.lean'], 'gap':'Bound prefix request and distinct named observations; cached checkpoints derive from the same journal.'},
 {'capability':'clock view','data':['ClockMillis','Run.Work'], 'owners':['src/Effect4/Data/ClockMillis.lean','src/Effect4/Store/Domain/Clock.lean','src/Effect4/Api/TestClock.lean'], 'law_owner':['src/Effect4/Data/ClockMillis.lean'], 'gap':'No new unit policy; target range/profile and any Work codec explicit.'},
 {'capability':'straight and loops','data':['StraightEq','Looped','meaningB','LoopAgreement'], 'owners':['src/Effect4/Laws/Program/MeaningEq.lean','src/Effect4/Laws/Program/DenoteB.lean','src/Effect4/Laws/Program/LoopAgreement.lean'], 'law_owner':['src/Effect4/Laws/Program/Agreement/Loop.lean'], 'gap':'Joint named completed observation; no finite-prefix relation or async-module generalization inferred.'},
 {'capability':'proof explanation/application','data':['ProofRef','Plan','Conform.Report'], 'owners':['tools/ProofGraph/Proof.lean','tools/ProofGraph/Plan.lean','tools/Conform/Core/Report.lean','tools/Tools/Semantics.lean','tools/Tools/SemanticsRegistry.lean'], 'law_owner':[], 'gap':'Claim-specific host-validated application adapters; preserve actual premises and transitive goals.'},
 {'capability':'target/CLI projection','data':['ground program description','generated TypeScript carrier','generated OCaml carrier'], 'owners':['tools/Tools/ProgramStructure.lean','tools/Tools/HostProtocol.lean','tools/Drivers/TsGen.lean','ts/eff/ingest/cli.ts','ocaml/engine/api_engine.ml','ocaml/engine/api_engine_inst.ml'], 'law_owner':[], 'gap':'Thin operation drivers and named numeric/observation adapters; no new checker or interpreter.'}
]
write('source-map.json',{'commit':rev,'items':source_map})
write('literature.json',{'kind':'primary-source selected readings; no theorem transferred automatically','sources':[
 {'title':'Combinators for Bidirectional Tree Transformations: A Linguistic Approach to the View-Update Problem','url':'https://www.cis.upenn.edu/~bcpierce/papers/lenses-toplas-final.pdf','locator':'Sections 3.1–3.4','used_for':'Partial-lens round trips, totality and update-law separation; version-counter counterexample','limit':'No behavioral or typed Eff editing theorem follows from lens laws','evidence':'Read primary PDF via web tool; no downloaded-PDF hash claimed'},
 {'title':'Hazelnut: A Bidirectionally Typed Structure Editor Calculus','url':'https://arxiv.org/pdf/1607.04180','locator':'Section 3.3.1, Theorems 1–3','used_for':'Action sensibility and movement erasure invariance; distinguish synthesis from analysis','limit':'Its hole calculus is not Eff; no typed-hole feature proposed','evidence':'Read primary PDF via web tool'},
 {'title':'Language Server Protocol 3.17 metamodel','url':'https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/metaModel/metaModel.json','locator':'VersionedTextDocumentIdentifier, TextDocumentEdit, DidChangeTextDocumentParams, staleRequestSupport','used_for':'Separate versioned edit and sequential change contracts; avoid misuse of ContentModified','limit':'Protocol analogy only; no LSP implementation proposed','evidence':'Read official metamodel via web tool'},
 {'title':'Bidirectional Type Slicing','url':'https://arxiv.org/abs/2607.12197','pdf':'https://arxiv.org/pdf/2607.12197','locator':'Metatheorems in prior algebra packet; Section 10 for general minimum-size hardness','used_for':'Local type explanation with named context; avoid minimum explanation guarantee','limit':'Research preprint, different hole/precision calculus','evidence':'Primary reading retained in prior 2026-10-06-tree-control-review/algebra/literature.json; current report reuses that verified reading'}]})
# Pure receipt checks: existing source bytes, valid packet references, and complete design records.
checks=[]
for f in m['files']:
 data=(p/f['snapshot']).read_bytes() if not Path(f['snapshot']).is_absolute() else Path(f['snapshot']).read_bytes()
 checks.append({'check':'snapshot hash','path':f['path'],'ok':hashlib.sha256(data).hexdigest()==f['sha256']})
known={f['path'] for f in m['files']}
for item in source_map:
 for f in item['owners']+item['law_owner']:
  checks.append({'check':'source map points to frozen source','path':f,'ok':f in known})
required=['concept','required_property','requirements','registry_relation','consumers','statement_shape','premises','observations','reuse','prerequisite','exclusions','controls']
for o in obligations:
 checks.append({'check':'obligation carries required placement and limits','id':o['id'],'ok':all(bool(o.get(k)) for k in required)})
write('verification.json',{'scope':'Pure source-hash and packet-reference checks only; no proposed API execution','commit':rev,'checks':checks,'passed':sum(c['ok'] for c in checks),'failed':[c for c in checks if not c['ok']]})
write('commands.json',{'commands':[{'command':'git rev-parse HEAD','result':rev,'scope':'initial frozen revision'}, {'command':'git show '+rev+':<each manifest path>','result':'79 exact committed source snapshots; see source-manifest.json'}, {'command':"git grep -n -E 'Canonical \\(?(_root_\\.)?Effect4\\.(Program\\.(Node|GenTy|LayerTy|Checker.StmtTy)|Api.Budget|Run.Work)|Canonical (Node|GenTy|LayerTy|StmtTy|Budget|Work)' "+rev+' -- src tools','exit_code':1,'output':'','scope':'Bounded textual search; no direct Canonical instances located for these wrappers, not a completeness proof over elaboration'}, {'command':'python3 '+str(p/'finish-packet.py'),'result':'verification.json; source/packet checks only'}]})
artifacts=['report.md','envelopes.txt','obligations.json','controls.md','source-map.json','source-manifest.json','literature.json','verification.json','commands.json','finish-packet.py','committed-verification.json']
write('receipt.json',{'task':'Capability and interoperability API research','commit':rev,'status':'Research complete; all APIs/obligations proposed and uncompiled','source_files':len(m['files']),'verification':'verification.json','no_project_execution':True,'no_repo_edits':True,'no_build_compiler_runtime_generator_install':True,'actual_checks':'Frozen source hashes, packet references, complete obligation metadata; primary literature inspected','design_controls':'controls.md; proposed, not run','limitations':['No new API implementation or theorem checked','Existing theorem statements inspected, not rebuilt','TypeScript/OCaml face agreement remains scoped and open','Current Built service-declaration gap retained','No hash injectivity assumed','No general loop termination, liveness or budget-resumption claim'], 'artifacts':[{'path':a,'sha256':hashlib.sha256((p/a).read_bytes()).hexdigest(),'bytes':(p/a).stat().st_size} for a in artifacts]})
print(json.dumps({'source_files':len(m['files']),'pure_checks_passed':sum(c['ok'] for c in checks),'failed':sum(not c['ok'] for c in checks),'obligations':len(obligations)}))
