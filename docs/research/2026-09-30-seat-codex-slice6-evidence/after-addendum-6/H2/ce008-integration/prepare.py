from pathlib import Path
import difflib, hashlib, json, re
ROOT = Path('/Users/pooks/Dev/lean4-effect4-slice6')
OUT = Path('/private/tmp/h2-independent-review/ce008-integration')
TEST = 'Test/Program/H2PartOne.lean'
REG = 'Test/Counterexamples/REGISTER.md'
BLOCK = '''
/-! E4-TYPED-CE-008: retained part-two saved-frame witness from the model-probe audit.
The local FullExitOk additionally refuses missingService at an empty requirement row.
The accepted loop stack returns that failure unchanged across different requirement rows.
This is a saved-frame witness, not a reachable-run claim or a refutation of base FitsExit;
part one's live ExitOk deliberately admits missingService at both rows. -/
namespace MissingServiceTransport
open Effect4.Program.Typed.Contracts

/-- The proposed full exclusion, retained here only to expose its transport obligation. -/
def fullForbidden (ty : EffTy) : Reason Err Defect FiberId Ann → Bool
  | .die defect _ => defect == .badName || defect == .notImplemented ||
      (defect == .missingService && ty.requires == Env.Requirement.empty)
  | _ => false

def FullNoShapeDefect (ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure cause => cause.reasons.any (fullForbidden ty) = false

def FullExitOk (w : W) (ty : EffTy) (ex : ExitV) : Prop :=
  FitsExit w ty ex ∧ FullNoShapeDefect ty ex

def inner : EffTy := ⟨.never, .never, Env.Requirement.single nativeScopeKey⟩
def outer : EffTy := EffTy.pure .unit
def missing : CauseV := Cause.die .missingService
def name : EffName := .abort
def saved : RSaved := ⟨.pure (.success .unit), [], false, none, false⟩

/-- The answer-never loop meets the actual frame protocol, whose continuation is vacuous. -/
theorem loop_admitted (src : ProgramSource) (w : W) :
    StackAccepts (TypedProg src) FullExitOk (frameProtocols src) w inner outer
      [.loop name .unit] := by
  apply StackAccepts.cons (middle := outer)
  · apply FrameAccepts.loop
    exact LoopProtocol.step (tin := inner) (tout := outer) rfl (fun _ h => False.elim h)
  · exact StackAccepts.nil outer

theorem input_ok (w : W) : FullExitOk w inner (.failure missing) :=
  ⟨fitsExit_of_clean w inner missing rfl, rfl⟩

theorem provenance : InterruptProvenance saved := by
  constructor
  · intro c h
    cases h
  · intro h
    cases h

/-- The actual stack walk passes the failure through the loop without changing it. -/
theorem output_eq (interp : RInterp) :
    (popR interp (.failure missing) [.loop name .unit] saved).2 =
      some (.failure missing) := rfl

theorem output_bad (w : W) : ¬ FullExitOk w outer (.failure missing) := by
  intro typed
  have excluded := typed.2
  change true = false at excluded
  exact Bool.noConfusion excluded

#print axioms loop_admitted
#print axioms input_ok
#print axioms provenance
#print axioms output_eq
#print axioms output_bad
end MissingServiceTransport
'''
old_test = (ROOT / TEST).read_text()
assert old_test.count('end Test.Program.H2PartOne') == 1
assert 'namespace MissingServiceTransport' not in old_test
assert 'Effect4.Program.Typed.RRace' in old_test
assert ': Option ExitV' in old_test
new_test = old_test.replace('end Test.Program.H2PartOne', BLOCK + '\nend Test.Program.H2PartOne')
old_reg = (ROOT / REG).read_text()
old_ce003 = '| `E4-TYPED-CE-003` | SEEDED | Checking Fail payloads in StrongCause excludes badShapeExit | `Test/Counterexamples/Machine/Semantics/StrongExitDefect.lean`: `bad_shape_still_admitted`, for every stronger value predicate | keep ordinary defects admitted by exit typing and prove absence of badShape production from admitted source/control separately |'
new_ce003 = '| `E4-TYPED-CE-003` | SEEDED | Checking Fail payloads in StrongCause excludes badShapeExit | `Test/Counterexamples/Machine/Semantics/StrongExitDefect.lean`: `bad_shape_still_admitted`, for every stronger value predicate | The base claim remains true: Fail-payload membership does not reject Die reasons. H2 part one adds shared `ExitOk = FitsExit ∧ NoShapeDefect`, excluding only badName and notImplemented at typed exit boundaries; base Fits/FitsExit stay unchanged. `Test/Program/H2PartOne.lean`: `base_badName_still_fits`, `badName_refused`, `notImplemented_refused`, `user_die_admitted`. MissingService is held under E4-TYPED-CE-008; general M5/M6 proofs remain open. |'
assert old_reg.count(old_ce003) == 1
assert 'E4-TYPED-CE-007' not in old_reg
assert 'E4-TYPED-CE-008' not in old_reg
ce007 = '| `E4-TYPED-CE-007` | REPAIRED 2026-10-01 | A clause on finished fibers alone keeps shape defects out of typed states | Historical field-only probe: `docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/H2/h2-part-one-controls/FieldOnlyRed.lean`, `Research.Slice6.H2FieldOnlyRed.strengthened_input`, `strengthened_output_false`, `firstStep_queue`, `produced_queue_refused`. Current controls: `Test/Program/H2PartOne.lean`, `bad_current_code_refused`, `notImplemented_current_code_refused`, `RaceFailureBuffers.new_badName_refused`, `new_notImplemented_refused`, and ordinary-die/interrupt controls. | Shared ExitOk excludes badName and notImplemented throughout typed exit positions, including current code and buffered race failures. The historical field-only predicate and its refutation remain exact research evidence; base FitsExit is unchanged. This repairs the placement gap, not the open M5/M6 preservation proofs. |'
ce008 = '| `E4-TYPED-CE-008` | SEEDED 2026-10-01 | The existing frame contracts transport the proposed full missingService exclusion across requirement rows | `Test/Program/H2PartOne.lean`: `MissingServiceTransport.loop_admitted`, `input_ok`, `provenance`, `output_eq`, `output_bad`; original audit: `docs/research/2026-09-30-codex-review-model-probe/probes/SavedFrameTransport.lean`, namespace `AuditH2`. | A never-answer loop accepts the failure at a nonempty requirement row and returns it unchanged at an empty row, where local FullExitOk refuses it. Amend the frame/operation contracts with scoped/provision controls before adopting this part-two exclusion (row 117). This is a saved-frame witness, not a reached-run claim; part one still admits missingService. |'
ce006 = next(line for line in old_reg.splitlines() if line.startswith('| `E4-TYPED-CE-006`'))
new_reg = old_reg.replace(old_ce003, new_ce003).replace(ce006, ce006 + '\n' + ce007 + '\n' + ce008)
manifest = {'state':'UNCOMPILED; root owns the Lean lane', 'historical_source':'docs/research/2026-09-30-codex-review-model-probe/probes/SavedFrameTransport.lean', 'new_theorems':[], 'files':[]}
all_patches = []
for rel, old, new, patch in [(TEST,old_test,new_test,'ce008-controls.patch'), (REG,old_reg,new_reg,'register.patch')]:
    for directory,text in [('baseline',old),('candidate',new)]:
        path = OUT / directory / rel
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(text)
    diff = ''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
    (OUT / patch).write_text(diff)
    all_patches.append(diff)
    manifest['files'].append({'path':rel,'baseline_sha256':hashlib.sha256(old.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(new.encode()).hexdigest()})
for name in re.findall(r'^theorem (\w+)',BLOCK,re.M):
    assert '#print axioms '+name in BLOCK
    line = next(i for i,s in enumerate(new_test.splitlines(),1) if s.startswith('theorem '+name+' ' ) or s.startswith('theorem '+name+' :'))
    manifest['new_theorems'].append({'name':'Test.Program.H2PartOne.MissingServiceTransport.'+name,'candidate_line':line,'audit_name':'AuditH2.'+name})
assert len(manifest['new_theorems']) == 5
assert new_test.count('#print axioms ') == old_test.count('#print axioms ') + 5
(OUT / 'integration.patch').write_text(''.join(all_patches))
(OUT / 'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'directory':str(OUT),'new_theorems':manifest['new_theorems'],'total_prints':new_test.count('#print axioms ')},indent=2))
