#!/usr/bin/env python3
"""Read repository/candidates; stage reviewable D patches under /tmp only.
Never writes the repository or invokes Lean/build/generation/git mutations.
Re-run after proof corrections. Generated patches remain UNCHECKED until root tests them.
The two red fixture message files must contain exact #guard_msgs expected bodies.
"""
from pathlib import Path
import argparse, difflib, hashlib, json
ap=argparse.ArgumentParser()
ap.add_argument('--repo',default='/Users/pooks/Dev/lean4-effect4-slice6')
ap.add_argument('--invariant',default='/Users/pooks/Dev/lean4-effect4-slice6/docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/D/probes/InvariantCandidate.lean')
ap.add_argument('--trace',default='/Users/pooks/Dev/lean4-effect4-slice6/docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/D/probes/TraceCandidate.lean')
ap.add_argument('--out',default='/tmp/d-integration/staged')
ap.add_argument('--trace-red-message')
ap.add_argument('--ledger-red-message')
a=ap.parse_args(); repo=Path(a.repo).resolve();out=Path(a.out).resolve()
if not (str(out).startswith('/tmp/') or str(out).startswith('/private/tmp/')):
    raise SystemExit('Output must stay under /tmp; this tool never applies patches.')
out.mkdir(parents=True,exist_ok=True)
base={};state={};receipts=[]
def read(p):
    if p not in state:
        text=(repo/p).read_text() if (repo/p).exists() else None
        state[p]=text;base[p]=text
    return state[p]
def replace_once(text,old,new):
    if text.count(old)!=1: raise ValueError(f'Expected exactly one anchor: {old[:100]!r}')
    return text.replace(old,new,1)
def between(text,start,end):
    if text.count(start)!=1: raise ValueError(f'Non-unique start section {start!r}')
    begin=text.index(start); finish=text.index(end,begin)
    return text[begin:finish]
def patch(stage,updates):
    root=out/stage;root.mkdir(exist_ok=True);diff=[];items=[]
    for p,new in updates.items():
        old=read(p)
        if old==new: continue
        diff.extend(difflib.unified_diff((old or '').splitlines(True),(new or '').splitlines(True),
            fromfile='a/'+p if old is not None else '/dev/null',
            tofile='b/'+p if new is not None else '/dev/null'))
        if new is not None:
            dest=root/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(new)
        items.append({'path':p,'before_sha256':hashlib.sha256(old.encode()).hexdigest() if old is not None else None,
                      'after_sha256':hashlib.sha256(new.encode()).hexdigest() if new is not None else None})
        state[p]=new
    (root/'source.patch').write_text(''.join(diff))
    (root/'paths.json').write_text(json.dumps(items,indent=2)+'\n')
    receipts.append({'stage':stage,'paths':items})
def message(path,label):
    return Path(path).read_text().strip() if path else 'D_RED_MESSAGE_'+label+'_MUST_BE_RECORDED_BY_ROOT'
trace=Path(a.trace).read_text()
trace=trace[trace.index('set_option autoImplicit false'):]
trace=trace[:trace.index('\nend Draft.TraceAgreement')+len('\nend Draft.TraceAgreement')]+'\n'
trace=trace.replace('declare_aesop_rule_sets [Effect4.StepInv]\n','')
trace=trace.replace('Draft.TraceAgreement','Effect4.Api.TraceFacts.Agreement')
if 'Slice6Probe' in trace: raise ValueError('Research bank import leaked into source body')
trace_positive='''
namespace Effect4.Api.TraceFacts.Agreement
open Effect4 Effect4.Machine Effect4.Program

/-- The named bank supplies the conditional emit equation. -/
theorem emit_with_bank (m : NativeMachine)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (h : Ok m) (hf : NoFork events) : Ok (m.emit events) := by
  aesop (rule_sets := [Effect4.StepInv])

end Effect4.Api.TraceFacts.Agreement
'''
old_trace=read('src/Effect4/Laws/Api/TraceOrigin.lean')
old_trace='\n'.join(line for line in old_trace.splitlines() if not line.startswith('import '))+'\n'
old_trace=old_trace.replace('#proof_wanted step_agrees\n','').replace('#proof_wanted reachable_agrees\n','')
proofrefs='''#obligation_proved Effect4.Api.TraceFacts.M1Trace.load_agrees :=
  @Effect4.Api.TraceFacts.Agreement.Native.load_agrees
#obligation_proved Effect4.Api.TraceFacts.M1Trace.step_agrees :=
  @Effect4.Api.TraceFacts.Agreement.Native.step_agrees
#obligation_proved Effect4.Api.TraceFacts.M1Trace.reachable_agrees :=
  @Effect4.Api.TraceFacts.Agreement.Native.reachable_agrees

'''
old_trace=replace_once(old_trace,'#typed_state_obligations Effect4.Api.TraceFacts.M1Trace ceiling 2',
    proofrefs+'#typed_state_obligations Effect4.Api.TraceFacts.M1Trace ceiling 0')
trace_source='''import Effect4.Laws.Api.Supervision
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Auto.Obligations

/-! Diagnostic agreement of the ordered (parent, child, daemon) observations.
This does not observe source paths or prove that recorded parents/flags are correct. -/

'''+trace+trace_positive+old_trace
trace_red='''import Effect4.Laws.Api.TraceOrigin

namespace Test.Machine.StepInvRulesRed
open Effect4 Effect4.Machine Effect4.Program Effect4.Api.TraceFacts.Agreement

/--
'''+message(a.trace_red_message,'TRACE')+'''
-/
#guard_msgs (error) in
example (m : NativeMachine)
    (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (h : Ok m) (hf : NoFork events) : Ok (m.emit events) := by
  aesop

#print axioms Effect4.Api.TraceFacts.Agreement.emit_with_bank
end Test.Machine.StepInvRulesRed
'''
rules=replace_once(read('src/Effect4/Laws/Auto/RuleSets.lean'),
    'Effect4.Reader, Effect4.Checker, Effect4.Stores, Effect4.StoreKernel, Effect4.Fibers]',
    'Effect4.Reader, Effect4.Checker, Effect4.Stores, Effect4.StoreKernel, Effect4.Fibers,\n  Effect4.StepInv]')
rules+='\n/-! `Effect4.StepInv` carries leaf equations for machine facts. Allocation laws keep their\nnecessary invariant premises; trace emission requires a no-fork observation. -/\n'
all_tests=replace_once(read('Test/All.lean'),'import Test.Program.TypedStateRulesRed\n',
    'import Test.Program.TypedStateRulesRed\nimport Test.Machine.StepInvRulesRed\n')
patch('01-trace-user',{'src/Effect4/Laws/Auto/RuleSets.lean':rules,
    'src/Effect4/Laws/Api/TraceOrigin.lean':trace_source,
    'Test/Machine/StepInvRulesRed.lean':trace_red,'Test/All.lean':all_tests})

inv=Path(a.invariant).read_text()
first=inv.index('namespace Draft.ForkLedger')
generic=inv[first:inv.index('\nsection Native\n',first)]
# First section Native contains load + conditional wrappers; only load is needed below.
load=between(inv,'theorem load_ok','/-- Conditional native wrapper.')
normal=between(inv,'section Normalization','end Normalization')+'end Normalization\n'
native_start=inv.index('namespace Native\n',inv.index('section Normalization'))
native=inv[native_start:inv.index('\nend Draft.ForkLedger',native_start)]+'\nend Draft.ForkLedger\n'
generic=generic.replace('open Effect4 Effect4.Machine Effect4.Program', 'open Effect4 Effect4.Machine')
generic_source='''import Effect4.Laws.Machine.ForkLedger
import Effect4.Laws.Machine.Lift

/-! The allocation view needed by ledger lookup: distinct fiber and child IDs, both below
nextId, with each record child present. Parent, daemon and source-site correctness are separate. -/
set_option autoImplicit false

'''+generic+normal+'\nend Draft.ForkLedger\n'
generic_source=generic_source.replace('Draft.ForkLedger','Effect4.Machine.ForkLedger.Invariant')
native_source='''import Effect4.Laws.Machine.ForkLedgerInvariant
import Effect4.Laws.Program.Guard.Core

/-! The four ledger lookup facts on raw native decision prefixes. No reference evaluator
or M6 instance is claimed. All command cases and all eight outside-loop edits are covered. -/
set_option autoImplicit false

namespace Draft.ForkLedger
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

'''+load+native
native_source=native_source.replace('Draft.ForkLedger','Effect4.Machine.ForkLedger.Invariant')
ledger_positive='''
namespace Effect4.Machine.ForkLedger.Invariant.Native
open Effect4 Effect4.Machine Effect4.Program

/-- Replacing a fiber requires the named ID-preservation normalization rule. -/
theorem update_with_bank (m : NativeMachine) (f : NFiber)
    (h : Effect4.Machine.ForkLedger.Invariant.Ok m) :
    Effect4.Machine.ForkLedger.Invariant.Ok (m.update f) := by
  aesop (rule_sets := [Effect4.StepInv])

end Effect4.Machine.ForkLedger.Invariant.Native
'''
native_source+=ledger_positive
ledger_red='''
namespace Test.Machine.StepInvRulesRed
open Effect4 Effect4.Machine Effect4.Program

/--
'''+message(a.ledger_red_message,'LEDGER')+'''
-/
#guard_msgs (error) in
example (m : NativeMachine) (f : NFiber)
    (h : Effect4.Machine.ForkLedger.Invariant.Ok m) :
    Effect4.Machine.ForkLedger.Invariant.Ok (m.update f) := by
  aesop

#print axioms Effect4.Machine.ForkLedger.Invariant.Native.update_with_bank
end Test.Machine.StepInvRulesRed
'''
new_guard=replace_once(read('src/Effect4/Laws/Program/Guard.lean'),
    'import Effect4.Laws.Program.Guard.MemoIds\n',
    'import Effect4.Laws.Program.Guard.MemoIds\nimport Effect4.Laws.Program.Guard.ForkLedger\n')
new_red='import Effect4.Laws.Program.Guard.ForkLedger\n'+read('Test/Machine/StepInvRulesRed.lean')+ledger_red
patch('02-ledger-user',{'src/Effect4/Laws/Machine/ForkLedgerInvariant.lean':generic_source,
    'src/Effect4/Laws/Program/Guard/ForkLedger.lean':native_source,
    'src/Effect4/Laws/Program/Guard.lean':new_guard,'Test/Machine/StepInvRulesRed.lean':new_red})

# Move only declarations depending on the diagnostic projection; interleaved source,
# allocation and runtime status laws stay in the library.
supervision=read('src/Effect4/Laws/Api/Supervision.lean')
projection=between(supervision,'/-- Diagnostic trace projection.', '/-! ## A measure on the program')
frame_start=supervision.index('section MachineForks\n')
frame_end=supervision.index('omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in\ntheorem M1Trace.forkedOf_append',frame_start)
frame_header=supervision[frame_start:frame_end]
prefix='omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in\n'
chunk1=between(supervision,prefix+'theorem M1Trace.forkedOf_append',prefix+'/-- `spawn` appends exactly one event')
chunk2=between(supervision,prefix+'theorem M1Trace.spawn_forked',prefix+'/-- The id the spawn mints')
chunk3=between(supervision,'omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core in\ntheorem M1Trace.start_forked','end MachineForks')
projection=projection.replace('Runtime supervision reads fiber origins.','Runtime supervision reads the fork ledger.')
trace_defs=between(supervision,'namespace Effect4.Api.TraceFacts\n','namespace Effect4.Api.M1Trace\n')
refs='\n'.join(line for line in supervision.splitlines() if line.startswith('#obligation_proved Effect4.Api.M1Trace.'))+'\n'
for chunk in [between(supervision,'/-- Diagnostic trace projection.', '/-! ## A measure on the program'),
              chunk1,chunk2,chunk3,trace_defs,refs]:
    supervision=replace_once(supervision,chunk,'')
supervision=replace_once(supervision,
    '#typed_state_obligations Effect4.Api.M1Trace ceiling 4 using aesop (rule_sets := [Effect4.Stores, Effect4.Fibers])',
    '#typed_state_obligations Effect4.Api.M1Trace ceiling 0 using aesop (rule_sets := [Effect4.Stores, Effect4.Fibers])')
intro=between(supervision,'**(a) Diagnostic fork flags.**','The static half is whole-program')
supervision=replace_once(supervision,intro,
    '**(a) Static fork sites and ledger entries.** Runtime provenance is read from the fork\nledger. The diagnostic trace laws and agreement control are in `Test/Api/TraceOrigin.lean`.\n\n')
moved='''import Effect4.Laws.Api.Supervision
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Auto.Obligations

/-! The diagnostic fork trace agrees with the fork ledger's ordered triples on raw native
prefixes. Source paths and semantic correctness of the recorded flags remain separate laws. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Effect4.Api
open Effect4 Effect4.Machine Effect4.Program
universe u v

'''+projection+frame_header+chunk1+chunk2+chunk3+'end MachineForks\nend Effect4.Api\n\n'+trace_defs
moved+='\n'.join(line for line in read('src/Effect4/Laws/Api/TraceOrigin.lean').splitlines() if not line.startswith('import '))+'\n'
moved+='\n'+refs+'\n#typed_state_obligations Effect4.Api.M1Trace ceiling 0 using aesop (rule_sets := [Effect4.Stores, Effect4.Fibers])\n'
laws=replace_once(read('src/Effect4/Laws.lean'),'import Effect4.Laws.Api.TraceOrigin\n','')
contract=replace_once(read('Test/Api/SupervisionContract.lean'),
    'import Effect4.Laws.Api.Supervision\n','import Test.Api.TraceOrigin\n')
red=replace_once(read('Test/Machine/StepInvRulesRed.lean'),
    'import Effect4.Laws.Api.TraceOrigin\n','import Test.Api.TraceOrigin\n')
patch('03-diagnostic-move',{'src/Effect4/Laws/Api/Supervision.lean':supervision,
    'src/Effect4/Laws/Api/TraceOrigin.lean':None,'src/Effect4/Laws.lean':laws,
    'Test/Api/TraceOrigin.lean':moved,'Test/Api/SupervisionContract.lean':contract,
    'Test/Machine/StepInvRulesRed.lean':red})
manifest={'status':'UNCOMPILED REVIEW CANDIDATES; no repository changes made',
          'inputs':{str(Path(a.invariant)):hashlib.sha256(Path(a.invariant).read_bytes()).hexdigest(),
                    str(Path(a.trace)):hashlib.sha256(Path(a.trace).read_bytes()).hexdigest()},
          'stages':receipts,
          'red_messages_ready':bool(a.trace_red_message and a.ledger_red_message)}
final=out/'final';final.mkdir(exist_ok=True)
for p,content in state.items():
    if content is not None:
        dest=final/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(content)
manifest['deleted']=[p for p,content in state.items() if content is None]
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(out/'manifest.json')
if not manifest['red_messages_ready']:
    print('Red fixture messages are placeholders. Do not apply until replaced by checked output.')
