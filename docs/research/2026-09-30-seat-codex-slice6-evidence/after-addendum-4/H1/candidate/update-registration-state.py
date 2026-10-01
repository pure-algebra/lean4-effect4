from pathlib import Path
out=Path('/private/tmp/h1-candidate')
def once(s,old,new):
 assert s.count(old)==1, (s.count(old),old[:90])
 return s.replace(old,new,1)
p=out/'src/Effect4/Laws/Program/Typed/Scheduler.lean'
s=p.read_text()
s=once(s,'def CommandAuthorityR (m : RState) : RCmd → Prop\n',(out/'registration-state-fragment.lean').read_text()+'def CommandAuthorityR (m : RState) : RCmd → Prop\n')
p.write_text(s)
p=out/'prepare.py'
s=p.read_text()
s=once(s,'    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m\n', '    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m\n')
old="  '    ?_, schedulerState_load p 20 20, observerState_load (p : ProgramSource) _ 20 20⟩')"
# The exact literal includes the leading question mark in the previous string segment.
old="  '  refine ⟨initialWorld ty, initial_world_valid _ p 20 20 closed, ⟨?_, ?_, ?_⟩,\\n    ?_, schedulerState_load p 20 20, observerState_load (p : ProgramSource) _ 20 20⟩')"
new="  '  refine ⟨initialWorld ty, initial_world_valid _ p 20 20 closed, ⟨?_, ?_, ?_⟩,\\n    ?_, schedulerState_load p 20 20, observerState_load (p : ProgramSource) _ 20 20,\\n    registrationState_load (p : ProgramSource) _ 20 20 noMarker⟩')"
s=once(s,old,new)
anchor='save(rel,s)\n\n# The requested historical falsifiers'
insert="""s = replace_once(s,
  'theorem typedStateF_load (p : NativeEff) (ty : EffTy) (closed : ClosedEff ty)\\n',
  'theorem typedStateF_load (p : NativeEff) (ty : EffTy) (closed : ClosedEff ty)\\n    (noMarker : raceRegistrationR (denoteR p p (rootPoint 20)) = none)\\n')
s = replace_once(s, 'typedStateF_load refProg _ ⟨rfl, rfl⟩ refProg_typedF',
  'typedStateF_load refProg _ ⟨rfl, rfl⟩ rfl refProg_typedF')
s = replace_once(s, 'typedStateF_load getProg _ ⟨rfl, rfl⟩ getProg_typedF',
  'typedStateF_load getProg _ ⟨rfl, rfl⟩ rfl getProg_typedF')
save(rel,s)

# The requested historical falsifiers"""
s=once(s,anchor,insert)
p.write_text(s)
p=out/'tests-fragment.lean'
s=p.read_text()
s=once(s,'    (closed : ClosedEff resultTy)\n    (code : ∀ w, TypedProg (p : ProgramSource) w resultTy (denoteR p p (rootPoint compileFuel)))',
'    (closed : ClosedEff resultTy)\n    (noMarker : raceRegistrationR (denoteR p p (rootPoint compileFuel)) = none)\n    (code : ∀ w, TypedProg (p : ProgramSource) w resultTy (denoteR p p (rootPoint compileFuel)))')
s=once(s,'    ?_, schedulerState_load p fuel compileFuel, observerState_load (p : ProgramSource) _ fuel compileFuel⟩',
'    ?_, schedulerState_load p fuel compileFuel, observerState_load (p : ProgramSource) _ fuel compileFuel,\n    registrationState_load (p : ProgramSource) _ fuel compileFuel noMarker⟩')
s=once(s,'theorem typed_loaded (p : NativeEff) (resultTy : EffTy) (closed : ClosedEff resultTy)\n',
 'theorem typed_loaded (p : NativeEff) (resultTy : EffTy) (closed : ClosedEff resultTy)\n    (noMarker : raceRegistrationR (denoteR p p (rootPoint 20)) = none)\n')
s=once(s,'  typed_loaded_at p resultTy 20 20 closed code', '  typed_loaded_at p resultTy 20 20 closed noMarker code')
s=once(s,'  typed_loaded program ty ⟨rfl, rfl⟩ loaded_code', '  typed_loaded program ty ⟨rfl, rfl⟩ rfl loaded_code')
s=once(s,'  typed_loaded sleeper (EffTy.pure .unit) ⟨rfl, rfl⟩ loaded_sleep_code', '  typed_loaded sleeper (EffTy.pure .unit) ⟨rfl, rfl⟩ rfl loaded_sleep_code')
s=once(s,'  typed_loaded_at sleeper (EffTy.pure .unit) 80 80 ⟨rfl, rfl⟩ loaded_sleep80_code', '  typed_loaded_at sleeper (EffTy.pure .unit) 80 80 ⟨rfl, rfl⟩ rfl loaded_sleep80_code')
p.write_text(s)
p=out/'Axioms.lean'
s=p.read_text().replace('#print axioms Effect4.Program.Typed.observerState_load', '#print axioms Effect4.Program.Typed.registrationState_load\n#print axioms Effect4.Program.Typed.observerState_load')
p.write_text(s)
