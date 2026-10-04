import Effect4.Laws.Program.Typed.Residual

set_option autoImplicit false
namespace KripkeResumeResearch
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def oldWorld : W := initialWorld (EffTy.pure .unit)
def newWorld : W := oldWorld.addToken Api.root 0 (EffTy.pure .nat)
def unitCode : RProgram := .pure (.success .unit)

theorem fresh : oldWorld.Θ Api.root 0 = none := rfl
theorem grows : oldWorld.leHost newWorld :=
  ⟨(park_extension _ _ _ _ fresh).1, fun _ _ h => h⟩
theorem new_declaration : newWorld.Θ Api.root 0 = some (EffTy.pure .nat) :=
  (park_extension _ _ _ _ fresh).2

theorem old_condition (root : ProgramSource) :
    Contracts.ResumeOk (TypedProg root) oldWorld Api.root 0 unitCode := by
  intro ty declared
  cases declared

theorem new_condition_refused (root : ProgramSource) :
    ¬ Contracts.ResumeOk (TypedProg root) newWorld Api.root 0 unitCode := by
  intro h
  have exit := TypedProg.pure_inv (h _ new_declaration)
  exact exit.1

theorem good_code_control (root : ProgramSource) :
    Contracts.ResumeOk (TypedProg root) newWorld Api.root 0 (.pure (.success (.nat 0))) := by
  intro ty declared
  rw [new_declaration] at declared
  cases declared
  exact .pure ⟨trivial, trivial⟩

/-- The whole token table need not be equal: the addressed lookup is sufficient. -/
theorem resume_at_stable_key (root : ProgramSource) {w w' : W}
    {target : FiberId} {token : Nat} {code : RProgram}
    (ord : w.leHost w') (same : w'.Θ target token = w.Θ target token)
    (h : Contracts.ResumeOk (TypedProg root) w target token code) :
    Contracts.ResumeOk (TypedProg root) w' target token code := by
  intro ty declared
  rw [same] at declared
  exact typedProg_mono root w w' ty code ord (h ty declared)

/-- A fresh supply token cannot change an older addressed lookup, even for its owner. -/
theorem resume_below_fresh_supply (root : ProgramSource) (w : W)
    (owner target : FiberId) (supply token : Nat) (ty : EffTy) (code : RProgram)
    (unused : w.Θ owner supply = none) (below : token < supply)
    (h : Contracts.ResumeOk (TypedProg root) w target token code) :
    Contracts.ResumeOk (TypedProg root) (w.addToken owner supply ty) target token code := by
  have ord : w.leHost (w.addToken owner supply ty) :=
    ⟨(park_extension _ _ _ _ unused).1, fun _ _ h => h⟩
  apply resume_at_stable_key root ord ?_ h
  change (if target = owner then tableInsert (w.Θ target) supply ty else w.Θ target) token =
    w.Θ target token
  by_cases same : target = owner
  · rw [if_pos same]
    exact if_neg (Nat.ne_of_lt below)
  · rw [if_neg same]

#print axioms fresh
#print axioms grows
#print axioms new_declaration
#print axioms old_condition
#print axioms new_condition_refused
#print axioms good_code_control
#print axioms resume_at_stable_key
#print axioms resume_below_fresh_supply
end KripkeResumeResearch
