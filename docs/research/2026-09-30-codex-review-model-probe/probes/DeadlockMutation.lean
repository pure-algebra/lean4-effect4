import Effect4.Api
namespace AuditR12
open Effect4 Effect4.Machine Effect4.Program
def waiting : NativeEff := .bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0))
def m := (Api.replay waiting 200 [Api.evaluate, Api.flush]).machine
#guard (Api.replay waiting 200 [Api.evaluate, Api.flush]).outcome = .frontier
#guard m.fibers.all (fun f => f.exit.isSome || f.parked != .notParked)
#guard m.armed = []
#guard Api.hostReasons m = []
#guard Api.timerReasons m = []
#guard m.middlewareInstalled = false
theorem old_false : m.middlewareInstalled = false := by decide +kernel
theorem middleware_changes : (stepDecision (interpOf waiting []) 200 m .installMiddleware).middlewareInstalled = true := rfl
theorem machine_changes : stepDecision (interpOf waiting []) 200 m .installMiddleware ≠ m := by
  intro h
  have he := congrArg (fun x => x.middlewareInstalled) h
  rw [middleware_changes, old_false] at he
  exact Bool.noConfusion he
#print axioms old_false
#print axioms middleware_changes
#print axioms machine_changes
end AuditR12
