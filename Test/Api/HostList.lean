import Effect4.Laws.Api.HostDrive

/-!
# A host that answers from a list

A program run under the reply host of its row table (`tapeHost`, read as a reactor by
`Run.Reactor.ofHost`): the run is opened, its root evaluated, and each call the session meets
takes the list's next exit, whatever its row and request. This is what a list of preloaded
answers was before DI-23 deleted it. Each answer is now a decision that the session checks and
applies. On H9's fragment, with answers that the rows admit without allocating, H9 gives the
run's meaning (`runWith_host_denotes`); a handle row is outside it.

The host tells calls apart only by the order in which the session meets them, so it suits a
run of one fiber; keyed replies tell concurrent calls apart (`E4-HOST-CE-006`).
-/

set_option autoImplicit false

namespace Test.Api.HostList

open Effect4 Effect4.Machine Effect4.Program

/-- The program run under the list host at the budget, or `none` when the program is not
admitted at the table. -/
def run (p : Api.Program) (table : RowTable) (exits : List ExitV) (budget : Api.Budget := {}) :
    Option Effect4.Run :=
  match Api.admitProgram p ⟨table, []⟩ with
  | .ok admitted =>
    some (Effect4.Run.runWith ⟨table, p, admitted, []⟩
      (Effect4.Run.Reactor.ofHost table (Denote.tapeHost table)) exits "list" budget).1
  | .error _ => none

/-- The root's exit of the run under the list host; `none` when the program is not admitted or
its root has no exit. -/
def exit (p : Api.Program) (table : RowTable) (exits : List ExitV) : Option ExitV :=
  (run p table exits).bind (·.exit)

/-- The stores the run under the list host leaves; `none` when the program is not admitted. -/
def stores (p : Api.Program) (table : RowTable) (exits : List ExitV) : Option Stores :=
  (run p table exits).map (·.machine.state)

end Test.Api.HostList
