import Effect4.Laws.Modules.Latch.Registration

/-! Latch registration readers and finite controls.
The general connector keeps independent model behavior and its table and scope premises.
The finite source evaluations cover duplicates, waiter priority, detached batches, and a bad table. -/
set_option autoImplicit false
namespace Test.Program.LatchRegistration
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Latch.Model

def table : Table := { handle := fun n => ⟨n + 100⟩, hint := fun n => ⟨n + 200⟩ }
def cases : List State :=
  [{isOpen := true, waiters := [1]},
   {isOpen := false},
   {isOpen := false, waiters := [1, 1, 2], pending := [1, 9], scheduled := true},
   {isOpen := false, pending := [1, 1, 9], scheduled := true},
   {isOpen := false, pending := [1], scheduled := true},
   {isOpen := false, pending := [1], scheduled := false},
   (flush {isOpen := false, pending := [1, 2], scheduled := true}).1]

def observe (source : TermSrc) (tb : Table) (s : State) : Option Val :=
  match source {names := ["id", "hint", "cell"]} [] with
  | .error _ => none
  | .ok term => evalTerm [.promise (tb.handle 1), .promise (tb.hint 1), cellVal tb s] term

#guard cases.all fun s => observe (Latch.awaitStep (var "id") (var "hint") (var "cell")) table s =
  some (.list [.bool (awaitLatch s 1).2, cellVal table (awaitLatch s 1).1])
#guard cases.all fun s => observe (Latch.withdrawStep (var "id") (var "cell")) table s =
  some (.list [.unit, cellVal table (withdraw s 1).1])
#guard [false, true].all fun isOpen =>
  ((Latch.initialStep (bool isOpen)) {} []).toOption.bind (evalTerm [] ·) =
    some (cellVal table (initial isOpen))

-- Aliasing request handles invalidates the independent-number cleanup connector.
def aliasing : Table := {handle := fun _ => ⟨0⟩, hint := fun n => ⟨n⟩}
def duplicateKeys : State := {isOpen := false, waiters := [2, 1]}
#guard observe (Latch.withdrawStep (var "id") (var "cell")) aliasing duplicateKeys !=
  some (.list [.unit, cellVal aliasing (withdraw duplicateKeys 1).1])

-- The shared law is read at a duplicate-bearing model state and arbitrary caller terms.
example (tb : Table) (injective : tb.Injective) {idSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val}
    (hi : Reads idSrc env path vals (.promise (tb.handle 1)))
    (hc : Reads cellSrc env path vals (cellVal tb duplicateKeys)) (scope : vals.length = env.names.length) :
    Reads (Latch.withdrawStep idSrc cellSrc) env path vals
      (.list [.unit, cellVal tb (withdraw duplicateKeys 1).1]) :=
  withdrawStep_agrees tb injective duplicateKeys 1 hi hc scope
end Test.Program.LatchRegistration
