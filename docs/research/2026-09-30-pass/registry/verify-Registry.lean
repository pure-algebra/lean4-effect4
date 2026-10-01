import registry.Core
import Test.Program.ExitTypeLane

/-! Verifier of the registry seat: two cases the seat's fixtures do not run.

Research evidence outside the Test root. Base `be15b062`. Written by the adversarial verifier;
it imports the seat's `Core.lean` unchanged (compiled into the session scratchpad, as the
seat's note §12 does). Finite checks, not proofs.

1. A race two binders deep whose entrants read the binders. The seat's fixtures hold no race
   (`declared.log`: fixture race entrants 0), and its race guard in `StaticEnv.lean` checks the
   declarations only. Here the entrants run, under every lane tape, and each exit is checked
   against the registry's declaration of that entrant.
2. The daemon view. The seat found that a running layer build reads as an unpinned daemon.
   A running race entrant does too: `raceAll` launches entrants as daemons
   (`Machine/Fibers.lean:958`) that no parent tracks and no scope pins, and `statusOf`
   (`Api/Supervision.lean:215-226`) has no race case. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Research.Pass.RegistryVerify.Registry
open Effect4 Effect4.Machine Effect4.Program Research.Pass.Registry
open Test.Program.ExitTypeLane (fits tapes hostReplies)

abbrev E := Eff NativeOp
def n (i : Nat) : Term := .lit (.nat i)
def s (x : String) : Term := .lit (.str x)
def es : List E → Effs NativeOp | [] => .nil | e :: r => .cons e (es r)

/-- The first entrant fails with the outer number (level 0); the second succeeds with the
inner string (level 1). -/
def raceUnder : E :=
  .bind (.succeed (n 7)) (.bind (.succeed (s "x"))
    (.withFiber (.raceAll (es [.fail (.var 0), .succeed (.var 1)]))))

/-- The levels swapped: a fold that confused them would declare the wrong types here. -/
def raceSwapped : E :=
  .bind (.succeed (n 7)) (.bind (.succeed (s "x"))
    (.withFiber (.raceAll (es [.fail (.var 1), .succeed (.var 0)]))))

/-- Every fiber of every lane tape: its id, its declared answer and error, and whether its
exit (if any) fits the declaration. -/
def verdicts (p : E) : List (Nat × Option (Ty × Ty) × Bool) :=
  match Api.typeOf p [] with
  | none => []
  | some rootTy =>
    tapes.flatMap fun (_, tape) =>
      let r := Api.replay p 4000 tape hostReplies []
      let decl := fiberDecl (nativeSignature []) p.expandRefs rootTy r.machine
      r.machine.fibers.map fun f =>
        let d := decl f.id
        (f.id.value, d.map (fun t => (t.answer, t.error)),
          match f.exit, d with
          | some ex, some ty => fits ty r.machine.state.externals.allocated ex
          | none, some _ => true
          | _, none => false)

#guard Api.typeOf raceUnder [] = some ⟨.string, .nat, Env.Requirement.empty⟩
#guard (verdicts raceUnder).length = 12
#guard (verdicts raceUnder).all (·.2.2)
#guard (verdicts raceUnder).filterMap (fun (id, d, _) => if id = 1 then d else none) =
  List.replicate 4 (.never, .nat)
#guard (verdicts raceUnder).filterMap (fun (id, d, _) => if id = 2 then d else none) =
  List.replicate 4 (.string, .never)
#guard (verdicts raceSwapped).all (·.2.2)
#guard (verdicts raceSwapped).filterMap (fun (id, d, _) => if id = 1 then d else none) =
  List.replicate 4 (.never, .string)
#guard (verdicts raceSwapped).filterMap (fun (id, d, _) => if id = 2 then d else none) =
  List.replicate 4 (.nat, .never)

/-! ## The daemon view reads live race entrants as unpinned daemons -/

def slowRace : E :=
  .withFiber (.raceAll (es [.bind (.perform .sleep (n 5)) (.succeed (n 1)),
    .bind (.perform .sleep (n 5)) (.succeed (n 2))]))

def parked : Api.Machine := (Api.replay slowRace 2000 [Api.evaluate, Api.flush]).machine

#guard Api.wellTyped slowRace
#guard parked.fibers.map (fun f => (f.id, f.origin)) =
  [(⟨0⟩, .root), (⟨1⟩, .forked ⟨0⟩ true [0, 0]), (⟨2⟩, .forked ⟨0⟩ true [0, 0, 1])]
#guard parked.fibers.all fun f => f.exit.isNone
#guard Api.unpinnedDaemonsAlive parked = [⟨1⟩, ⟨2⟩]
#guard Api.daemonsQuiet parked = false

#eval IO.println "verify-Registry: all guards passed."

end Research.Pass.RegistryVerify.Registry
