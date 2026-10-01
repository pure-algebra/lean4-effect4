import Effect4.Laws.Program.Typed.Assembly

/-! Verifier scouting (no claims): the denoted root of the corpus's `awaitFiber.value` program. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
namespace VerifyScout5
def n (i : Nat) : Term := .lit (.nat i)
def v (i : Nat) : Term := .var i
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def forked : NativeEff := .withFiber (.fork (.succeed (n 1)) opts)
def awaitProg : NativeEff := .bind forked (.awaitFiber (v 0) .awaitValue)

def desc : RProgram → String
  | .pure _ => "pure"
  | .vis (.inl _) _ => "store"
  | .vis (.inr op) _ => match op with
    | .fork b _ _ => match b with
      | .at_ p => s!"fork at_ path={p.path} env={p.env.length} completed={p.completed.length}"
      | _ => "fork other-body"
    | .await t .awaitValue => s!"await-value target={t.value}"
    | .await _ _ => "await-join"
    | .guard_ k => match k with | .onSuccess => "guard onSuccess" | _ => "guard other"
    | .suspend _ => "suspend" | .construction => "construction" | .sync _ => "sync"
    | .getContext => "getContext" | .setContext _ => "setContext" | .mask _ _ => "mask"
    | .yieldNow _ => "yieldNow" | .frontier _ _ => "frontier" | .scoped _ => "scoped"
    | .getId => "getId" | .ambientScope => "ambientScope" | _ => "fiber-other"

def root : RProgram := denoteR awaitProg awaitProg (rootPoint 5)
#eval desc root
def guardBody : RProgram → Option RProgram
  | .vis (.inr (.guard_ _)) k => some (k none)
  | _ => none
def guardRun (ex : ExitV) : RProgram → Option RProgram
  | .vis (.inr (.guard_ _)) k => some (k (some ex))
  | _ => none
#eval (guardBody root).map desc
#eval (guardRun (.success (Val.fiber ⟨1⟩)) root).map desc
-- the fork's continuation on the handle
def forkNext (ans : Val) : RProgram → Option RProgram
  | .vis (.inr (.fork _ _ _)) k => some (k ans)
  | _ => none
#eval ((guardBody root).bind (forkNext (Val.fiber ⟨1⟩))).map desc
-- the await's continuation on a value
def awaitNext (ans : Val) : RProgram → Option RProgram
  | .vis (.inr (.await _ .awaitValue)) k => some (k ans)
  | _ => none
#eval ((guardRun (.success (Val.fiber ⟨1⟩)) root).bind (awaitNext (Val.nat 5))).map desc
#eval match Checker.check (nativeSignature []) [] [0, 0, 0] (Eff.succeed (n 1)) with
  | .ok t => decide (t = EffTy.pure .nat) | .error _ => false
#eval match Node.at_ (.eff awaitProg) [0, 0, 0] with
  | some (.eff e) => decide (e = Eff.succeed (n 1)) | _ => false
-- construction's continuation on the empty completed list
def consNext (l : List (FiberId × ExitV)) : RProgram → Option RProgram
  | .vis (.inr .construction) k => some (k l)
  | _ => none
#eval ((guardRun (.success (Val.fiber ⟨1⟩)) root).bind (consNext [])).map desc
#eval (((guardRun (.success (Val.fiber ⟨1⟩)) root).bind (consNext [])).bind (awaitNext (Val.nat 5))).map desc
-- the sync-like op after the fork
def anyNext (ans : Val) : RProgram → Option RProgram
  | .vis (.inr (.sync _)) k => some (k ans)
  | _ => none
#eval (((guardBody root).bind (forkNext (Val.fiber ⟨1⟩))).bind (anyNext (Val.fiber ⟨1⟩))).map desc
end VerifyScout5
