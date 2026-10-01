import Effect4.Api
import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.Residual
open Effect4 Effect4.Machine Effect4.Program
namespace AdversarialReview

def n (k : Nat) : Term := .lit (.nat k)
def fail (k : Nat) : NativeEff := .fail (n k)
def race : NativeEff := .withFiber (.raceAll (.cons (fail 1) (.cons (fail 2) .nil)))
def countExit (ex : Option ExitV) : Nat :=
  match ex with | some (.failure c) => failCount c | _ => 0
#guard Api.wellTyped race
#guard countExit (Api.run race 300).exit = 2
-- The proposed A1 race rule ORs two false children, but the actual failure has two reasons.
#guard countExit (Api.run (fail 1) 100).exit = 1
#guard countExit (Api.run (fail 2) 100).exit = 1

def combined : NativeEff := .failCause (.both (.fail (n 1)) (.fail (n 2)))
def finalizer : NativeEff := .onExit (fail 1) (fail 2)
#guard Denote.Straight combined
#guard Denote.Straight finalizer
#guard countExit (Api.run combined 100).exit = 2
#guard countExit (Api.run finalizer 100).exit = 2

def row : Row :=
  { name := "probe", spelling := "Host.probe", kind := .async, registration := .external,
    request := .nat, answer := .nat, error := .nat, cite := "" }
def program : NativeEff := .perform (.external 0) (n 0)
def table : RowTable := [row]
def parked := (Api.run program 200 [] table).machine
def two : Completion Val Err Defect FiberId Ann :=
  .ofExit (.failure ⟨[.fail (errOf (.nat 1)) .empty, .fail (errOf (.nat 2)) .empty]⟩)
#guard (awaits parked).length = 1
#guard admitAnswer row parked ⟨0⟩ 0 two = none

def reply : Option RecordedReply := do
  let (fiber, token, op, request) ← (awaits parked).head?
  pure ⟨table, fiber, token, op, request, two⟩
#guard reply.isSome
#guard match reply with
  | some r => (acceptReply table parked r).isSome
  | none => false

-- Broad products and list aliases invalidate unrestricted tag-based payload selection.
def tagged : Ty := .prod (.lit "A") .nat
def textPair : Val := .list [.str "A", .str "oops"]
#guard Val.hasTy textPair (.union tagged (.prod .string .string))
#guard Val.hasTy textPair (.union tagged (.list .string))
#guard !Val.hasTy textPair tagged
#guard NativeAtom.tagHit "A" textPair

-- An unrestricted annotation parser cannot recover these distinct raw types.
#guard Ty.renderRaw .nat = Ty.renderRaw .int
#guard Ty.renderRaw (.handle "Option.Option<number>") = Ty.renderRaw (.option .nat)
#guard Ty.renderRaw (.lit "A\"B") = "\"A\"B\""
end AdversarialReview
