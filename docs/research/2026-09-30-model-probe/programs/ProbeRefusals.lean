import Effect4.Api.Author

/-! Seat PROGRAMS (2026-09-30), probe 1 of 3: where the five programs meet the checked language
today, one guard per construct. Each refusal is the language as it is at HEAD, located by the
build's own refusal; each acceptance is the nearest spelling that types. Scratch, not in the
tree. Compiled through the one-compiler lock with `-DwarningAsError=true`. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Probe.Refusals
open Effect4 Effect4.Program Effect4.Program.Authoring
open Effect4.Api (BuildRefusal)

/-- The build's verdict, as a short word, so a guard reads the refusal kind. -/
def verdict (m : Module NativeOp) : String :=
  match Effect4.Api.Author.build m with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ none) => "serviceCarrier: signature none"
  | .error (.serviceCarrier _ _ (some _)) => "serviceCarrier: signature disagrees"

def program (src : Src NativeOp) : Module NativeOp := { main := src }

/-! ## Cells hold numbers only (R4; decisions rows 42-43 steps 3-5 open) -/

-- p4's and p5's state as a pair in one cell: refused at the request.
#guard verdict (program (Ref.make (app "pair" [nat 1, nat 2]))) = "typing: requestNotSubtype"
-- a string in a cell (p5's account id): refused.
#guard verdict (program (Ref.make (str "acc-1"))) = "typing: requestNotSubtype"
-- a list in a cell (p3's queue buffer, p5's listener list): refused.
#guard verdict (program (Ref.make (app "cons" [nat 1, app "nil" []]))) = "typing: requestNotSubtype"
-- the number cell types.
#guard verdict (program (Ref.make (nat 0))) = "built"

/-! ## Typed failures carry strings only (R3 error payloads; DESIGN-BASIS refuses `Err.value`) -/

-- p2's `NotFound{id}` with a number payload: refused at `fail`.
#guard verdict (program (fail (app "pair" [str "NotFound", nat 7]))) = "typing: errorNotAdmitted"
-- p5's `InsufficientFunds{needed, available}` as nested pairs: refused.
#guard verdict (program (fail (app "pair" [str "InsufficientFunds", app "pair" [nat 25, nat 10]])))
  = "typing: errorNotAdmitted"
-- the tag with a string message types (`Err.tagged`).
#guard verdict (program (fail (app "pair" [str "NotFound", str "7"]))) = "built"

/-! ## Service carriers: six type codes, no string, no record, no code (R1, R5; row 21) -/

/-- p2's `AppConfig` reduced to its token: a string carrier under a free name. -/
def AdminToken : ServiceDef := { key := ⟨⟨12⟩, ⟨12⟩⟩, carrier := .string }

#guard verdict
    { services := [AdminToken]
      layers := [("cfg", AdminToken.constant (str "secret"))]
      main := provide (Layer.ref "cfg") AdminToken.use } = "serviceCarrier: signature none"

/-- p2's `UserRepo` with the SQL client it captured as its carrier: type code 8 under a free
name. This is the builder route's carrier: the handle is data, the methods are Lean functions. -/
def UserRepo : ServiceDef := { key := ⟨⟨13⟩, ⟨8⟩⟩, carrier := NativeOp.sqlTy }

#guard ServiceDef.Agrees (nativeSignature) UserRepo

/-- p2's `CurrentUser` reduced to the user's id: a number carrier. -/
def CurrentUserId : ServiceDef := { key := ⟨⟨14⟩, ⟨4⟩⟩, carrier := .nat }

#guard ServiceDef.Agrees (nativeSignature) CurrentUserId

-- The auth middleware as a requirement transformer (provision algebra §5): the handler needs
-- `CurrentUserId`; `give` discharges it and the program needs nothing.
#guard verdict (program (CurrentUserId.give (nat 1) (bindName "me" CurrentUserId.use fun me =>
    succeed me))) = "built"

/-! ## The authoring surface admits no binder-carrying update (R4/R7; row 43 step 3 open) -/

-- `Ref.update` takes one of five named functions (`Machine/Stores.lean:61-72`); p4's admit step
-- `w => w.used < limit ? … : …` and p5's transition have no spelling. The nearest: `incr`.
#guard verdict (program (bindName "r" (Ref.make (nat 0)) fun r => Ref.update .incr r)) = "built"

end Probe.Refusals
