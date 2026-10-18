import Effect4.Tool.Wire
import Effect4.Laws.Tool.CodecProfile

/-!
# Test.Program.SeamsS3bWire — the tool's JSON profile, codecs and wire adapter (seams S3b)

Finite controls. The JSON profile refuses `Option Unit` and a rounded natural, and keeps an
ordinary one. The Check codecs refuse unknown tags and missing fields. The wire adapter decodes a
request at the selected version and refuses an unselected method, a wrong version, a method that
disagrees with its payload, a malformed message and an invalid connection; each refusal leaves the
state as it was. An accepted request through `serveJson` appends one action.
-/

set_option autoImplicit false
namespace Test.Program.SeamsS3bWire
open Effect4 Effect4.Program Effect4.Program.Check Effect4.Store Effect4.Tool
open Effect4.Tool.Wire (Envelope Connection decode serveJson)

/-! ## The JSON profile -/

#guard CodecProfile.supports (Canonical.shape (Option Unit)) = false
#guard match CodecProfile.write (some () : Option Unit) with
  | .error .unsupportedProfile => true | _ => false
#guard match CodecProfile.read (α := Option Unit) .null with
  | .error .unsupportedProfile => true | _ => false
-- A natural that a JSON number would round refuses rather than change.
#guard match CodecProfile.write (9007199254740993 : Nat) with
  | .error .unprintable => true | _ => false
#guard match CodecProfile.write (7 : Nat) with
  | .ok j => (CodecProfile.read (α := Nat) j).toOption = some 7 | _ => false

/-! ## The Check codecs -/

def program : NativeEff := .succeed (.lit (.nat 7))
def input : CheckInput := .module {} [] program
#guard Canonical.ofVal (Canonical.toVal input) = some input
#guard Canonical.ofVal (α := CheckInput) (.ctor 99 []) = none
#guard Canonical.ofVal (α := CheckInput) (.ctor 0 []) = none
#guard match CodecProfile.write input with
  | .ok j => (CodecProfile.read (α := CheckInput) j).toOption = some input
  | .error _ => false

/-! ## The wire adapter -/

def openRequest : Request := .act (.open_ "wire" {} ⟨program, []⟩)
def framed (method : String) (version : Nat) (payload : Request) : Effect4.Json :=
  match CodecProfile.write (⟨method, version, payload⟩ : Envelope Request) with
  | .ok j => j
  | .error _ => .null

-- A request reads back at the selected version.
#guard match decode Connection.v1 (framed "open" 1 openRequest) with
  | .ok envelope => envelope.method == "open" && envelope.version == 1
  | .error _ => false
-- An unselected method, a wrong version and a disagreeing method refuse.
#guard match decode ⟨[]⟩ (framed "open" 1 openRequest) with
  | .error (.unselected "open") => true | _ => false
#guard match decode Connection.v1 (framed "open" 2 openRequest) with
  | .error (.version "open" 1 2) => true | _ => false
#guard match decode Connection.v1 (framed "edit" 1 openRequest) with
  | .error (.method "edit" "open") => true | _ => false
-- A message that is not an envelope, and a connection that selects one method twice, refuse.
#guard match decode Connection.v1 (.str "open") with
  | .error (.codec .unreadable) => true | _ => false
#guard match decode ⟨[("open", 1), ("open", 1)]⟩ (framed "open" 1 openRequest) with
  | .error .connection => true | _ => false

-- An accepted request appends one action; a refused message leaves the state.
def served := (serveJson Oracle.uncached Connection.v1 empty (framed "open" 1 openRequest)).value
#guard served.1.transcript.length = 1
#guard served.2.toOption.isSome
def refused := (serveJson Oracle.uncached ⟨[]⟩ empty (framed "open" 1 openRequest)).value
#guard refused.1.transcript.isEmpty
#guard refused.2.toOption.isNone

end Test.Program.SeamsS3bWire
