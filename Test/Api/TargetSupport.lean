import Effect4.Api.Codegen

/-! # The certified faces' target-support decision

Controls of `Api.targetSupport`, the decision `Typed.print`, `Typed.emit` and `Built.print` take
before they print at the rows' signature (`src/Effect4/Api/Codegen.lean`). The red case is the
proof scout's `rebound`, and the known cost is the final review's `unusedDeclarations`
(`docs/research/2026-10-17-proof-scout/README.md`, §7.1, controls 5 and 6). Each line is a control
or a finite evaluation. -/

namespace Effect4.Test.TargetSupport

open Effect4 Effect4.Program

/-- Built-in service code 4, whose built-in carrier is `nat`. -/
def key4 : ServiceKey := ⟨⟨127⟩, ⟨4⟩⟩

/-- An application that redeclares code 4 at `string`. -/
def rebound : SigApp := { services := [(key4, .string)] }

-- Why the decision stands: the certificate types the service at `string`, and the rows'
-- signature, which the faces print at, types it at `nat`.
#guard (Api.check (.service key4) rebound).toOption.map (·.ty.answer) = some .string
#guard (Api.check (.service key4) (SigApp.ofTable rebound.rows)).toOption.map (·.ty.answer) =
  some .nat

-- Control 5: the certified faces refuse that application at the root, before printing.
#guard match Api.check (.service key4) rebound with
  | .ok t => match t.emit "main" with
    | .error (.print (.declarations 1 0)) => true
    | _ => false
  | .error _ => false
#guard match Api.check (.service key4) rebound with
  | .ok t => match t.print with
    | .error (.declarations 1 0) => true
    | _ => false
  | .error _ => false

/-- A program that reads no service. -/
def one : NativeEff := .succeed (.lit (.nat 1))

/-- A service the program never reads, at a code with no built-in carrier. -/
def unused : SigApp := { services := [(⟨⟨127⟩, ⟨127⟩⟩, .string)] }

-- Control 6, the decision's known cost: the declaration changes no type, and is refused anyway.
#guard (Api.check one unused).toOption.map (·.ty) =
  (Api.check one (SigApp.ofTable unused.rows)).toOption.map (·.ty)
#guard match Api.check one unused with
  | .ok t => match t.emit "main" with
    | .error (.print (.declarations 1 0)) => true
    | _ => false
  | .error _ => false

/-- An application that declares one named type. -/
def named : SigApp := { types := [("Todo", .nat)] }

-- A named type is refused by `Built.print` too, through the built program's certificate.
#guard match admitProgram one named with
  | .ok admitted => match (⟨named, one, admitted⟩ : Api.Built).print with
    | .error (.declarations 0 1) => true
    | _ => false
  | .error _ => false

-- Readers: an application that declares nothing prints and emits.
#guard match Api.check one {} with
  | .ok t => t.print.isOk && (t.emit "main").isOk
  | .error _ => false

end Effect4.Test.TargetSupport
