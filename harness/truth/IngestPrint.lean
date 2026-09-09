import Tools.GeneratedStamp
import Effect4.Api
import TypeScript.Render
import Lean.Data.Json

/-! Decode the existing program wire and ask the application API for its type and
printed declaration. Input is one lowercase hexadecimal program per line; output
is one JSON observation per line. No source recognition or JSON parser lives here. -/

private def nibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

private def bytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← nibble a
    let lo ← nibble b
    let tail ← bytes rest
    pure (UInt8.ofNat (hi * 16 + lo) :: tail)
  | [_] => none

private def observe (hex : String) : Lean.Json := Id.run do
  let some raw := bytes hex.toList | return Lean.Json.mkObj [("error", "invalid hex")]
  let some p := Effect4.Api.ofBytes raw | return Lean.Json.mkObj [("error", "wire decode refused")]
  let ty := Effect4.Api.typeOf p
  let decl := Effect4.Api.printDecl "main" p
  return Lean.Json.mkObj
    [ ("wireHex", Lean.Json.str hex)
    , ("wellTyped", Lean.Json.bool ty.isSome)
    , ("requiresEmpty", match ty with
        | some t => Lean.Json.bool (decide (t.requires = Effect4.Machine.Env.Requirement.empty))
        | none => Lean.Json.null)
    , ("decl", match decl with
        | some d => Lean.Json.str (TypeScript.Render.constDecl TypeScript.house0 d)
        | none => Lean.Json.null) ]

def main (args : List String) : IO Unit := do
  let [input, output] := args | throw (IO.userError "IngestPrint INPUT OUTPUT")
  let lines ← IO.FS.lines input
  let out ← IO.FS.Handle.mk output IO.FS.Mode.write
  for line in lines do
    unless line.isEmpty do out.putStrLn (observe line).compress
  let stamp ← Tools.GeneratedStamp.line "harness/truth/IngestPrint.lean" []
    [input, "harness/truth/run-truth.ts", "harness/truth/prelude.ts", "ts/eff/package.json", "ts/eff/bun.lock"]
  Tools.GeneratedStamp.sidecar output stamp
