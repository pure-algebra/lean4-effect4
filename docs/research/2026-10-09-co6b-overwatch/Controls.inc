
-- Positive and negative controls use independent choices of exported names and behavior.
def definitions (other : String := "T") (methodName : String := "get") : List DefDecl :=
  [{ name := "mkS", request := .unit, answer := .nat, role := .serviceInit "S" },
   { name := "readS", request := .nat, answer := .nat, role := .serviceMethod "S" methodName 0 },
   { name := "mkT", request := .unit, answer := .nat, role := .serviceInit other },
   { name := "readT", request := .nat, answer := .nat, role := .serviceMethod other "get" 0 }]

#guard serviceFault (definitions "T") = none
#guard serviceNamesFault [] "main" (definitions "T") = none
#guard (printServices nativeSignature (definitions "T")).map (List.map (·.name)) =
  .ok ["S", "SLayer", "T", "TLayer"]

-- The negative name case passes the same guards but emits SLayer twice.
#guard serviceFault (definitions "SLayer") = none
#guard serviceNamesFault [] "main" (definitions "SLayer") = none
#guard (printServices nativeSignature (definitions "SLayer")).map (List.map (·.name)) =
  .ok ["S", "SLayer", "SLayer", "SLayerLayer"]

-- Invalid method spelling is accepted by both service guards.
#guard serviceFault (definitions "T" "bad-name") = none
#guard serviceNamesFault [] "main" (definitions "T" "bad-name") = none
#guard (printServices nativeSignature (definitions "T" "bad-name")).isOk

-- The layer name is not checked against row spellings.
def hostRow : Row :=
  { name := "host", spelling := "SLayer", kind := .program,
    request := .unit, answer := .nat, error := .never, cite := "review fixture" }
#guard serviceNamesFault [hostRow] "main" (definitions "T") = none
#guard serviceNamesFault [{ hostRow with spelling := "S" }] "main" (definitions "T") = some "S"

-- The reader ignores the actual method argument. Both source forms give identical metadata.
#guard readServiceMethod ("get", .lambda [] (.call (.ident "readS") [.ident "a0"])) =
  some ("get", "readS", 0)
#guard readServiceMethod ("get", .lambda [] (.call (.ident "readS") [.int 99])) =
  some ("get", "readS", 0)

-- Mutate exactly the captured-state argument in a generated layer.
def changeRequest (c : TypeScript.ConstDecl) : TypeScript.ConstDecl :=
  if c.name ≠ "SLayer" then c else
  match c.value with
  | .call (.ident "Layer.effect") [.ident s, .call (.ident "Effect.map")
      [initial, .arrowBlock params [.ret (.object [(m, .lambda ps (.call (.ident d) [_]) none)])] none]] =>
    { c with value := .call (.ident "Layer.effect") [.ident s, .call (.ident "Effect.map")
      [initial, .arrowBlock params [.ret (.object [(m, .lambda ps (.call (.ident d) [.int 99]))])]]] }
  | _ => c

#guard match printServices nativeSignature (definitions "T") with
  | .error _ => false
  | .ok cs => (cs.map changeRequest).filterMap readServiceLayer == cs.filterMap readServiceLayer
#guard match printServices nativeSignature (definitions "T") with
  | .error _ => false
  | .ok cs => (cs.map changeRequest) != cs

-- Repair candidates stay in this isolated probe. They are not production changes.
namespace RepairCandidates

def serviceNamesFree (taken : List String) (cs : List TypeScript.ConstDecl) : Bool :=
  decide (cs.map (·.name)).Nodup && cs.all (fun c => !taken.contains c.name)

def readImageAgrees (defs : List DefDecl) (cs : List TypeScript.ConstDecl) : Bool :=
  match printServices nativeSignature defs with
  | .error _ => false
  | .ok expected => cs == expected

-- Reuse the existing record key policy; add no new string escaping rules.
def quoteMethods (c : TypeScript.ConstDecl) : TypeScript.ConstDecl :=
  match c.value with
  | .call (.ident "Layer.effect") [key, .call (.ident "Effect.map")
      [initial, .arrowBlock params [.ret (.object closures)] none]] =>
    { c with value := .call (.ident "Layer.effect") [key, .call (.ident "Effect.map")
      [initial, .arrowBlock params [.ret (.objectWith
        (Effect4.Codegen.Record.keyForm (closures.map (·.1)))
        (closures.map fun (name, body) => .property name body))]]] }
  | _ => c

#guard match printServices nativeSignature (definitions "T") with
  | .error _ => false
  | .ok cs => serviceNamesFree [] cs && !serviceNamesFree ["SLayer"] cs
#guard match printServices nativeSignature (definitions "SLayer") with
  | .error _ => false
  | .ok cs => !serviceNamesFree [] cs
#guard match printServices nativeSignature (definitions "T") with
  | .error _ => false
  | .ok cs => readImageAgrees (definitions "T") cs &&
      !readImageAgrees (definitions "T") (cs.map changeRequest)

end RepairCandidates

end Co6bProbe

open Co6bProbe

def main : IO Unit := do
  let prelude := "import { Context, Effect, Layer } from \"effect\"\n" ++
    "const mkS = (_a0: void): Effect.Effect<number, never, never> => Effect.succeed(1)\n" ++
    "const readS = (a0: number): Effect.Effect<number, never, never> => Effect.succeed(a0)\n" ++
    "const mkT = (_a0: void): Effect.Effect<number, never, never> => Effect.succeed(2)\n" ++
    "const readT = (a0: number): Effect.Effect<number, never, never> => Effect.succeed(a0)\n"
  for (file, defs, mutate, repairKeys) in [
      ("positive.ts", definitions "T", false, false),
      ("collision.ts", definitions "SLayer", false, false),
      ("method-name.ts", definitions "T" "bad-name", false, false),
      ("changed-request.ts", definitions "T", true, false),
      ("method-name-repaired.ts", definitions "T" "bad-name", false, true),
      ("prototype-name-repaired.ts", definitions "T" "__proto__", false, true)] do
    match printServices Effect4.Program.nativeSignature defs with
    | .error _ => throw (IO.userError "unexpected service printer refusal")
    | .ok cs =>
      let cs := if mutate then cs.map changeRequest else cs
      let cs := if repairKeys then cs.map RepairCandidates.quoteMethods else cs
      IO.FS.writeFile ("docs/research/2026-10-09-co6b-overwatch/" ++ file)
        (prelude ++ String.intercalate "\n" (cs.map (TypeScript.Render.constDecl TypeScript.house0)))
  IO.println "PASS: positive, collision, method-name, row-name and changed-request controls"
