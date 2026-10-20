import Lean
import Effect4.Author
import Effect4.Run
import Effect4.Emit
import Effect4.Program.Fold
import Effect4.Data.JsonNorm
import Tools.Code.Module

/-!
# The faces of an outcome: every constructor on the observation's path, witnessed on both runtimes

    lake env lean --run docs/research/2026-10-19-schema-as-the-carrier/probe/Faces.lean OUT PRELUDE

The observation of a run (D1) is a fold: the codec's `wireAlgebra` over `Ty`, then `encodeCause`,
`encodeReason`, `encodeDefect` and `encodeErr` over the cause's sorts, and the interruptor's
`Option`. A fold is complete when every constructor of every sort it dispatches on has a
witness. So the universe of forms is the constructor lists of those sorts, read from the loaded
environment, and the coverage is the union of constructors the cases' exits and exit types hit.
The script writes `OUT/census.txt` with the universe, the witnessed and the missing constructors
of each sort, and it refuses when a `Ty` constructor has no codec-support representative.

For each case it builds the program, runs it on the Lean machine, prints its exit encoded at the
certificate's exit type with the reasons' annotations dropped, and writes the program as Effect
TypeScript at `OUT/<name>.gen.ts`. `OUT/cases.gen.ts` holds each case's exit Schema as a JSON
codec. `run.ts` runs each printed program under Bun and encodes its exit with that codec. -/

set_option autoImplicit false

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Codegen
open Effect4.Store (Val)

namespace Faces

/-- One case: its name, its program, and whether it runs as `runSync`. -/
structure Case where
  name : String
  src : Src NativeOp
  sync : Bool := false

def itemFields : List (String × Bool × Ty) := [("id", false, .nat), ("nick", true, .string), ("title", false, .string)]

/-- The reason `Interrupt` with no interruptor, as a cause. -/
def interruptCause : CauseSrc := fun _ _ => .ok (.interrupt none)

/-- A child that never ends on its own. -/
def sleeping : Src NativeOp := Effect.sleep (nat 1000)

def cases : List Case :=
  [ ⟨"successUnit", succeed unit, false⟩
  , ⟨"successNat", succeed (nat 7), false⟩
  , ⟨"successIntNegative", succeed (Atom.minus (nat 1) (nat 2)), false⟩
  , ⟨"successIntNonNegative", succeed (Atom.minus (nat 3) (nat 1)), false⟩
  , ⟨"successBool", succeed (bool true), false⟩
  , ⟨"successString", succeed (str "λ🙂 \"quoted\" \\ tab\t"), false⟩
  , ⟨"successSome", succeed (Atom.some (nat 3)), false⟩
  , ⟨"successNone", succeed Atom.none, false⟩
  , ⟨"successList", succeed (Atom.cons (nat 1) (Atom.cons (nat 2) Atom.nil)), false⟩
  , ⟨"successPair", succeed (Atom.pair (nat 1) (str "x")), false⟩
  , ⟨"successTuple", succeed (tuple [nat 1, str "a", bool false]), false⟩
  , ⟨"successRecord", succeed (record itemFields [("id", nat 1), ("title", str "milk")]), false⟩
  , ⟨"successRecordOptional", succeed (record itemFields [("id", nat 1), ("nick", str "m"), ("title", str "milk")]), false⟩
  , ⟨"successMap", succeed (Atom.mapSet Atom.mapEmpty (str "k") (nat 1)), false⟩
  , ⟨"successUnion", ifElse (bool true) (succeed (nat 1)) (succeed (str "x")), false⟩
  , ⟨"successExitOfFail", exit (fail (str "inner")), false⟩
  , ⟨"successExitOfSucceed", exit (succeed (nat 1)), false⟩
  , ⟨"successCause", catchCause "c" (fail (str "c")) (succeed (var "c")), false⟩
  , ⟨"failString", fail (str "bad"), false⟩
  , ⟨"failNat", fail (nat 3), false⟩
  , ⟨"failTagged", fail (Atom.pair (str "EmptyTitle") (str "a title is required")), false⟩
  , ⟨"failRecord", fail (record [("_tag", false, .lit "NotFound"), ("id", false, .nat)] [("_tag", str "NotFound"), ("id", nat 7)]), false⟩
  , ⟨"dieNat", Forms.die (nat 7), false⟩
  , ⟨"dieString", Forms.die (str "boom"), false⟩
  , ⟨"interruptNoOne", failCause interruptCause, false⟩
  , ⟨"exitOfInterrupt", exit (failCause interruptCause), false⟩
  , ⟨"forkFailJoin", eff do
      let f ← fork (fail (str "child"))
      join f, false⟩
  , ⟨"forkDieJoin", eff do
      let f ← fork (Forms.die (nat 9))
      join f, false⟩
  , ⟨"forkInterruptJoin", eff do
      let f ← fork sleeping
      let _ ← withFiber (Action.interrupt f)
      join f, false⟩
  , ⟨"forkScopedNoScope", Forms.forkScopedDefault (succeed unit), false⟩
  , ⟨"asyncSleep", sleeping, true⟩
  , ⟨"answerIsFiber", fork (succeed unit), false⟩
  , ⟨"answerIsRef", Ref.make (nat 1), false⟩
  , ⟨"answerIsDeferred", Deferred.make .nat .never, false⟩
  , ⟨"answerIsScope", Scope.make .sequential, false⟩ ]

/-! ## The observation -/

/-- The exit with every reason's annotations dropped: the normaliser of the typed observation.
Effect's JSON codec writes no annotation, so the exact codec admits an exit only without them. -/
def bare : Machine.ExitV → Machine.ExitV
  | .success v => .success v
  | .failure c => .failure ⟨c.reasons.map fun
      | .fail e _ => .fail e .empty
      | .die d _ => .die d .empty
      | .interrupt who _ => .interrupt who .empty⟩

/-- The exit type of a built program. -/
def exitTy (b : Api.Built) : Ty := .exitOf b.ty.answer b.ty.error

/-- A JSON number as text: a natural by its digits, a negative integer by the sign and the
digits of its magnitude, and any other binary64 by Lean's float text. The profile's tree
(`NatJson`) holds naturals only, so the codec's JSON needs its own renderer. -/
def numberText (f : Float64) : String :=
  match Schema.Codec.nat? (.number f) with
  | some n => toString n
  | none =>
    match Schema.Codec.nat? (.number ⟨f.bits ^^^ ((1 : UInt64) <<< 63)⟩) with
    | some n => "-" ++ toString n
    | none => toString (Float.ofBits f.bits)

mutual
/-- The codec's JSON as text, keys as they stand. -/
def jsonText : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .number f => numberText f
  | .str s => String.fromUTF8! ⟨((NatJson.render (.str s)).map (·.toUInt8)).toArray⟩
  | .arr xs => "[" ++ ",".intercalate (jsonTexts xs) ++ "]"
  | .obj entries => "{" ++ ",".intercalate (jsonEntries entries) ++ "}"
def jsonTexts : List Json → List String
  | [] => []
  | x :: xs => jsonText x :: jsonTexts xs
def jsonEntries : List (String × Json) → List String
  | [] => []
  | (k, v) :: rest => (String.fromUTF8! ⟨((NatJson.render (.str k)).map (·.toUInt8)).toArray⟩ ++ ":" ++ jsonText v) :: jsonEntries rest
end

/-- An exit encoded at the built program's exit type, keys in canonical order, as text; `refused`
where the type has no codec (`Codec.isSupported`) or the value no image. -/
def typedJson (b : Api.Built) (exit : Option Machine.ExitV) : String :=
  match exit with
  | none => "no exit"
  | some e =>
    if !Schema.Codec.isSupported (exitTy b) then "refused" else
    match Ty.encode (exitTy b) (Machine.exitImage.toVal (bare e)) with
    | some j => jsonText (Schema.Codec.normJ j)
    | none => "refused"

/-- The exit Schema of a built program as a JSON codec, as TypeScript text. -/
def exitSchemaCode (b : Api.Built) : Except String String := do
  let a ← SchemaCode.ofTy b.ty.answer
  let e ← SchemaCode.ofTy b.ty.error
  let render := TypeScript.Render.expr TypeScript.house0 0
  pure s!"Schema.toCodecJson(Schema.Exit({render a}, {render e}, Schema.Defect()))"

/-! ## The census: the constructors a case's exit and exit type hit -/

/-- The constructor heads of a type, by the generated algebra: one field a constructor, so a
constructor without a field does not compile. -/
def tyHeadsAlgebra : TyAlgebra (fun _ => List String) where
  ty_never := ["never"]
  ty_unit := ["unit"]
  ty_nat := ["nat"]
  ty_int := ["int"]
  ty_string := ["string"]
  ty_bool := ["bool"]
  ty_handle _ := ["handle"]
  ty_option t := "option" :: t
  ty_list t := "list" :: t
  ty_prod a b := "prod" :: a ++ b
  ty_except e a := "except" :: e ++ a
  ty_exitOf a e := "exitOf" :: a ++ e
  ty_causeOf e := "causeOf" :: e
  ty_fiberOf a e := "fiberOf" :: a ++ e
  ty_union a b := "union" :: a ++ b
  ty_lit _ := ["lit"]
  ty_refOf a := "refOf" :: a
  ty_deferredOf a e := "deferredOf" :: a ++ e
  ty_var _ := ["var"]
  ty_unknown := ["unknown"]
  ty_record fields := "record" :: fields.flatMap (·.2.2)
  ty_map k v := "map" :: k ++ v
  ty_tuple items := "tuple" :: items.flatten
  ty_app _ items := "app" :: items.flatten
  ty_null := ["null"]
  ty_undefined := ["undefined"]
  ty_number := ["number"]
  ty_bytes := ["bytes"]
  ty_contextOf _ := ["contextOf"]

def tyHeads (t : Ty) : List String := cata_ty tyHeadsAlgebra t

mutual
/-- The constructor heads of a value. Every constructor has its arm. -/
def valHeads : Val → List String
  | .unit => ["unit"]
  | .bool _ => ["bool"]
  | .nat _ => ["nat"]
  | .str _ => ["str"]
  | .bytes _ => ["bytes"]
  | .list xs => "list" :: valHeadsList xs
  | .pair a b => "pair" :: valHeads a ++ valHeads b
  | .none => ["none"]
  | .some a => "some" :: valHeads a
  | .ctor _ args => "ctor" :: valHeadsList args
  | .ref _ _ => ["ref"]
  | .handle _ _ => ["handle"]
  | .negInt _ => ["negInt"]
  | .float _ => ["float"]
def valHeadsList : List Val → List String
  | [] => []
  | x :: xs => valHeads x ++ valHeadsList xs
end

def errHead : Machine.Err → String
  | .boom => "boom"
  | .tag _ => "tag"
  | .tagged _ _ => "tagged"
  | .text _ => "text"
  | .payload _ => "payload"

def defectHead : Machine.Defect → String
  | .notImplemented => "notImplemented"
  | .asyncFiber => "asyncFiber"
  | .badName => "badName"
  | .missingService => "missingService"
  | .user _ => "user"
  | .error _ => "error"

/-- The heads an exit hits, by sort: `Exit`, `Reason`, `Defect`, `Err`, the interruptor's
`Option`, and the success value's `Val` constructors. -/
def exitHits (e : Machine.ExitV) : List (String × String) :=
  match e with
  | .success v => ("Exit", "success") :: (valHeads v).map ("Val", ·)
  | .failure c => ("Exit", "failure") :: c.reasons.flatMap fun
    | .fail err _ => [("Reason", "fail"), ("Err", errHead err)]
    | .die d _ => [("Reason", "die"), ("Defect", defectHead d)]
    | .interrupt who _ => [("Reason", "interrupt"), ("Option", if who.isSome then "some" else "none")]

/-- One representative type for each `Ty` constructor, for the codec's support judgment. -/
def representatives : List (String × Ty) :=
  [ ("never", .never), ("unit", .unit), ("nat", .nat), ("int", .int), ("string", .string), ("bool", .bool)
  , ("handle", .handle "Scope"), ("option", .option .unit), ("list", .list .unit), ("prod", .prod .unit .unit)
  , ("except", .except .unit .unit), ("exitOf", .exitOf .unit .unit), ("causeOf", .causeOf .unit)
  , ("fiberOf", .fiberOf .unit .unit), ("union", .union .nat .string), ("lit", .lit "a"), ("refOf", .refOf .unit)
  , ("deferredOf", .deferredOf .unit .unit), ("var", .var 0), ("unknown", .unknown), ("record", .record [])
  , ("map", .map .string .unit), ("tuple", .tuple []), ("app", .app "T" []), ("null", .null)
  , ("undefined", .undefined), ("number", .number), ("bytes", .bytes), ("contextOf", .contextOf Row.empty) ]

/-- The sorts the observation's fold dispatches on, with their inductive's name. -/
def sorts : List (String × Lean.Name) :=
  [ ("Ty", `Effect4.Program.Ty), ("Exit", `Effect4.Exit), ("Reason", `Effect4.Reason)
  , ("Defect", `Effect4.Machine.Defect), ("Err", `Effect4.Machine.Err), ("Option", `Option)
  , ("Val", `Effect4.Store.Val) ]

/-- A sort's constructors, by their short names, from the environment. -/
def constructors (env : Lean.Environment) (sort : Lean.Name) : Except String (List String) :=
  match env.find? sort with
  | some (.inductInfo iv) => .ok (iv.ctors.map fun c => (c.toString.splitOn ".").getLast!)
  | some _ => .error s!"{sort} is no inductive"
  | none => .error s!"{sort} is not in the environment"

def dedup (xs : List String) : List String := xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

end Faces

open Faces in
def main (args : List String) : IO UInt32 := do
  let [out, prelude] := args | IO.eprintln "usage: Faces.lean OUT PRELUDE"; return 2
  let out : System.FilePath := out
  IO.FS.createDirAll out
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Effect4.Author }, { module := `Effect4.Run }] {} 0
  let mut manifest : List String := []
  let mut refused : List String := []
  let mut order : List String := []
  let mut types : List String := []
  let mut hits : List (String × String) := []
  let mut witnessedRefusals : List String := []
  for c in cases do
    order := order ++ [c.name]
    match Api.Author.build { main := c.src } with
    | .error _ => IO.println s!"{c.name} BUILD REFUSED"
    | .ok b =>
      let exit : Option Machine.ExitV :=
        if c.sync then some (Api.runSync b.program 100000 b.table).2
        else (Api.run b.program 100000 b.table).exit
      let line := typedJson b exit
      IO.println s!"{c.name} {line}"
      types := types ++ [s!"{c.name}\t{b.ty.answer.render}\t{b.ty.error.render}\t{if c.sync then "runSync" else "run"}"]
      hits := hits ++ (tyHeads (exitTy b)).map ("Ty", ·) ++ (exit.map exitHits).getD []
      if line == "refused" then witnessedRefusals := witnessedRefusals ++ (dedup (tyHeads (exitTy b))).filter fun h =>
        (representatives.find? (·.1 == h)).map (fun r => !Schema.Codec.isSupported r.2) |>.getD false
      match exitSchemaCode b with
      | .ok code => manifest := manifest ++ [s!"  {c.name.quote}: \{ codec: {code}, sync: {c.sync} }"]
      | .error _ => refused := refused ++ [c.name]
      match Api.emitModule "main" b.program b.table with
      | .error why => IO.eprintln s!"{c.name}: the emission refuses: {reprStr why}"
      | .ok emission =>
        match emission.file prelude with
        | .error why => IO.eprintln s!"{c.name}: the file refuses: {reprStr why}"
        | .ok file =>
          IO.FS.writeFile (out / s!"{c.name}.gen.ts")
            (Tools.Code.moduleText Tools.Code.Ts.width { file with header := [s!"faces: {c.name}, written by Faces.lean. Do not edit."] })
  IO.FS.writeFile (out / "cases.gen.ts")
    ("// Each case's exit Schema as a JSON codec, written by Faces.lean. Do not edit.\nimport { Schema } from \"effect\"\n" ++
      "export const order = [" ++ ", ".intercalate (order.map String.quote) ++ "]\n" ++
      "export const refused = [" ++ ", ".intercalate (refused.map String.quote) ++ "]\n" ++
      "export const cases: Record<string, { codec: unknown; sync: boolean }> = {\n" ++ ",\n".intercalate manifest ++ "\n}\n")
  IO.FS.writeFile (out / "types.tsv") ("\n".intercalate types ++ "\n")
  -- the census
  let mut census : List String := []
  let mut drift := false
  for (sort, name) in sorts do
    match constructors env name with
    | .error why => census := census ++ [s!"{sort}: {why}"]; drift := true
    | .ok ctors =>
      let witnessed := dedup ((hits.filter (·.1 == sort)).map (·.2))
      let missing := ctors.filter (!witnessed.contains ·)
      census := census ++ [s!"{sort}: {ctors.length} constructors: {", ".intercalate ctors}",
        s!"  witnessed {witnessed.length}: {", ".intercalate witnessed}",
        s!"  missing {missing.length}: {", ".intercalate missing}"]
      if sort == "Ty" then
        let supported := ctors.filter fun h => (representatives.find? (·.1 == h)).map (fun r => Schema.Codec.isSupported r.2) |>.getD false
        let refusedHeads := ctors.filter (!supported.contains ·)
        let noRep := ctors.filter fun h => (representatives.find? (·.1 == h)).isNone
        if !noRep.isEmpty then drift := true
        census := census ++ [s!"  codec supports {supported.length}: {", ".intercalate supported}",
          s!"  codec refuses {refusedHeads.length}: {", ".intercalate refusedHeads}",
          s!"  refusals witnessed {(dedup witnessedRefusals).length}: {", ".intercalate (dedup witnessedRefusals)}",
          s!"  without a representative {noRep.length}: {", ".intercalate noRep}"]
  let total := (sorts.filterMap fun (_, name) => (constructors env name).toOption).map List.length |>.foldl (· + ·) 0
  census := census ++ [s!"universe: {total} constructors over {sorts.length} sorts; cases: {cases.length}"]
  IO.FS.writeFile (out / "census.txt") ("\n".intercalate census ++ "\n")
  IO.println ("\n".intercalate census)
  return (if drift then 3 else 0)
