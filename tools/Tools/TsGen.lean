import Lean
import OCaml5.Eff.World
import Effect4.Program.Native
import Effect4.Codegen.Profile
import Effect4.Codegen.Read

/-!
# Tools.TsGen — the TypeScript estate's generated files, from the Lean environment

    lake env lean -M4096 --run tools/Tools/TsGen.lean ts/eff

Writes three files, all `GENERATED`, none ever edited:

* `eff.gen.ts` — one Effect Schema per family of the closed world `OCaml5.Eff.World.blocks`
  reads off the environment (the same world `ocaml/eff` is generated from): `Schema.TaggedUnion`
  for an inductive, `Schema.Struct` for a structure, `Schema.Literals` for an all-nullary
  inductive, a hand-shaped `type` beside each recursive one; constructor and field names
  verbatim, constructors in declaration order.
* `json.gen.ts` — one JSON writer per family: the bytes `OCaml5.Eff.Goldens.V.json` writes and
  `ocaml/eff/eff_json.ml` prints (`["ctor", field, …]`, structures as objects, options as the
  value or `null`, the cons-list families as `["cons", head, tail]`).
* `profile.gen.ts` — the image profile of `Effect4.Api.print` as one JSON payload decoded at
  import through the schemas of `eff.gen.ts`: the address (`hostPin.libraries` plus the
  `typescript` revision read out of `lakefile.toml`), the reserved heads
  (`Effect4.Program.reserved`, cross-checked against every `.ident "…"` literal of
  `Print.lean`), and one entry per `NativeOp` value — the operation as a `NativeOp` node and
  its `Row` as a `Row` node. No row type is written by hand: `Row`, `Ty`, `NativeOp` are
  families like any other. A stamp (FNV-1a 64 over the payload bytes) is recomputed at import.

Two carrier rules, stated in the generated headers and nowhere else: a family whose
constructors are exactly `nil` and `cons head tail` is `ReadonlyArray<head>`, and a family
whose constructors are all nullary is a union of string literals. `Nat` is `number`, `Option`
is `| null`, `List` is `ReadonlyArray`.

The enumerations behind the profile are checked, not asserted: `run_cmd` reads the three
inductives out of the environment and refuses if their constructor lists moved. A value
printer here that disagrees with a generated schema fails the decode at import, loudly.

`scripts/generate-ts-eff.sh` runs this; `scripts/check-ts-eff.sh` is the stamped drift gate
over the three files, in the sweep. A tool (`IO`, `Lean.Meta`; `lakefile.toml`, the `Tools`
library): outside the axiom gate, imported by nothing.
-/

open Lean Meta OCaml5.Eff

namespace Tools.TsGen

/-! ## Text -/

/-- A string literal valid as TypeScript and as JSON: `\`, `"` and newline escaped. -/
def lit (s : String) : String :=
  let escaped := s.toList.foldl (fun acc c =>
    acc ++ (if c == '\\' then "\\\\" else if c == '"' then "\\\"" else
            if c == '\n' then "\\n" else String.singleton c)) ""
  "\"" ++ escaped ++ "\""

def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

def hex (n : UInt64) : String :=
  let digits : List Char := "0123456789abcdef".toList
  let rec go (fuel : Nat) (v : Nat) (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if v == 0 then acc
      else go fuel (v / 16) (String.singleton (digits.getD (v % 16) '0') ++ acc)
  if n == 0 then "0x0" else "0x" ++ go 32 n.toNat ""

def lowerFirst (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toLower :: cs)
  | [] => s

/-! ## The families -/

/-- How a family is carried in TypeScript. -/
inductive Kind
  /-- All constructors nullary: a union of string literals. -/
  | enum
  /-- A Lean structure: a `Schema.Struct` with the field names. -/
  | struct
  /-- Exactly `nil` and `cons head tail`: `ReadonlyArray<head>`, no declaration of its own. -/
  | consList (elem : OTy)
  /-- Everything else: a `Schema.TaggedUnion` with the constructor names as `_tag`. -/
  | tagged

def kindOf (f : Family) : Kind :=
  if f.isStruct then .struct
  else if f.ctors.all (·.args.isEmpty) then .enum
  else match f.ctors with
    | [nil, cons] =>
      match nil.short, nil.args, cons.short, cons.args with
      | "nil", [], "cons", [(_, elem), (_, .named self)] =>
        if self == f.spec.oname then .consList elem else .tagged
      | _, _, _, _ => .tagged
    | _ => .tagged

/-- The TypeScript name: the Lean short name (`Effect4.Program.CauseTerm` → `CauseTerm`). -/
def tsName (f : Family) : String := shortName f.spec.leanName

/-- The JSON writer of a family: `effJson`, `termJson`, … -/
def jsonFn (f : Family) : String := lowerFirst (tsName f) ++ "Json"

def familyOf (fs : List Family) (oname : String) : Option Family := fs.find? (·.spec.oname == oname)

partial def namedIn : OTy → List String
  | .named o => [o]
  | .option a | .list a => namedIn a
  | .prod a b => namedIn a ++ namedIn b
  | _ => []

partial def tsTy (fs : List Family) : OTy → String
  | .int => "number"
  | .bool => "boolean"
  | .string => "string"
  | .unit => "null"
  | .option a => tsTy fs a ++ " | null"
  | .list a => "ReadonlyArray<" ++ tsTy fs a ++ ">"
  | .prod a b => "readonly [" ++ tsTy fs a ++ ", " ++ tsTy fs b ++ "]"
  | .named o =>
    match familyOf fs o with
    | some f =>
      match kindOf f with
      | .consList elem => "ReadonlyArray<" ++ tsTy fs elem ++ ">"
      | _ => tsName f
    | none => "never"

/-- The schema of a carrier. A reference to a tagged family is suspended: the families are
mutually recursive and the schema constants are declared in dependency order. -/
partial def tsSchema (fs : List Family) : OTy → String
  | .int => "Schema.Int"
  | .bool => "Schema.Boolean"
  | .string => "Schema.String"
  | .unit => "Schema.Null"
  | .option a => "Schema.NullOr(" ++ tsSchema fs a ++ ")"
  | .list a => "Schema.Array(" ++ tsSchema fs a ++ ")"
  | .prod a b => "Schema.Tuple([" ++ tsSchema fs a ++ ", " ++ tsSchema fs b ++ "])"
  | .named o =>
    match familyOf fs o with
    | some f =>
      match kindOf f with
      | .consList elem => "Schema.Array(" ++ tsSchema fs elem ++ ")"
      | .tagged => "Schema.suspend((): Schema.Codec<" ++ tsName f ++ "> => " ++ tsName f ++ ")"
      | _ => tsName f
    | none => "Schema.Never"

def emitFamilySchema (fs : List Family) (f : Family) : String :=
  let name := tsName f
  match kindOf f with
  | .enum =>
    s!"export const {name} = Schema.Literals([{", ".intercalate (f.ctors.map fun c => lit c.short)}])\n" ++
    s!"export type {name} = typeof {name}.Type\n"
  | .struct =>
    let c := f.ctors.head!
    let fields := c.args.map fun (nm, t) => s!"  {nm}: {tsSchema fs t},"
    s!"export const {name} = Schema.Struct(\{\n" ++ "\n".intercalate fields ++ "\n})\n" ++
    s!"export type {name} = typeof {name}.Type\n"
  | .consList elem =>
    s!"// {name}: the cons-list of {tsTy fs elem}, carried as ReadonlyArray<{tsTy fs elem}>.\n"
  | .tagged =>
    let arms := f.ctors.map fun c =>
      let fields := c.args.map fun (nm, t) => s!"; readonly {nm}: {tsTy fs t}"
      s!"  | \{ readonly _tag: {lit c.short}{String.join fields} }"
    let cases := f.ctors.map fun c =>
      let fields := c.args.map fun (nm, t) => s!"{nm}: {tsSchema fs t}"
      s!"  {c.short}: \{{if fields.isEmpty then "" else " " ++ ", ".intercalate fields ++ " "}},"
    s!"export type {name} =\n" ++ "\n".intercalate arms ++ "\n\n" ++
    s!"export const {name} = Schema.TaggedUnion(\{\n" ++ "\n".intercalate cases ++ "\n})\n"

def familyLine (fs : List Family) (f : Family) : String :=
  let shape := match kindOf f with
    | .enum => "literals"
    | .struct => "struct"
    | .consList elem => s!"ReadonlyArray<{tsTy fs elem}>"
    | .tagged => "tagged union"
  s!"//   {tsName f} ({f.spec.leanName}, {shape}): " ++
    " ".intercalate (f.ctors.map fun c =>
      if c.args.isEmpty then c.short
      else c.short ++ "(" ++ ", ".intercalate (c.args.map fun (nm, t) => nm ++ ": " ++ tsTy fs t) ++ ")")

def header (what : String) : String :=
  "// GENERATED by tools/Tools/TsGen.lean from the Lean environment — do not edit.\n" ++
  "// Regenerate: scripts/generate-ts-eff.sh (the drift gate is scripts/check-ts-eff.sh, in the sweep).\n//\n" ++
  "// " ++ what ++ "\n//\n" ++
  "// The Eff program IR and its typing (src/Effect4/Program/{Eff,Native,Typing}.lean,\n" ++
  "// Machine/Supervision.lean, Machine/Scope.lean, Machine/Stores.lean, Machine/Key.lean): constructor\n" ++
  "// and field names verbatim, constructors in declaration order. Two carrier rules, stated here and\n" ++
  "// nowhere else: a family whose constructors are exactly `nil` and `cons head tail` is\n" ++
  "// ReadonlyArray<head>; a family whose constructors are all nullary is a union of string literals.\n" ++
  "// Nat is number, Option is `| null`, List is ReadonlyArray.\n"

def emitSchemas (fs : List Family) : String :=
  header "The families as Effect Schema nodes, and their TypeScript types." ++
  "// Families:\n" ++ "\n".intercalate (fs.map (familyLine fs)) ++ "\n\n" ++
  "import { Schema } from \"effect\"\n\n" ++
  "\n".intercalate (fs.map (emitFamilySchema fs)) ++ "\n" ++
  "/** A program checked against the schema: what the reader hands out, and what a caller may trust. */\n" ++
  "export const decodeEff: (input: unknown) => Eff = Schema.decodeUnknownSync(Eff)\n" ++
  "export const isEff: (input: unknown) => input is Eff = Schema.is(Eff)\n"

/-! ## JSON writers -/

partial def jsonOf (fs : List Family) : OTy → String → String
  | .int, x | .bool, x | .string, x => x
  | .unit, _ => "[]"
  | .option a, x => s!"({x} === null ? null : {jsonOf fs a x})"
  | .list a, x => s!"{x}.map((y) => {jsonOf fs a "y"})"
  | .prod a b, x => s!"[{jsonOf fs a (x ++ "[0]")}, {jsonOf fs b (x ++ "[1]")}]"
  | .named o, x =>
    match familyOf fs o with
    | some f => s!"{jsonFn f}({x})"
    | none => "null"

def emitFamilyJson (fs : List Family) (f : Family) : String :=
  let name := tsName f
  let fn := jsonFn f
  match kindOf f with
  | .enum => s!"export const {fn} = (v: {name}): Json => [v]\n"
  | .struct =>
    let c := f.ctors.head!
    let fields := c.args.map fun (nm, t) => s!"  {nm}: {jsonOf fs t ("v." ++ nm)},"
    s!"export const {fn} = (v: {name}): Json => (\{\n" ++ "\n".intercalate fields ++ "\n})\n"
  | .consList elem =>
    s!"export const {fn} = (v: ReadonlyArray<{tsTy fs elem}>): Json => consList(v, (y) => {jsonOf fs elem "y"})\n"
  | .tagged =>
    let arms := f.ctors.map fun c =>
      let items := lit c.short :: c.args.map fun (nm, t) => jsonOf fs t ("v." ++ nm)
      s!"    case {lit c.short}: return [{", ".intercalate items}]"
    s!"export const {fn} = (v: {name}): Json => \{\n  switch (v._tag) \{\n" ++
      "\n".intercalate arms ++ "\n  }\n}\n"

def emitJson (fs : List Family) (root : Family) : String :=
  header ("One JSON writer per family: the bytes OCaml5.Eff.Goldens.V.json writes and ocaml/eff/eff_json.ml " ++
    "prints. A constructor is [\"name\", field, …], a structure {field: value}, an option the value or null,\n" ++
    "// a cons-list [\"cons\", head, tail] down to [\"nil\"]. Same bytes from three languages.") ++
  "\n" ++
  "import type { " ++ ", ".intercalate (fs.filterMap fun f => match kindOf f with | .consList _ => none | _ => some (tsName f)) ++
    " } from \"./eff.gen.ts\"\n\n" ++
  "export type Json = string | number | boolean | null | ReadonlyArray<Json> | { readonly [key: string]: Json }\n\n" ++
  "const consList = <A>(items: ReadonlyArray<A>, each: (a: A) => Json): Json =>\n" ++
  "  items.reduceRight<Json>((tail, item) => [\"cons\", each(item), tail], [\"nil\"])\n\n" ++
  "\n".intercalate (fs.map (emitFamilyJson fs)) ++ "\n" ++
  s!"/** The program as the exact bytes Lean writes (no whitespace, no trailing newline). */\n" ++
  s!"export const toJson = (e: {tsName root}): string => JSON.stringify({jsonFn root}(e))\n"

/-! ## The profile: values of the families, in the schemas' encoded form

The value printers below spell Lean values as the encoded form of the schemas above:
`{"_tag": ctor, field: …}` for an inductive, `{field: …}` for a structure, the constructor
name for an all-nullary inductive. A field name here that disagrees with the environment fails
the decode at import. -/

def allFnNames : List Effect4.Machine.FnName :=
  [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

/-- The rows with a pure function in the operation (`Ref.update(ref, incr)`). -/
def rmwOps : List (Effect4.Machine.FnName → Effect4.Program.NativeOp) :=
  [.refUpdate, .refGetAndUpdate, .refUpdateAndGet, .refUpdateSome, .refGetAndUpdateSome,
   .refUpdateSomeAndGet, .refModify, .refModifySome]

/-- Every `NativeOp` value, in the declaration order of the inductive. -/
def allNativeOps : List Effect4.Program.NativeOp :=
  [.refMake, .refGet, .refSet, .refGetAndSet, .refSetAndGet] ++
  rmwOps.flatMap (fun con => allFnNames.map con) ++
  [.deferredMake, .deferredIsDone, .deferredPoll, .deferredSucceed, .deferredFail,
   .deferredAwait] ++
  Effect4.FinalizerStrategy.all.map .scopeMake

-- Refuse if any of the three inductives grew, shrank or was reordered: the enumeration
-- above is then stale and the profile would silently miss a row.
run_cmd do
  let env ← Lean.getEnv
  let expect : List (Lean.Name × List Lean.Name) :=
    [ (``Effect4.Program.NativeOp,
        [``Effect4.Program.NativeOp.refMake, ``Effect4.Program.NativeOp.refGet,
         ``Effect4.Program.NativeOp.refSet, ``Effect4.Program.NativeOp.refGetAndSet,
         ``Effect4.Program.NativeOp.refSetAndGet, ``Effect4.Program.NativeOp.refUpdate,
         ``Effect4.Program.NativeOp.refGetAndUpdate, ``Effect4.Program.NativeOp.refUpdateAndGet,
         ``Effect4.Program.NativeOp.refUpdateSome, ``Effect4.Program.NativeOp.refGetAndUpdateSome,
         ``Effect4.Program.NativeOp.refUpdateSomeAndGet, ``Effect4.Program.NativeOp.refModify,
         ``Effect4.Program.NativeOp.refModifySome, ``Effect4.Program.NativeOp.deferredMake,
         ``Effect4.Program.NativeOp.deferredIsDone, ``Effect4.Program.NativeOp.deferredPoll,
         ``Effect4.Program.NativeOp.deferredSucceed, ``Effect4.Program.NativeOp.deferredFail,
         ``Effect4.Program.NativeOp.deferredAwait, ``Effect4.Program.NativeOp.scopeMake])
    , (``Effect4.Machine.FnName,
        [``Effect4.Machine.FnName.incr, ``Effect4.Machine.FnName.double,
         ``Effect4.Machine.FnName.zeroWhenPositive, ``Effect4.Machine.FnName.noChange,
         ``Effect4.Machine.FnName.takeAndBump])
    , (``Effect4.FinalizerStrategy,
        [``Effect4.FinalizerStrategy.sequential, ``Effect4.FinalizerStrategy.parallel]) ]
  for (ind, ctors) in expect do
    match env.find? ind with
    | some (.inductInfo info) =>
      unless info.ctors == ctors do
        throwError "TsGen: {ind} constructors moved: {info.ctors} ≠ {ctors}"
    | _ => throwError "TsGen: {ind} is not an inductive in this environment"

#guard allNativeOps.length = 53
#guard allNativeOps.eraseDups.length = 53

def obj (fields : List (String × String)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => lit k ++ ":" ++ v) ++ "}"

def tagged (ctor : String) (fields : List (String × String)) : String :=
  obj (("_tag", lit ctor) :: fields)

def arr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def fnJs : Effect4.Machine.FnName → String
  | .incr => lit "incr"
  | .double => lit "double"
  | .zeroWhenPositive => lit "zeroWhenPositive"
  | .noChange => lit "noChange"
  | .takeAndBump => lit "takeAndBump"

def strategyJs : Effect4.FinalizerStrategy → String
  | .sequential => lit "sequential"
  | .parallel => lit "parallel"

def opJs : Effect4.Program.NativeOp → String
  | .refMake => tagged "refMake" []
  | .refGet => tagged "refGet" []
  | .refSet => tagged "refSet" []
  | .refGetAndSet => tagged "refGetAndSet" []
  | .refSetAndGet => tagged "refSetAndGet" []
  | .refUpdate f => tagged "refUpdate" [("f", fnJs f)]
  | .refGetAndUpdate f => tagged "refGetAndUpdate" [("f", fnJs f)]
  | .refUpdateAndGet f => tagged "refUpdateAndGet" [("f", fnJs f)]
  | .refUpdateSome f => tagged "refUpdateSome" [("f", fnJs f)]
  | .refGetAndUpdateSome f => tagged "refGetAndUpdateSome" [("f", fnJs f)]
  | .refUpdateSomeAndGet f => tagged "refUpdateSomeAndGet" [("f", fnJs f)]
  | .refModify f => tagged "refModify" [("f", fnJs f)]
  | .refModifySome f => tagged "refModifySome" [("f", fnJs f)]
  | .deferredMake => tagged "deferredMake" []
  | .deferredIsDone => tagged "deferredIsDone" []
  | .deferredPoll => tagged "deferredPoll" []
  | .deferredSucceed => tagged "deferredSucceed" []
  | .deferredFail => tagged "deferredFail" []
  | .deferredAwait => tagged "deferredAwait" []
  | .scopeMake s => tagged "scopeMake" [("strategy", strategyJs s)]

def tyJs : Effect4.Program.Ty → String
  | .never => tagged "never" []
  | .unit => tagged "unit" []
  | .nat => tagged "nat" []
  | .int => tagged "int" []
  | .string => tagged "string" []
  | .bool => tagged "bool" []
  | .handle target => tagged "handle" [("target", lit target)]
  | .option inner => tagged "option" [("inner", tyJs inner)]
  | .list inner => tagged "list" [("inner", tyJs inner)]
  | .prod l r => tagged "prod" [("left", tyJs l), ("right", tyJs r)]
  | .except e v => tagged "except" [("error", tyJs e), ("value", tyJs v)]
  | .exitOf v e => tagged "exitOf" [("value", tyJs v), ("error", tyJs e)]
  | .causeOf e => tagged "causeOf" [("error", tyJs e)]
  | .fiberOf v e => tagged "fiberOf" [("value", tyJs v), ("error", tyJs e)]
  | .union l r => tagged "union" [("left", tyJs l), ("right", tyJs r)]

def shapeJs : Effect4.Program.RowShape → String
  | .call => lit "call"
  | .value => lit "value"

def kindJs : Effect4.Program.RowKind → String
  | .sync => lit "sync"
  | .async => lit "async"
  | .program => lit "program"

def keyJs (k : Effect4.ServiceKey) : String :=
  obj [("name", obj [("value", toString k.name.value)]),
       ("service", obj [("value", toString k.service.value)])]

def rowJs (r : Effect4.Program.Row) : String :=
  obj [ ("name", lit r.name), ("spelling", lit r.spelling), ("shape", shapeJs r.shape)
      , ("trailing", arr (r.trailing.map lit)), ("kind", kindJs r.kind)
      , ("request", tyJs r.request), ("answer", tyJs r.answer), ("error", tyJs r.error)
      , ("requires", arr (r.requires.map keyJs)), ("cite", lit r.cite) ]

def entryJs (op : Effect4.Program.NativeOp) : String :=
  obj [("op", opJs op), ("row", rowJs (Effect4.Program.nativeSignature.rowOf op))]

/-- The payload: address, heads and entries, as one line of JSON. -/
def payload (address : String) : String :=
  obj [ ("address", lit address)
      , ("heads", arr (Effect4.Program.reserved.map lit))
      , ("rows", arr (allNativeOps.map entryJs)) ]

def emitProfile (address : String) : String :=
  let text := payload address
  let stamp := hex (fnv1a64 text)
  "// GENERATED by tools/Tools/TsGen.lean from the Lean environment — do not edit.\n" ++
  "// Regenerate: scripts/generate-ts-eff.sh (the drift gate is scripts/check-ts-eff.sh, in the sweep).\n//\n" ++
  "// The image profile of Effect4.Api.print: the address the bytes were printed under, the reserved\n" ++
  "// heads (Effect4.Program.reserved, in the reader's order), and one entry per NativeOp value — the\n" ++
  "// operation as a NativeOp node and its row (NativeOp.row) as a Row node, both decoded at import\n" ++
  "// through the schemas of eff.gen.ts. `stamp` is FNV-1a 64 over the payload bytes, recomputed here.\n" ++
  "// Address: " ++ address ++ "\n" ++
  "// Stamp:   " ++ toString Effect4.Program.reserved.length ++ " heads, " ++
    toString allNativeOps.length ++ " rows, content " ++ stamp ++ "\n\n" ++
  "import { Schema } from \"effect\"\n" ++
  "import { NativeOp, Row } from \"./eff.gen.ts\"\n\n" ++
  "export const address = " ++ lit address ++ "\n\n" ++
  "export const heads = [\n  " ++ ",\n  ".intercalate (Effect4.Program.reserved.map lit) ++ ",\n] as const\n" ++
  "export type Head = (typeof heads)[number]\n\n" ++
  "/** One native operation and its row. */\n" ++
  "export const Entry = Schema.Struct({ op: NativeOp, row: Row })\n" ++
  "export type Entry = typeof Entry.Type\n\n" ++
  "export const Profile = Schema.Struct({\n" ++
  "  address: Schema.String,\n  heads: Schema.Array(Schema.String),\n  rows: Schema.Array(Entry),\n})\n" ++
  "export type Profile = typeof Profile.Type\n\n" ++
  "/** The payload as Lean wrote it; `stamp` is FNV-1a 64 over exactly these bytes. */\n" ++
  "const text = " ++ lit text ++ "\n" ++
  "export const stamp = " ++ lit stamp ++ "\n\n" ++
  "const fnv1a64 = (s: string): string => {\n" ++
  "  let h = 14695981039346656037n\n" ++
  "  for (const byte of new TextEncoder().encode(s)) h = ((h ^ BigInt(byte)) * 1099511628211n) & 0xffffffffffffffffn\n" ++
  "  return \"0x\" + h.toString(16)\n}\n\n" ++
  "{\n  const recomputed = fnv1a64(text)\n" ++
  "  if (recomputed !== stamp) throw new Error(`profile.gen.ts: stamp ${stamp} does not match its content (${recomputed}); regenerate it`)\n}\n\n" ++
  "export const profile: Profile = Schema.decodeUnknownSync(Profile)(JSON.parse(text))\n\n" ++
  "if (profile.address !== address || profile.heads.length !== heads.length || profile.heads.some((h, i) => h !== heads[i])) {\n" ++
  "  throw new Error(\"profile.gen.ts: the payload and the constants disagree; regenerate it\")\n}\n\n" ++
  "export const rows: ReadonlyArray<Entry> = profile.rows\n"

/-! ## The address, and the cross-check against the printer -/

def stripSpace (s : String) : String :=
  String.ofList (s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r')
    |>.reverse.dropWhile (fun c => c == ' ' || c == '\t' || c == '\r') |>.reverse)

/-- The `rev` of a `[[require]]` block of `lakefile.toml`, read rather than transcribed. -/
def revOf (lakefile : String) (package : String) : Option String := Id.run do
  let lines := lakefile.splitOn "\n"
  let mut armed := false
  for line in lines do
    let trimmed := stripSpace line
    if trimmed == "name = \"" ++ package ++ "\"" then armed := true
    else if armed && trimmed.startsWith "rev = \"" then
      let body := (trimmed.toList.drop "rev = \"".length).dropLast
      return some (String.ofList body)
    else if trimmed == "[[require]]" then armed := false
  return none

/-- Every string literal on a line of `Print.lean` that mentions `.ident`. -/
def identLiterals (source : String) : List String :=
  let onIdentLine (line : String) : List String :=
    if (line.splitOn ".ident").length ≤ 1 then []
    else
      let pieces := line.splitOn "\""
      (pieces.zipIdx.filterMap fun (piece, i) => if i % 2 == 1 then some piece else none)
  ((source.splitOn "\n").flatMap onIdentLine).eraseDups

def missingFrom (xs ys : List String) : List String := xs.filter (fun x => !ys.contains x)

end Tools.TsGen

open Tools.TsGen in
def main (args : List String) : IO Unit := do
  let some outDir := args.head? | throw (IO.userError "usage: TsGen <ts/eff directory>")
  let out : System.FilePath := outDir
  -- the closed world
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Program.Native }] {} 0
  let ctx : Core.Context := { fileName := "<tsgen>", fileMap := default }
  let (bs, _) ← ((readBlocks.run' {}).toIO ctx { env := env })
  let fs := bs.flatten
  for f in fs do
    for c in f.ctors do
      for (nm, t) in c.args do
        for o in namedIn t do
          if (familyOf fs o).isNone then
            throw (IO.userError s!"TsGen: {f.spec.leanName}.{c.short}.{nm} is carried by `{o}`, which is not a family")
  let some root := fs.find? (·.spec.leanName == `Effect4.Program.Eff)
    | throw (IO.userError "TsGen: Effect4.Program.Eff is not among the families")
  -- the address, and the heads against the printer's literals
  let lakefile ← IO.FS.readFile "lakefile.toml"
  let tsRev := (revOf lakefile "typescript").getD "UNKNOWN"
  let address := " + ".intercalate
    (Effect4.Codegen.Profile.hostPin.libraries ++ ["lean4-typescript@" ++ tsRev])
  let printed := identLiterals (← IO.FS.readFile "src/Effect4/Codegen/Print.lean")
  let extraInPrint := missingFrom printed Effect4.Program.reserved
  let extraInHeads := missingFrom Effect4.Program.reserved printed
  unless extraInPrint.isEmpty && extraInHeads.isEmpty do
    throw (IO.userError s!"TsGen: the reader's heads and Print.lean's `.ident` literals differ: in Print.lean only {extraInPrint}; in reserved only {extraInHeads}")
  -- write
  IO.FS.createDirAll out
  let schemas := emitSchemas fs
  let json := emitJson fs root
  let profile := emitProfile address
  IO.FS.writeFile (out / "eff.gen.ts") schemas
  IO.FS.writeFile (out / "json.gen.ts") json
  IO.FS.writeFile (out / "profile.gen.ts") profile
  let kinds := fs.map fun f => match kindOf f with
    | .enum => "literals" | .struct => "struct" | .consList _ => "array" | .tagged => "tagged"
  IO.println s!"TsGen: {fs.length} families ({(kinds.filter (· == "tagged")).length} tagged, {(kinds.filter (· == "literals")).length} literals, {(kinds.filter (· == "struct")).length} struct, {(kinds.filter (· == "array")).length} array), {fs.foldl (fun n f => n + f.ctors.length) 0} constructors; profile {Effect4.Program.reserved.length} heads, {allNativeOps.length} rows, address {address}"
  IO.println s!"wrote {out / "eff.gen.ts"} ({schemas.length}), {out / "json.gen.ts"} ({json.length}), {out / "profile.gen.ts"} ({profile.length}) characters"
