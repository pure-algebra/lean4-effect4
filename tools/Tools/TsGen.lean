import Tools.GeneratedStamp
import Lean
import OCaml5.Eff.World
import OCaml5.Eff.Emit
import Effect4.Program.Native
import Effect4.Program.Packages
import Effect4.Codegen.Profile
import Effect4.Codegen.Read
import Effect4.Ingest.Taxonomy
import Effect4.Codegen.Forms

/-!
# Tools.TsGen — the TypeScript estate's generated files, from the Lean environment

    lake env lean -M4096 --run tools/Tools/TsGen.lean ts/eff

Writes seven files, all `GENERATED`, none ever edited:

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
  `Print.lean`), the pure atom set (`nativeAtom`/`nativeAtomTy`, name, arity and monomorphic
  signature, checked against `nativeAtomTy` at generation — DI-40: the ingest engines and the
  truth prelude read it instead of keeping copies), and one entry per built-in `NativeOp` value — the operation as a `NativeOp` node and
  its `Row` as a `Row` node. No row type is written by hand: `Row`, `Ty`, `NativeOp` are
  families like any other. A stamp (FNV-1a 64 over the payload bytes) is recomputed at import.

* `taxonomy.gen.ts` and `forms.gen.ts` — the refusal partition, relative expansions,
  dual-call metadata and unambiguous lambda shapes, as stamped literal data.
* `wire.gen.ts` — the canonical byte writer for every closed-world family, with an
  explicit work stack and frame-length patching instead of recursive concatenation.
* `packages.gen.ts` — the canonical package tables (`Effect4.Program.Packages.all`, the host
  rows slice): per package its rc.112 key string, service type code, handle target and its
  rows in table order, decoded at import through the `Row` schema; the row at position `i` is
  `NativeOp.external i` under that table. The pinned vendor sources the tables transcribe are
  stamp inputs of this file, so a change under `vendor/` re-cuts it.

Two carrier rules, stated in the generated headers and nowhere else: a family whose
constructors are exactly `nil` and `cons head tail` is `ReadonlyArray<head>`, and a family
whose constructors are all nullary is a union of string literals. `Nat` is `number`, `Option`
is `| null`, `List` is `ReadonlyArray`.

The enumerations behind the profile are checked, not asserted: `run_cmd` reads the three
inductives out of the environment and refuses if their constructor lists moved. A value
printer here that disagrees with a generated schema fails the decode at import, loudly.

`scripts/generate-ts-eff.sh` runs this; `scripts/check-ts-eff.sh` is the stamped drift gate
over the six files, in the sweep. A tool (`IO`, `Lean.Meta`; `lakefile.toml`, the `Tools`
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

def wireRuntime : String :=
  "\n".intercalate
    [ "// The frame algebra of Store.Val. Work is scheduled explicitly: nested programs and"
    , "// inductive lists do not consume the JavaScript call stack. Frame lengths are patched"
    , "// after children finish; bytes are copied only when the growing buffer needs capacity."
    , "class Writer {"
    , "  private buffer = new Uint8Array(1024)"
    , "  private used = 0"
    , "  private tasks: Array<() => void> = []"
    , "  private reserve(count: number): number {"
    , "    const start = this.used"
    , "    const end = start + count"
    , "    if (!Number.isSafeInteger(end)) throw new RangeError(\"wire size\")"
    , "    if (end > this.buffer.length) {"
    , "      const next = new Uint8Array(Math.max(end, this.buffer.length * 2))"
    , "      next.set(this.buffer.subarray(0, start)); this.buffer = next"
    , "    }"
    , "    this.used = end"
    , "    return start"
    , "  }"
    , "  frame(tag: number, children: ReadonlyArray<() => void>): void {"
    , "    const start = this.reserve(9)"
    , "    this.buffer[start] = tag"
    , "    this.tasks.push(() => {"
    , "      const length = BigInt(this.used - start - 9)"
    , "      new DataView(this.buffer.buffer).setBigUint64(start + 1, length, false)"
    , "    })"
    , "    for (let i = children.length - 1; i >= 0; --i) this.tasks.push(children[i]!)"
    , "  }"
    , "  private raw(bytes: Uint8Array): void {"
    , "    const start = this.reserve(bytes.length); this.buffer.set(bytes, start)"
    , "  }"
    , "  nat(n: number): void {"
    , "    if (!Number.isSafeInteger(n) || n < 0 || Object.is(n, -0)) throw new RangeError(\"wire Nat must be an exact nonnegative safe integer\")"
    , "    let v = BigInt(n)"
    , "    if (v >= (1n << 62n)) throw new RangeError(\"wire Nat exceeds OCaml carrier\")"
    , "    const bytes: number[] = []"
    , "    while (v > 0n) { bytes.push(Number(v & 255n)); v >>= 8n }"
    , "    const payload = Uint8Array.from(bytes.reverse())"
    , "    this.frame(2, [() => this.raw(payload)])"
    , "  }"
    , "  bool(value: boolean): void {"
    , "    if (typeof value !== \"boolean\") throw new TypeError(\"wire Bool\")"
    , "    this.frame(1, [() => this.raw(Uint8Array.of(value ? 1 : 0))])"
    , "  }"
    , "  str(value: string): void {"
    , "    if (typeof value !== \"string\") throw new TypeError(\"wire String\")"
    , "    for (let i = 0; i < value.length; ++i) {"
    , "      const code = value.charCodeAt(i)"
    , "      if (code >= 0xd800 && code <= 0xdbff) {"
    , "        const next = value.charCodeAt(++i)"
    , "        if (!(next >= 0xdc00 && next <= 0xdfff)) throw new TypeError(\"wire unpaired surrogate\")"
    , "      } else if (code >= 0xdc00 && code <= 0xdfff) throw new TypeError(\"wire unpaired surrogate\")"
    , "    }"
    , "    const bytes = new TextEncoder().encode(value)"
    , "    this.frame(3, [() => this.raw(bytes)])"
    , "  }"
    , "  unit(value: null): void {"
    , "    if (value !== null) throw new TypeError(\"wire Unit\")"
    , "    this.frame(9, [])"
    , "  }"
    , "  option<A>(value: A | null, each: (a: A) => void): void {"
    , "    if (value === null) this.frame(6, [])"
    , "    else this.frame(7, [() => each(value)])"
    , "  }"
    , "  ctor(index: number, children: ReadonlyArray<() => void>): void {"
    , "    this.frame(10, [() => this.nat(index), ...children])"
    , "  }"
    , "  list<A>(items: ReadonlyArray<A>, each: (a: A) => void): void {"
    , "    if (!Array.isArray(items)) throw new TypeError(\"wire List\")"
    , "    this.frame(4, items.map(a => () => each(a)))"
    , "  }"
    , "  cons<A>(items: ReadonlyArray<A>, each: (a: A) => void, at = 0): void {"
    , "    if (!Array.isArray(items)) throw new TypeError(\"wire inductive list\")"
    , "    if (at === items.length) this.ctor(0, [])"
    , "    else this.ctor(1, [() => each(items[at]!), () => this.cons(items, each, at + 1)])"
    , "  }"
    , "  finish(write: () => void): Uint8Array {"
    , "    this.tasks.push(write)"
    , "    while (this.tasks.length > 0) this.tasks.pop()!()"
    , "    return this.buffer.slice(0, this.used)"
    , "  }"
    , "}"
    , ""
    , ""
    ]

def wireFn (f : Family) : String := lowerFirst (tsName f) ++ "Wire"
def writeFn (f : Family) : String := "write" ++ tsName f

/-- The field traversal is generated structurally from the closed world's carriers. -/
def wireOf (fs : List Family) : OTy → String → String
  | .int, x => s!"w.nat({x})"
  | .bool, x => s!"w.bool({x})"
  | .string, x => s!"w.str({x})"
  | .unit, x => s!"w.unit({x})"
  | .option a, x => s!"w.option({x}, (y) => {wireOf fs a "y"})"
  | .list a, x => s!"w.list({x}, (y) => {wireOf fs a "y"})"
  | .prod a b, x => s!"w.frame(5, [() => {wireOf fs a (x ++ "[0]")}, () => {wireOf fs b (x ++ "[1]")}])"
  | .named o, x =>
    match familyOf fs o with
    | some f => s!"{writeFn f}(w, {x})"
    | none => "missingFamily()"

def emitFamilyWire (fs : List Family) (f : Family) : String :=
  let name := match kindOf f with | .consList elem => "ReadonlyArray<" ++ tsTy fs elem ++ ">" | _ => tsName f
  let ctor (index : Nat) (c : Ctor) :=
    s!"w.ctor({index}, [" ++ ", ".intercalate (c.args.map fun (nm, t) =>
      "() => " ++ wireOf fs t ("v." ++ nm)) ++ "])"
  let body := match kindOf f with
    | .enum =>
      "  switch (v) {\n" ++ "\n".intercalate (f.ctors.zipIdx.map fun ((c, i) : Ctor × Nat) =>
        s!"    case {lit c.short}: return w.ctor({i}, [])") ++
      s!"\n    default: throw new TypeError({lit ("wire " ++ name ++ " constructor")})\n  }"
    | .struct => "  " ++ ctor 0 f.ctors.head!
    | .consList elem => "  w.cons(v, (y) => " ++ wireOf fs elem "y" ++ ")"
    | .tagged =>
      "  switch (v._tag) {\n" ++ "\n".intercalate (f.ctors.zipIdx.map fun ((c, i) : Ctor × Nat) =>
        s!"    case {lit c.short}: return {ctor i c}") ++
      s!"\n    default: throw new TypeError({lit ("wire " ++ name ++ " constructor")})\n  }"
  s!"const {writeFn f} = (w: Writer, v: {name}): void => \{\n{body}\n}\n" ++
  s!"export const {wireFn f} = (v: {name}): Uint8Array => \{\n  const w = new Writer()\n  return w.finish(() => {writeFn f}(w, v))\n}\n"

def emitWire (fs : List Family) : String :=
  header "Canonical byte writers for every family; Store.Val framing and declaration-order constructor tags." ++
  "import type { " ++ ", ".intercalate (fs.filterMap fun f => match kindOf f with | .consList _ => none | _ => some (tsName f)) ++ " } from \"./eff.gen.ts\"\n\n" ++
  wireRuntime ++ "\n".intercalate (fs.map (emitFamilyWire fs)) ++
  "\nexport const encodeProgram = effWire\n"

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

/-- The 55 built-in rows. External indices are supplied by row tables and are not enumerated. -/
def allNativeOps : List Effect4.Program.NativeOp :=
  [.refMake, .refGet, .refSet, .refGetAndSet, .refSetAndGet] ++
  rmwOps.flatMap (fun con => allFnNames.map con) ++
  [.deferredMake, .deferredIsDone, .deferredPoll, .deferredSucceed, .deferredFail,
   .deferredAwait] ++
  Effect4.FinalizerStrategy.all.map .scopeMake ++
  -- the timer (A4, 2026-09-08)
  [.sleep, .clockNow]

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
         ``Effect4.Program.NativeOp.deferredAwait, ``Effect4.Program.NativeOp.scopeMake,
         ``Effect4.Program.NativeOp.sleep, ``Effect4.Program.NativeOp.clockNow,
         ``Effect4.Program.NativeOp.external])
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

#guard allNativeOps.length = 55
#guard allNativeOps.eraseDups.length = 55

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
  | .sleep => tagged "sleep" []
  | .clockNow => tagged "clockNow" []
  | .scopeMake s => tagged "scopeMake" [("strategy", strategyJs s)]
  | .external i => tagged "external" [("index", toString i)]

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
  | .tupleCall => lit "tupleCall"
  | .method => lit "method"

def registrationJs : Effect4.Program.Registration → String
  | .deferred => lit "deferred"
  | .external => lit "external"

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
      , ("requires", arr (r.requires.map keyJs)), ("cite", lit r.cite)
      , ("typeArgs", arr (r.typeArgs.map lit)), ("registration", registrationJs r.registration) ]

def entryJs (op : Effect4.Program.NativeOp) : String :=
  obj [("op", opJs op), ("row", rowJs (Effect4.Program.nativeSignature.rowOf op))]

/-! ### The pure atom set (DI-40)

`Effect4.Program.nativeAtom` and `nativeAtomTy` (`src/Effect4/Program/Native.lean:67-96`) are
a closed table of eleven names, and three hand copies of it existed on the host side: both
ingest engines' `atoms`/`atomNames` sets and the truth prelude's self-test table. The set is
emitted here so those copies become reads.

The rows are `OCaml5.Eff.Emit`'s — the same data the OCaml target emits, so the two targets
cannot disagree — and `OCaml5.Eff.checkAtoms` (`src/OCaml5/Eff/Emit.lean:373-382`) evaluates every row and probe
against `nativeAtomTy` before this file is written: a name or a signature that drifts aborts
the generator rather than being asserted here. `arity` is `null` for the variadic `strings`;
`args`/`answer` are `null` for the three atoms whose type is not monomorphic (`pair`, `fst`,
`snd`), whose signatures are schemes over `Ty` that the profile's `Ty` node cannot spell. -/
def atomJs : String × Option Nat × Option (List Effect4.Program.Ty × Effect4.Program.Ty) → String
  | (name, arity, mono) =>
    obj [ ("name", lit name)
        , ("arity", match arity with | some n => toString n | none => "null")
        , ("args", match mono with | some (args, _) => arr (args.map tyJs) | none => "null")
        , ("answer", match mono with | some (_, answer) => tyJs answer | none => "null") ]

/-- Name, arity and monomorphic signature of every pure atom, in `nativeAtom`'s own order. -/
def atomRows : List (String × Option Nat × Option (List Effect4.Program.Ty × Effect4.Program.Ty)) :=
  (OCaml5.Eff.monoAtoms.map fun (n, args, answer) => (n, some args.length, some (args, answer)))
  ++ [("pair", some 2, none), ("fst", some 1, none), ("snd", some 1, none), ("strings", none, none)]

/-- The payload: address, heads, atoms and entries, as one line of JSON. -/
def payload (address : String) : String :=
  obj [ ("address", lit address)
      , ("heads", arr (Effect4.Program.reserved.map lit))
      , ("atoms", arr (atomRows.map atomJs))
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
    toString atomRows.length ++ " atoms, " ++
    toString allNativeOps.length ++ " rows, content " ++ stamp ++ "\n\n" ++
  "import { Schema } from \"effect\"\n" ++
  "import { NativeOp, Row, Ty } from \"./eff.gen.ts\"\n\n" ++
  "export const address = " ++ lit address ++ "\n\n" ++
  "export const heads = [\n  " ++ ",\n  ".intercalate (Effect4.Program.reserved.map lit) ++ ",\n] as const\n" ++
  "export type Head = (typeof heads)[number]\n\n" ++
  "/** The pure atoms of the native route, `Effect4.Program.nativeAtom` in its own order: the\n" ++
  " * only identifiers besides the reserved heads and the row spellings that a printed term\n" ++
  " * may mention. `arity` is null for the variadic `strings`; `args`/`answer` are null for the\n" ++
  " * atoms whose `nativeAtomTy` arm is a scheme, not a monomorphic row. */\n" ++
  "export const Atom = Schema.Struct({\n" ++
  "  name: Schema.String,\n  arity: Schema.NullOr(Schema.Number),\n" ++
  "  args: Schema.NullOr(Schema.Array(Ty)),\n  answer: Schema.NullOr(Ty),\n})\n" ++
  "export type Atom = typeof Atom.Type\n\n" ++
  "/** One native operation and its row. */\n" ++
  "export const Entry = Schema.Struct({ op: NativeOp, row: Row })\n" ++
  "export type Entry = typeof Entry.Type\n\n" ++
  "export const Profile = Schema.Struct({\n" ++
  "  address: Schema.String,\n  heads: Schema.Array(Schema.String),\n" ++
  "  atoms: Schema.Array(Atom),\n  rows: Schema.Array(Entry),\n})\n" ++
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
  "export const atoms: ReadonlyArray<Atom> = profile.atoms\n" ++
  "/** The atom names as a set, for a reader deciding whether an identifier is an atom. */\n" ++
  "export const atomNames: ReadonlySet<string> = new Set(atoms.map((a) => a.name))\n\n" ++
  "export const rows: ReadonlyArray<Entry> = profile.rows\n"


/-! ## The package tables (`Effect4.Program.Packages.all`), rows through the `Row` schema -/

def packageJs (p : Effect4.Program.Packages.Package) : String :=
  obj [ ("name", lit p.name), ("key", lit p.key), ("module", lit p.module), ("service", toString p.service)
      , ("target", lit p.target), ("rows", arr (p.rows.map rowJs)) ]

def emitPackages : String :=
  let text := arr (Effect4.Program.Packages.all.map packageJs)
  let stamp := hex (fnv1a64 text)
  "// GENERATED by tools/Tools/TsGen.lean from the Lean environment — do not edit.\n" ++
  "// Regenerate: scripts/generate-ts-eff.sh (the drift gate is scripts/check-ts-eff.sh, in the sweep).\n//\n" ++
  "// The canonical package tables (Effect4.Program.Packages.all, the host rows slice): per package its\n" ++
  "// rc.112 key string, service type code and handle target, and its rows in table order — the row at\n" ++
  "// position i is NativeOp.external i under that table (Read.lean nativeSpell; an index is never parsed\n" ++
  "// out of an identifier). Rows decode at import through the Row schema of eff.gen.ts. `stamp` is\n" ++
  "// FNV-1a 64 over the payload bytes, recomputed here.\n" ++
  "// Pin: effect@4.0.0-rc.112. Inputs (stamped): vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts,\n" ++
  "// vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts,\n" ++
  "// vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts.\n" ++
  "// Stamp:   " ++ toString Effect4.Program.Packages.all.length ++ " packages, " ++
    toString (Effect4.Program.Packages.all.foldl (fun n p => n + p.rows.length) 0) ++ " rows, content " ++ stamp ++ "\n\n" ++
  "import { Schema } from \"effect\"\n" ++
  "import { Row } from \"./eff.gen.ts\"\n\n" ++
  "/** One package: its key, service code, handle target and rows (in table order). */\n" ++
  "export const Package = Schema.Struct({\n" ++
  "  name: Schema.String,\n  key: Schema.String,\n  module: Schema.String,\n  service: Schema.Number,\n  target: Schema.String,\n  rows: Schema.Array(Row),\n})\n" ++
  "export type Package = typeof Package.Type\n\n" ++
  "/** The payload as Lean wrote it; `stamp` is FNV-1a 64 over exactly these bytes. */\n" ++
  "const text = " ++ lit text ++ "\n" ++
  "export const stamp = " ++ lit stamp ++ "\n\n" ++
  "const fnv1a64 = (s: string): string => {\n" ++
  "  let h = 14695981039346656037n\n" ++
  "  for (const byte of new TextEncoder().encode(s)) h = ((h ^ BigInt(byte)) * 1099511628211n) & 0xffffffffffffffffn\n" ++
  "  return \"0x\" + h.toString(16)\n}\n\n" ++
  "{\n  const recomputed = fnv1a64(text)\n" ++
  "  if (recomputed !== stamp) throw new Error(`packages.gen.ts: stamp ${stamp} does not match its content (${recomputed}); regenerate it`)\n}\n\n" ++
  "export const packages: ReadonlyArray<Package> = Schema.decodeUnknownSync(Schema.Array(Package))(JSON.parse(text))\n\n" ++
  "/** The package whose key a service type code names, if any (nativeServiceTy's codes 8 and 9). */\n" ++
  "export const packageOf = (service: number): Package | undefined => packages.find((p) => p.service === service)\n"

/-! ## The ingestion tables, as immutable literal data with import-time stamps -/

def emitTable (name data : String) : String :=
  header ("Lean-owned " ++ name ++ " table; the import-time stamp covers the complete payload.") ++
  s!"export const {name} = {data} as const\n" ++
  s!"export const stamp = {lit (hex (fnv1a64 data))}\n" ++
  "const fnv1a64 = (s: string): string => {\n" ++
  "  let h = 14695981039346656037n\n" ++
  "  for (const byte of new TextEncoder().encode(s)) h = ((h ^ BigInt(byte)) * 1099511628211n) & 0xffffffffffffffffn\n" ++
  "  return \"0x\" + h.toString(16)\n}\n" ++
  s!"if (fnv1a64(JSON.stringify({name})) !== stamp) throw new Error({lit (name ++ " table stamp mismatch; regenerate")})\n"

def emitTaxonomy : String :=
  let rows := Effect4.Ingest.Code.all.map fun c => obj
    [("code", lit c.wire), ("spectrum", lit c.spectrum.wire),
     ("status", lit c.status.wire), ("detail", lit c.detailTemplate)]
  emitTable "taxonomy" (arr rows) ++
  "export type Code = (typeof taxonomy)[number][\"code\"]\n" ++
  "export const activeCodes = taxonomy.filter(r => r.status === \"active\").map(r => r.code)\n" ++
  "export const reservedCodes = taxonomy.filter(r => r.status === \"reserved\").map(r => r.code)\n"

open Effect4.Codegen.Forms in
def argClassJs : ArgClass → String
  | .effect => lit "effect" | .continuation => lit "continuation" | .thunk => lit "thunk"
  | .literal => lit "literal" | .term => lit "term" | .termArm => lit "termArm" | .key => lit "key"
  | .releaseOne => lit "releaseOne" | .handlers => lit "handlers"

open Effect4.Codegen.Forms in
def arityJs : Arity → String
  | .value => tagged "value" []
  | .call n => tagged "call" [("count", toString n)]
  | .dual n => tagged "dual" [("count", toString n)]

def literalJs : Effect4.Program.Lit → String
  | .unit => tagged "unit" []
  | .nat n => tagged "nat" [("value", toString n)]
  | .bool b => tagged "bool" [("value", toString b)]
  | .str s => tagged "str" [("value", lit s)]

open Effect4.Codegen.Forms in
def termTemplateJs : TermTemplate → String
  | .literal v => tagged "literal" [("value", literalJs v)]
  | .argument i => tagged "argument" [("slot", toString i)]
  | .here k => tagged "here" [("binder", toString k)]

def optionsJs (o : Effect4.Supervision.ForkOptions) : String :=
  obj [("startImmediately", toString o.startImmediately), ("daemon", toString o.daemon),
       ("maskMode", lit (match o.maskMode with | .inherit => "inherit" | .interruptible => "interruptible" | .uninterruptible => "uninterruptible"))]

open Effect4.Codegen.Forms in
def templateJs : Template → String
  | .argument slot cutOffset insertions => tagged "argument"
      [("slot", toString slot), ("cutOffset", toString cutOffset), ("insertions", toString insertions)]
  | .succeed value => tagged "succeed" [("value", termTemplateJs value)]
  | .die value => tagged "die" [("value", termTemplateJs value)]
  | .bind a b => tagged "bind" [("first", templateJs a), ("rest", templateJs b)]
  | .onExit a b => tagged "onExit" [("body", templateJs a), ("finalizer", templateJs b)]
  | .matchCause a b c => tagged "matchCause" [("body", templateJs a), ("onValue", templateJs b), ("onCause", templateJs c)]
  | .service i => tagged "service" [("keySlot", toString i)]
  | .yieldNow n => tagged "yieldNow" [("priority", toString n)]
  | .fork b o => tagged "fork" [("body", templateJs b), ("options", optionsJs o)]
  | .forkIn b scope o => tagged "forkIn" [("body", templateJs b), ("scope", termTemplateJs scope), ("options", optionsJs o)]
  | .forkScoped b o => tagged "forkScoped" [("body", templateJs b), ("options", optionsJs o)]
  | .acquireRelease a b => tagged "acquireRelease" [("acquire", templateJs a), ("release", templateJs b)]

open Effect4.Codegen.Forms in
def dualJs : DualRule → String
  | .fixed n => tagged "fixed" [("arity", toString n)]
  | .effectFirst => tagged "effectFirst" []
  | .provideService => tagged "provideService" []
  | .functionSecond => tagged "functionSecond" []
  | .effectSecond => tagged "effectSecond" []

open Effect4.Codegen.Forms in
def lambdaJs (f : Effect4.Machine.FnName) : String :=
  obj [("atom", fnJs f), ("shape", match lambdaShape f with
    | none => "null"
    | some .addOne => lit "addOne"
    | some .multiplyTwo => lit "multiplyTwo"
    | some .optionNone => lit "optionNone"
    | some .positiveThenZero => lit "positiveThenZero")]

open Effect4.Codegen.Forms in
def emitForms : String :=
  let rows := all.map fun f => obj [("id", lit f.id), ("head", lit f.head),
    ("arity", arityJs f.arity), ("arguments", arr (f.arguments.map argClassJs)),
    ("expansion", templateJs f.expansion), ("citation", lit f.citation)]
  emitTable "forms" (obj [("rows", arr rows), ("lambdas", arr (allFnNames.map lambdaJs)),
    ("duals", arr (duals.map fun (head, rule) => obj [("head", lit head), ("rule", dualJs rule)])),
    ("unaryRefs", arr (unaryRefs.map lit))])

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
  -- the atom set is data here (DI-40); `checkAtoms` evaluates every row and probe against
  -- `nativeAtomTy`, so a drifted name or signature aborts rather than being emitted
  match OCaml5.Eff.checkAtoms with
  | .error e => throw (IO.userError s!"TsGen: the atom table disagrees with nativeAtomTy: {e}")
  | .ok _ => pure ()
  let printed := identLiterals (← IO.FS.readFile "src/Effect4/Codegen/Print.lean")
  -- readRunIn consumes Effect.void only as its fixed block return, not as an
  -- effect head, and printTupleArgs spells a saved tuple request's components with
  -- the fst/snd atoms (source-repairs §18). Check those nested literals in both
  -- directions as well.
  let expectedIdents := Effect4.Program.reserved ++ ["Effect.void", "fst", "snd"]
  let extraInPrint := missingFrom printed expectedIdents
  let extraInHeads := missingFrom expectedIdents printed
  unless extraInPrint.isEmpty && extraInHeads.isEmpty do
    throw (IO.userError s!"TsGen: the reader's heads/nested return literal and Print.lean's `.ident` literals differ: in Print.lean only {extraInPrint}; in reserved only {extraInHeads}")
  -- the package tables transcribe pinned vendor sources; they are stamp inputs, so a change
  -- under vendor/ re-cuts every file this tool writes
  let stamp ← Tools.GeneratedStamp.line "tools/Tools/TsGen.lean"
    ["Effect4.Program.Native", "Effect4.Program.Packages"]
    ["lakefile.toml", "src/Effect4/Codegen/Print.lean",
     "vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlClient.ts",
     "vendor/effect-4.0.0-rc.112/src/unstable/sql/Statement.ts",
     "vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts"]
  let stampHeader := "// " ++ stamp ++ "\n"
  -- write
  IO.FS.createDirAll out
  let schemas := emitSchemas fs
  let json := emitJson fs root
  let profile := emitProfile address
  IO.FS.writeFile (out / "eff.gen.ts") (stampHeader ++ schemas)
  IO.FS.writeFile (out / "json.gen.ts") (stampHeader ++ json)
  IO.FS.writeFile (out / "profile.gen.ts") (stampHeader ++ profile)
  IO.FS.writeFile (out / "wire.gen.ts") (stampHeader ++ (emitWire fs))
  IO.FS.writeFile (out / "taxonomy.gen.ts") (stampHeader ++ emitTaxonomy)
  IO.FS.writeFile (out / "forms.gen.ts") (stampHeader ++ emitForms)
  IO.FS.writeFile (out / "packages.gen.ts") (stampHeader ++ emitPackages)
  let kinds := fs.map fun f => match kindOf f with
    | .enum => "literals" | .struct => "struct" | .consList _ => "array" | .tagged => "tagged"
  IO.println s!"TsGen: {fs.length} families ({(kinds.filter (· == "tagged")).length} tagged, {(kinds.filter (· == "literals")).length} literals, {(kinds.filter (· == "struct")).length} struct, {(kinds.filter (· == "array")).length} array), {fs.foldl (fun n f => n + f.ctors.length) 0} constructors; profile {Effect4.Program.reserved.length} heads, {atomRows.length} atoms, {allNativeOps.length} rows; packages {Effect4.Program.Packages.all.length} tables, {Effect4.Program.Packages.all.foldl (fun n p => n + p.rows.length) 0} rows, address {address}"
  IO.println s!"wrote eff.gen.ts, json.gen.ts, profile.gen.ts, taxonomy.gen.ts, forms.gen.ts, wire.gen.ts, packages.gen.ts under {out}"
