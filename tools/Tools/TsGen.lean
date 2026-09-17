import Tools.GeneratedStamp
import Tools.ProfileJson
import Lean
import OCaml5.Eff.World
import OCaml5.Eff.Emit
import Effect4.Program.Native
import Effect4.Program.Packages
import Effect4.Codegen.Read
import Effect4.Codegen.Templates
import Effect4.Ingest.Taxonomy
import Effect4.Codegen.Forms

/-!
# Tools.TsGen — the TypeScript estate's generated files, from the Lean environment

    lake env lean -M4096 --run tools/Tools/TsGen.lean ts/eff

Writes eight files, all `GENERATED`, none ever edited:

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
  signature, projected from `NativeAtom` — DI-40: the ingest engines and the
  truth prelude read it instead of keeping copies), the native reserved/ordinary service
  type tables and their spelling, and one entry per built-in `NativeOp` value — the operation as a `NativeOp` node and
  its `Row` as a `Row` node. No row type is written by hand: `Row`, `Ty`, `NativeOp` are
  families like any other. A stamp (FNV-1a 64 over the payload bytes) is recomputed at import.

* `taxonomy.gen.ts` and `forms.gen.ts` — the refusal partition, relative expansions,
  dual-call metadata and unambiguous lambda shapes, as stamped literal data.
* `wire.gen.ts` — the canonical byte writer for every closed-world family, with an
  explicit work stack and frame-length patching instead of recursive concatenation.
* `templates.gen.ts` — the table of printed clauses (`Effect4.Codegen.Templates.table`), each
  constructor's argument sorts and field names, and the reserved names that head a program
  clause: what `ts/eff/read.ts`'s one matcher runs over, as Lean's `readT` does. The reserved
  heads are cross-checked against the identifiers the table's skeletons write (data, not a
  source scan) and `PrintLeaf.lean`'s literals.
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

`make gen-ts` (`scripts/generate.py --only ts`) runs this; `make check-gen` is the drift check
over the eight files. A tool (`IO`, `Lean.Meta`; `lakefile.toml`, the `Tools`
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
  | .requirements => ["service_key"]
  | .named o => [o]
  | .option a | .list a => namedIn a
  | .prod a b => namedIn a ++ namedIn b
  | _ => []

partial def tsTy (fs : List Family) : OTy → String
  | .requirements => "ReadonlyArray<ServiceKey>"
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
  | .requirements => "Schema.Array(ServiceKey).check(Schema.makeFilter((xs) => xs.every((b, i) => i === 0 || ((a) => a !== undefined && (a.name.value < b.name.value || (a.name.value === b.name.value && a.service.value < b.service.value)))(xs[i - 1]))))"
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
  "// Regenerate: make gen-ts (the drift check is make check-gen).\n//\n" ++
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
  | .requirements, x => s!"{x}.map(serviceKeyJson)"
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
    , "  ctor(tag: number, children: ReadonlyArray<() => void>): void {"
    , "    this.frame(10, [() => this.nat(tag), ...children])"
    , "  }"
    , "  list<A>(items: ReadonlyArray<A>, each: (a: A) => void): void {"
    , "    if (!Array.isArray(items)) throw new TypeError(\"wire List\")"
    , "    this.frame(4, items.map(a => () => each(a)))"
    , "  }"
    , "  cons<A>(items: ReadonlyArray<A>, each: (a: A) => void, nil: number, cons: number, at = 0): void {"
    , "    if (!Array.isArray(items)) throw new TypeError(\"wire inductive list\")"
    , "    if (at === items.length) this.ctor(nil, [])"
    , "    else this.ctor(cons, [() => each(items[at]!), () => this.cons(items, each, nil, cons, at + 1)])"
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
  | .requirements, x => s!"(() => \{ if (!{x}.every((b, i) => i === 0 || ((a) => a !== undefined && (a.name.value < b.name.value || (a.name.value === b.name.value && a.service.value < b.service.value)))({x}[i - 1]))) throw new TypeError(\"noncanonical requirements\"); w.list({x}, (y) => writeServiceKey(w, y)) })()"
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
  -- The number written is the constructor's wire tag (`Ctor.tag`, from the one assignment
  -- `tools/Effect4Gen/wire-tags.json`), never its position in the declaration.
  let ctor (tag : Nat) (c : Ctor) :=
    s!"w.ctor({tag}, [" ++ ", ".intercalate (c.args.map fun (nm, t) =>
      "() => " ++ wireOf fs t ("v." ++ nm)) ++ "])"
  let body := match kindOf f with
    | .enum =>
      "  switch (v) {\n" ++ "\n".intercalate (f.ctors.map fun (c : Ctor) =>
        s!"    case {lit c.short}: return w.ctor({c.tag}, [])") ++
      s!"\n    default: throw new TypeError({lit ("wire " ++ name ++ " constructor")})\n  }"
    | .struct => "  " ++ ctor 0 f.ctors.head!
    | .consList elem =>
      let tagOf (short : String) : Nat :=
        match f.ctors.find? (fun (c : Ctor) => c.short == short) with
        | some c => c.tag
        | none => 0
      "  w.cons(v, (y) => " ++ wireOf fs elem "y" ++ s!", {tagOf "nil"}, {tagOf "cons"})"
    | .tagged =>
      "  switch (v._tag) {\n" ++ "\n".intercalate (f.ctors.map fun (c : Ctor) =>
        s!"    case {lit c.short}: return {ctor c.tag c}") ++
      s!"\n    default: throw new TypeError({lit ("wire " ++ name ++ " constructor")})\n  }"
  s!"const {writeFn f} = (w: Writer, v: {name}): void => \{\n{body}\n}\n" ++
  s!"export const {wireFn f} = (v: {name}): Uint8Array => \{\n  const w = new Writer()\n  return w.finish(() => {writeFn f}(w, v))\n}\n"

def emitWire (fs : List Family) : String :=
  header "Canonical byte writers for every family; Store.Val framing and the wire tags of tools/Effect4Gen/wire-tags.json." ++
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

/-- The target metadata writers share one JSON view with the truth manifest. -/
def tyJs (ty : Effect4.Program.Ty) : String := (Tools.ProfileJson.tyJson ty).compress

def shapeJs (shape : Effect4.Program.RowShape) : String := (Tools.ProfileJson.shapeJson shape).compress

def registrationJs (registration : Effect4.Program.Registration) : String :=
  (Tools.ProfileJson.registrationJson registration).compress

def kindJs (kind : Effect4.Program.RowKind) : String := (Tools.ProfileJson.kindJson kind).compress

def keyJs (key : Effect4.ServiceKey) : String := (Tools.ProfileJson.keyJson key).compress

def rowJs (row : Effect4.Program.Row) : String := (Tools.ProfileJson.rowJson row).compress

def entryJs (op : Effect4.Program.NativeOp) : String :=
  obj [("op", opJs op), ("row", rowJs (Effect4.Program.nativeSignature.rowOf op))]

/-! ### The pure atom set (DI-40)

`Effect4.Program.NativeAtom` (`src/Effect4/Program/NativeAtom.lean`) owns the complete
finite atom inventory, exhaustive typing/evaluation, names, arities and monomorphic
metadata. Both foreign readers and the prelude coverage check read its generated projection.

`atomRows` projects that complete inventory directly. `NativeAtom.all_complete` and
`NativeAtom.typeOf_mono` supply the inventory and monomorphic-signature laws; this
profile emits metadata, not a second implementation of polymorphic typing.
`arity` is null for a variadic atom, and `args`/`answer` are null for schemes. -/

def atomJs : String × Option Nat × Option (List Effect4.Program.Ty × Effect4.Program.Ty) → String
  | (name, arity, mono) =>
    obj [ ("name", lit name)
        , ("arity", match arity with | some n => toString n | none => "null")
        , ("args", match mono with | some (args, _) => arr (args.map tyJs) | none => "null")
        , ("answer", match mono with | some (_, answer) => tyJs answer | none => "null") ]

/-- Name, arity and monomorphic signature of every pure atom, in `nativeAtom`'s own order. -/
def atomRows : List (String × Option Nat × Option (List Effect4.Program.Ty × Effect4.Program.Ty)) :=
  Effect4.Program.NativeAtom.all.map fun atom => (atom.name, atom.arity, atom.mono)

/-- The service lookup's complete finite inputs, including reserved-name policy.
The legacy text profile retains `Ty.render`; the printer separately converts the
same core types to structural TypeScript syntax. -/
def servicesJs : String :=
  obj [("firstFreeName", toString Effect4.Machine.Env.firstFreeName),
    ("reserved", arr (Effect4.Program.nativeReservedServiceTypes.map fun (key, ty) =>
      obj [("key", keyJs key), ("ty", tyJs ty), ("rendered", lit ty.render)])),
    ("ordinary", arr (Effect4.Program.nativeServiceTypes.map fun (code, ty) =>
      obj [("code", toString code), ("ty", tyJs ty), ("rendered", lit ty.render)]))]

/-- The payload: address, heads, atoms, services and entries, as one line of JSON. -/
def payload (address : String) : String :=
  obj [ ("address", lit address)
      , ("heads", arr (Effect4.Program.reserved.map lit))
      , ("atoms", arr (atomRows.map atomJs))
      , ("services", servicesJs)
      , ("rows", arr (allNativeOps.map entryJs)) ]

def emitProfile (address : String) : String :=
  let text := payload address
  let stamp := hex (fnv1a64 text)
  "// GENERATED by tools/Tools/TsGen.lean from the Lean environment — do not edit.\n" ++
  "// Regenerate: make gen-ts (the drift check is make check-gen).\n//\n" ++
  "// The image profile of Effect4.Api.print: the address the bytes were printed under, the reserved\n" ++
  "// heads (Effect4.Program.reserved, in the reader's order), and one entry per NativeOp value — the\n" ++
  "// operation as a NativeOp node and its row (NativeOp.row) as a Row node, both decoded at import\n" ++
  "// through the schemas of eff.gen.ts. `stamp` is FNV-1a 64 over the payload bytes, recomputed here.\n" ++
  "// Address: " ++ address ++ "\n" ++
  "// Stamp:   " ++ toString Effect4.Program.reserved.length ++ " heads, " ++
    toString atomRows.length ++ " atoms, " ++
    toString allNativeOps.length ++ " rows, content " ++ stamp ++ "\n\n" ++
  "import { Schema } from \"effect\"\n" ++
  "import { NativeOp, Row, ServiceKey, Ty } from \"./eff.gen.ts\"\n\n" ++
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
  "/** The native service lookup, projected from its actual Lean tables. */\n" ++
  "export const ServiceTypes = Schema.Struct({\n" ++
  "  firstFreeName: Schema.Number,\n" ++
  "  reserved: Schema.Array(Schema.Struct({ key: ServiceKey, ty: Ty, rendered: Schema.String })),\n" ++
  "  ordinary: Schema.Array(Schema.Struct({ code: Schema.Number, ty: Ty, rendered: Schema.String })),\n})\n" ++
  "export type ServiceTypes = typeof ServiceTypes.Type\n\n" ++
  "export const Profile = Schema.Struct({\n" ++
  "  address: Schema.String,\n  heads: Schema.Array(Schema.String),\n" ++
  "  atoms: Schema.Array(Atom),\n  services: ServiceTypes,\n  rows: Schema.Array(Entry),\n})\n" ++
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
  "export const rows: ReadonlyArray<Entry> = profile.rows\n" ++
  "export const serviceTypes: ServiceTypes = profile.services\n\n" ++
  "/** Same reserved-first lookup as Program.nativeServiceTy; no local type-code policy. */\n" ++
  "export const serviceTypeFor = (key: ServiceKey): { readonly ty: Ty; readonly rendered: string } | undefined => {\n" ++
  "  const reserved = serviceTypes.reserved.find(entry => entry.key.name.value === key.name.value && entry.key.service.value === key.service.value)\n" ++
  "  if (reserved !== undefined) return reserved\n" ++
  "  if (key.name.value < serviceTypes.firstFreeName) return undefined\n" ++
  "  return serviceTypes.ordinary.find(entry => entry.code === key.service.value)\n}\n"


/-! ## The package tables (`Effect4.Program.Packages.all`), rows through the `Row` schema -/

def packageJs (p : Effect4.Program.Packages.Package) : String :=
  obj [ ("name", lit p.name), ("key", lit p.key), ("module", lit p.module), ("service", toString p.service)
      , ("target", lit p.target), ("rows", arr (p.rows.map rowJs)) ]

def emitPackages : String :=
  let text := arr (Effect4.Program.Packages.all.map packageJs)
  let stamp := hex (fnv1a64 text)
  "// GENERATED by tools/Tools/TsGen.lean from the Lean environment — do not edit.\n" ++
  "// Regenerate: make gen-ts (the drift check is make check-gen).\n//\n" ++
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

/-! ## The table of printed clauses (`Effect4.Codegen.Templates.table`), for the reader's one matcher

The TypeScript reader has no clause per head: it matches a tree against these rows, as Lean's
`readT` does (`src/Effect4/Codegen/Read.lean`). Beside the rows go what the generic step needs of
the constructor declarations: each constructor's argument sorts (`Effect4.Program.argSorts`) and
its field names in declaration order (the families above), and the reserved names that head a
program clause (`Effect4.Program.programHeads`). -/

section Templates
open Effect4.Codegen.Template Effect4.Codegen.Templates

mutual
  def tplJs : Tpl → String
    | .hole i => tagged "hole" [("i", toString i)]
    | .strHole i => tagged "strHole" [("i", toString i)]
    | .intHole i => tagged "intHole" [("i", toString i)]
    | .arrHole i => tagged "arrHole" [("i", toString i)]
    | .binderRef k => tagged "binderRef" [("k", toString k)]
    | .ident name => tagged "ident" [("name", lit name)]
    | .str value => tagged "str" [("value", lit value)]
    | .int value => tagged "int" [("value", toString value)]
    | .bool value => tagged "bool" [("value", toString value)]
    | .call head args => tagged "call" [("head", tplJs head), ("args", "[" ++ tplsJs args ++ "]")]
    | .callSpread head i => tagged "callSpread" [("head", tplJs head), ("i", toString i)]
    | .arr items => tagged "arr" [("items", "[" ++ tplsJs items ++ "]")]
    | .object fields => tagged "object" [("fields", "[" ++ fieldsJs fields ++ "]")]
    | .arrow body => tagged "arrow" [("body", tplJs body)]
    | .lambda binders body =>
      tagged "lambda" [("binders", arr (binders.map toString)), ("body", tplJs body)]
    | .cond test yes no => tagged "cond" [("test", tplJs test), ("yes", tplJs yes), ("no", tplJs no)]
    | .method target name args =>
      tagged "method" [("target", tplJs target), ("name", lit name), ("args", "[" ++ tplsJs args ++ "]")]
    | .arrowBlock binders body =>
      tagged "arrowBlock" [("binders", arr (binders.map toString)), ("body", stmtTplsJs body)]
    | .generator body => tagged "generator" [("body", stmtTplsJs body)]
  def tplsJs : Tpls → String
    | .nil => ""
    | .cons head .nil => tplJs head
    | .cons head tail => tplJs head ++ "," ++ tplsJs tail
  def fieldsJs : Fields → String
    | .nil => ""
    | .cons key value .nil => "[" ++ lit key ++ "," ++ tplJs value ++ "]"
    | .cons key value tail => "[" ++ lit key ++ "," ++ tplJs value ++ "]," ++ fieldsJs tail
  def stmtTplJs : StmtTpl → String
    | .letInit k value ann =>
      tagged "letInit" [("k", toString k), ("value", tplJs value),
        ("ann", match ann with | some i => toString i | none => "null")]
    | .assign k value => tagged "assign" [("k", toString k), ("value", tplJs value)]
    | .ret value => tagged "ret" [("value", tplJs value)]
    | .exprStmt value => tagged "exprStmt" [("value", tplJs value)]
    | .constYield k value => tagged "constYield" [("k", toString k), ("value", tplJs value)]
    | .yieldDiscard value => tagged "yieldDiscard" [("value", tplJs value)]
    | .ifElse test thenB elseB =>
      tagged "ifElse" [("test", tplJs test), ("thenB", stmtTplsJs thenB), ("elseB", stmtTplsJs elseB)]
    | .whileTrue body => tagged "whileTrue" [("body", stmtTplsJs body)]
    | .breakTo => tagged "breakTo" []
  /-- A statement list: one captured list, or its statements in order. -/
  def stmtTplsJs : StmtTpls → String
    | .hole i => tagged "hole" [("i", toString i)]
    | list => "[" ++ stmtItemsJs list ++ "]"
  def stmtItemsJs : StmtTpls → String
    | .nil => ""
    | .cons head .nil => stmtTplJs head
    | .cons head tail => stmtTplJs head ++ "," ++ stmtItemsJs tail
    -- a list that ends in a captured rest has no row today; `listsClosed` refuses it by name
    | .hole i => tagged "rest" [("i", toString i)]
end

mutual
  /-- Every statement list of a skeleton is one captured list or a closed list of statements:
  the two shapes the TypeScript matcher reads. -/
  def listsClosed : Tpl → Bool
    | .call head args | .method head _ args => listsClosed head && listsClosedTs args
    | .callSpread head _ => listsClosed head
    | .arr items => listsClosedTs items
    | .object fields => listsClosedFields fields
    | .arrow body | .lambda _ body => listsClosed body
    | .cond test yes no => listsClosed test && listsClosed yes && listsClosed no
    | .arrowBlock _ body | .generator body => listClosed body
    | _ => true
  def listsClosedTs : Tpls → Bool
    | .nil => true
    | .cons head tail => listsClosed head && listsClosedTs tail
  def listsClosedFields : Fields → Bool
    | .nil => true
    | .cons _ value tail => listsClosed value && listsClosedFields tail
  def listsClosedStmt : StmtTpl → Bool
    | .letInit _ value _ | .assign _ value | .ret value | .exprStmt value
    | .constYield _ value | .yieldDiscard value => listsClosed value
    | .ifElse test thenB elseB => listsClosed test && listClosed thenB && listClosed elseB
    | .whileTrue body => listClosed body
    | .breakTo => true
  def listClosed : StmtTpls → Bool
    | .hole _ => true
    | list => itemsClosed list
  def itemsClosed : StmtTpls → Bool
    | .nil => true
    | .cons head tail => listsClosedStmt head && itemsClosed tail
    | .hole _ => false
end

/-- A classifier pattern. A term pattern is a literal in every row; any other term is refused
here, by name, so that a new row cannot slip a pattern past the TypeScript reader. -/
def argPatJs : ArgPat → Except String String
  | .term (.lit value) =>
    .ok (tagged "term" [("value", tagged "lit" [("value", literalJs value)])])
  | .term _ => .error "a term pattern that is not a literal"
  | .bool b => .ok (tagged "bool" [("value", toString b)])
  | .mode .joinEffect => .ok (tagged "mode" [("value", lit "joinEffect")])
  | .mode .awaitValue => .ok (tagged "mode" [("value", lit "awaitValue")])
  | .decisionBool => .ok (tagged "decisionBool" [])
  | .decisionOption => .ok (tagged "decisionOption" [])
  | .decisionTag => .ok (tagged "decisionTag" [])
  | .optTermNone => .ok (tagged "optTermNone" [])
  | .optTermSome => .ok (tagged "optTermSome" [])
  | .optTyNone => .ok (tagged "optTyNone" [])
  | .optTySome => .ok (tagged "optTySome" [])
  | .daemon b => .ok (tagged "daemon" [("value", toString b)])

/-- The depth an argument is read at, as `Templates.argDepth` decides it: closed for an argument
of a layer family, otherwise under the binders its hole is under (`Template.levelAt`). -/
def depthJs (fam : Effect4.Program.EffFam) (sort : Effect4.Program.ArgSort) (level : Nat) : String :=
  match fam, sort with
  | .layer, _ | .layers, _ | _, .child .layer | _, .child .layers => tagged "closed" []
  | _, _ => tagged "rel" [("k", toString level)]

def famJs : Effect4.Program.EffFam → String
  | .eff => "eff" | .stmt => "stmt" | .stmts => "stmts" | .effs => "effs"
  | .action => "action" | .layer => "layer" | .layers => "layers"

def argSortJs : Effect4.Program.ArgSort → String
  | .child fam => lit ("child:" ++ famJs fam)
  | .term => lit "term" | .cause => lit "cause" | .op => lit "op" | .nat => lit "nat"
  | .mode => lit "mode" | .bool => lit "bool" | .key => lit "key" | .decision => lit "decision"
  | .optTy => lit "optTy" | .forkOptions => lit "forkOptions" | .optTerm => lit "optTerm"
  | .lit => lit "lit" | .path => lit "path"

def rowJs' (row : Effect4.Codegen.Templates.Row) : Except String String := do
  let fixed ← row.fixed.mapM fun (i, p) => do
    let p ← (argPatJs p).mapError fun why => s!"row {row.ctor}: {why}"
    pure ("[" ++ toString i ++ "," ++ p ++ "]")
  let closed := match row.out with
    | .tpl t => listsClosed t
    | .stmt t => listsClosedStmt t
    | .refuse _ => true
  unless closed do
    throw s!"row {row.ctor}: a statement list that ends in a captured rest"
  let out := match row.out with
    | .tpl t => tagged "tpl" [("tpl", tplJs t)]
    | .stmt t => tagged "stmt" [("stmt", stmtTplJs t), ("declares", toString t.declares)]
    | .refuse name => tagged "refuse" [("name", lit name)]
  let sorts := (Effect4.Program.argSorts row.fam row.ctor).getD []
  let depth := sorts.zipIdx.map fun (sort, i) => depthJs row.fam sort (row.out.levelAt i)
  pure (obj [("fam", lit (famJs row.fam)), ("ctor", lit row.ctor), ("fixed", arr fixed),
    ("depth", arr depth), ("out", out)])

/-- The four families read through rows, with their Lean names in the closed world. -/
def readFamilies : List (Effect4.Program.EffFam × Name) :=
  [(.eff, `Effect4.Program.Eff), (.action, `Effect4.Program.ActionTerm),
   (.layer, `Effect4.Program.LayerTerm), (.stmt, `Effect4.Program.Stmt)]

def templateTypes : String :=
  "export type Fam = \"eff\" | \"stmt\" | \"stmts\" | \"effs\" | \"action\" | \"layer\" | \"layers\"\n" ++
  "export type ArgSort = `child:${Fam}` | \"term\" | \"cause\" | \"op\" | \"nat\" | \"mode\" | \"bool\" | \"key\" | \"decision\" | \"optTy\" | \"forkOptions\" | \"optTerm\" | \"lit\" | \"path\"\n" ++
  "export type Tpl =\n" ++
  "  | { readonly _tag: \"hole\" | \"strHole\" | \"intHole\" | \"arrHole\"; readonly i: number }\n" ++
  "  | { readonly _tag: \"binderRef\"; readonly k: number }\n" ++
  "  | { readonly _tag: \"ident\"; readonly name: string }\n" ++
  "  | { readonly _tag: \"str\"; readonly value: string }\n" ++
  "  | { readonly _tag: \"int\"; readonly value: number }\n" ++
  "  | { readonly _tag: \"bool\"; readonly value: boolean }\n" ++
  "  | { readonly _tag: \"call\"; readonly head: Tpl; readonly args: ReadonlyArray<Tpl> }\n" ++
  "  | { readonly _tag: \"callSpread\"; readonly head: Tpl; readonly i: number }\n" ++
  "  | { readonly _tag: \"arr\"; readonly items: ReadonlyArray<Tpl> }\n" ++
  "  | { readonly _tag: \"object\"; readonly fields: ReadonlyArray<readonly [string, Tpl]> }\n" ++
  "  | { readonly _tag: \"arrow\"; readonly body: Tpl }\n" ++
  "  | { readonly _tag: \"lambda\"; readonly binders: ReadonlyArray<number>; readonly body: Tpl }\n" ++
  "  | { readonly _tag: \"cond\"; readonly test: Tpl; readonly yes: Tpl; readonly no: Tpl }\n" ++
  "  | { readonly _tag: \"method\"; readonly target: Tpl; readonly name: string; readonly args: ReadonlyArray<Tpl> }\n" ++
  "  | { readonly _tag: \"arrowBlock\"; readonly binders: ReadonlyArray<number>; readonly body: StmtTpls }\n" ++
  "  | { readonly _tag: \"generator\"; readonly body: StmtTpls }\n" ++
  "/** A statement list: one captured list, or its statements in order. */\n" ++
  "export type StmtTpls = ReadonlyArray<StmtTpl> | { readonly _tag: \"hole\"; readonly i: number }\n" ++
  "export type StmtTpl =\n" ++
  "  | { readonly _tag: \"letInit\"; readonly k: number; readonly value: Tpl; readonly ann: number | null }\n" ++
  "  | { readonly _tag: \"assign\" | \"constYield\"; readonly k: number; readonly value: Tpl }\n" ++
  "  | { readonly _tag: \"ret\" | \"exprStmt\" | \"yieldDiscard\"; readonly value: Tpl }\n" ++
  "  | { readonly _tag: \"ifElse\"; readonly test: Tpl; readonly thenB: StmtTpls; readonly elseB: StmtTpls }\n" ++
  "  | { readonly _tag: \"whileTrue\"; readonly body: StmtTpls }\n" ++
  "  | { readonly _tag: \"breakTo\" }\n" ++
  "export type ArgPat =\n" ++
  "  | { readonly _tag: \"term\"; readonly value: unknown }\n" ++
  "  | { readonly _tag: \"bool\" | \"daemon\"; readonly value: boolean }\n" ++
  "  | { readonly _tag: \"mode\"; readonly value: \"joinEffect\" | \"awaitValue\" }\n" ++
  "  | { readonly _tag: \"decisionBool\" | \"decisionOption\" | \"decisionTag\" | \"optTermNone\" | \"optTermSome\" | \"optTyNone\" | \"optTySome\" }\n" ++
  "export type Depth = { readonly _tag: \"rel\"; readonly k: number } | { readonly _tag: \"closed\" }\n" ++
  "export interface TemplateRow {\n" ++
  "  readonly fam: Fam\n  readonly ctor: string\n" ++
  "  readonly fixed: ReadonlyArray<readonly [number, ArgPat]>\n" ++
  "  readonly depth: ReadonlyArray<Depth>\n" ++
  "  readonly out:\n" ++
  "    | { readonly _tag: \"tpl\"; readonly tpl: Tpl }\n" ++
  "    | { readonly _tag: \"stmt\"; readonly stmt: StmtTpl; readonly declares: number }\n" ++
  "    | { readonly _tag: \"refuse\"; readonly name: string }\n}\n" ++
  "export const rowsOf = (fam: Fam): ReadonlyArray<TemplateRow> => (templates.rows as ReadonlyArray<TemplateRow>).filter((row) => row.fam === fam)\n" ++
  "export const argSortsOf = (fam: Fam, ctor: string): ReadonlyArray<ArgSort> | undefined =>\n" ++
  "  (templates.argSorts as Record<string, Record<string, ReadonlyArray<ArgSort>>>)[fam]?.[ctor]\n" ++
  "export const argNamesOf = (fam: Fam, ctor: string): ReadonlyArray<string> | undefined =>\n" ++
  "  (templates.argNames as Record<string, Record<string, ReadonlyArray<string>>>)[fam]?.[ctor]\n" ++
  "export const programHeads: ReadonlyArray<string> = templates.programHeads\n" ++
  "export const genHead: string = templates.genHead\n"

def emitTemplates (fs : List Family) : Except String String := do
  let rows ← table.mapM rowJs'
  let perFamily (f : Effect4.Program.EffFam × Name → Except String (List (String × String))) :
      Except String String := do
    let entries ← readFamilies.mapM fun entry => do
      pure (famJs entry.1, obj (← f entry))
    pure (obj entries)
  let sorts ← perFamily fun (fam, _) =>
    (Effect4.Program.ctorNames fam).mapM fun ctor =>
      match Effect4.Program.argSorts fam ctor with
      | some sorts => .ok (ctor, arr (sorts.map argSortJs))
      | none => .error s!"no argument sorts for {famJs fam}.{ctor}"
  let names ← perFamily fun (fam, leanName) =>
    match fs.find? (·.spec.leanName == leanName) with
    | none => .error s!"{leanName} is not among the families"
    | some family =>
      if family.ctors.map (·.short) != Effect4.Program.ctorNames fam then
        .error s!"{leanName}: the family's constructors are not `ctorNames`"
      else .ok (family.ctors.map fun c => (c.short, arr (c.args.map fun (name, _) => lit name)))
  pure (emitTable "templates" (obj [("rows", arr rows), ("argSorts", sorts), ("argNames", names),
    ("programHeads", arr (Effect4.Program.programHeads.map lit)), ("genHead", lit genHead)]) ++
    templateTypes)

mutual
  /-- The identifiers a skeleton writes: with the leaf printers' own, the printer's whole
  vocabulary of reserved names. -/
  def tplIdents : Tpl → List String
    | .ident name => [name]
    | .call head args | .method head _ args => tplIdents head ++ tplsIdents args
    | .callSpread head _ => tplIdents head
    | .arr items => tplsIdents items
    | .object fields => fieldsIdents fields
    | .arrow body | .lambda _ body => tplIdents body
    | .cond test yes no => tplIdents test ++ tplIdents yes ++ tplIdents no
    | .arrowBlock _ body | .generator body => stmtTplsIdents body
    | _ => []
  def tplsIdents : Tpls → List String
    | .nil => []
    | .cons head tail => tplIdents head ++ tplsIdents tail
  def fieldsIdents : Fields → List String
    | .nil => []
    | .cons _ value tail => tplIdents value ++ fieldsIdents tail
  def stmtTplIdents : StmtTpl → List String
    | .letInit _ value _ | .assign _ value | .ret value | .exprStmt value
    | .constYield _ value | .yieldDiscard value => tplIdents value
    | .ifElse test thenB elseB => tplIdents test ++ stmtTplsIdents thenB ++ stmtTplsIdents elseB
    | .whileTrue body => stmtTplsIdents body
    | .breakTo => []
  def stmtTplsIdents : StmtTpls → List String
    | .nil | .hole _ => []
    | .cons head tail => stmtTplIdents head ++ stmtTplsIdents tail
end

/-- Every identifier the table's skeletons write. -/
def tableIdents : List String :=
  (table.flatMap fun row => match row.out with
    | .tpl t => tplIdents t
    | .stmt t => stmtTplIdents t
    | .refuse _ => []).eraseDups

end Templates

/-! ## The address, and the cross-check against the printer -/

/-- The exact host every generated module is checked against. Its library pins are the
first half of the address every generated file is stamped with. -/
private def hostPin : TypeScript.HostPin :=
  { typescript := "7.0.2"
    languageService := some "@effect/tsgo@0.38.0"
    runtime := "node 22 --experimental-strip-types"
    libraries := ["effect@4.0.0-rc.112"] }

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
  let address := " + ".intercalate (hostPin.libraries ++ ["lean4-typescript@" ++ tsRev])
  -- the printer's vocabulary: the identifiers the table's skeletons write (data) and the leaf
  -- printers' own literals
  let printed := (tableIdents
    ++ identLiterals (← IO.FS.readFile "src/Effect4/Codegen/PrintLeaf.lean")).eraseDups
  -- readRunIn consumes Effect.void only as its fixed block return, not as an
  -- effect head, and printTupleArgs spells a saved tuple request's components with
  -- the fst/snd atoms (source-repairs §18). Check those nested literals in both
  -- directions as well.
  let expectedIdents := Effect4.Program.reserved ++ ["Effect.void", "fst", "snd"]
  let extraInPrint := missingFrom printed expectedIdents
  let extraInHeads := missingFrom expectedIdents printed
  unless extraInPrint.isEmpty && extraInHeads.isEmpty do
    throw (IO.userError s!"TsGen: the reserved heads and the printer's identifiers (the table's skeletons, PrintLeaf.lean) differ: printed only {extraInPrint}; in reserved only {extraInHeads}")
  -- the package tables transcribe pinned vendor sources; the Makefile's `gen-ts` rule names
  -- them as prerequisites, so a change under vendor/ re-cuts every file this tool writes
  let stamp := Tools.GeneratedStamp.note "tools/Tools/TsGen.lean"
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
  match emitTemplates fs with
  | .ok text => IO.FS.writeFile (out / "templates.gen.ts") (stampHeader ++ text)
  | .error why => throw (IO.userError s!"TsGen: templates: {why}")
  let kinds := fs.map fun f => match kindOf f with
    | .enum => "literals" | .struct => "struct" | .consList _ => "array" | .tagged => "tagged"
  IO.println s!"TsGen: {fs.length} families ({(kinds.filter (· == "tagged")).length} tagged, {(kinds.filter (· == "literals")).length} literals, {(kinds.filter (· == "struct")).length} struct, {(kinds.filter (· == "array")).length} array), {fs.foldl (fun n f => n + f.ctors.length) 0} constructors; profile {Effect4.Program.reserved.length} heads, {atomRows.length} atoms, {allNativeOps.length} rows; packages {Effect4.Program.Packages.all.length} tables, {Effect4.Program.Packages.all.foldl (fun n p => n + p.rows.length) 0} rows, address {address}"
  IO.println s!"wrote eff.gen.ts, json.gen.ts, profile.gen.ts, taxonomy.gen.ts, forms.gen.ts, wire.gen.ts, packages.gen.ts, templates.gen.ts under {out}"
