import Lean
import Effect4.Program.Native
import Effect4.Store.Canonical

/-!
# EffGen — the Eff program IR, read off the Lean environment, written as OCaml

    lake env lean -M 4096 --run src/OCaml5/Tools/EffGen.lean ocaml/eff

Writes into `<outdir>`:

* `eff_types.ml`    — one OCaml variant or record per Lean inductive or structure of the
                      closed world below, constructors in the environment's declaration order,
                      with `ctor_index_<t>`, `ctor_name_<t>`, `ctor_names_<t>` per type;
* `eff_wire.ml`     — the canonical byte encoding (`src/Effect4/Store/Canonical.lean` framing,
                      constructor tag 10 with the index as a `Nat` frame) and its exact,
                      length-directed decoder, per type, over the hand-written `Eff_frame`;
* `eff_json.ml`     — the JSON printer (a printer only) per type, over `Eff_json_text`;
* `eff_native.ml`   — the native alphabet as data: the atom typing table (verified here against
                      `nativeAtomTy` on probes), every `NativeOp` value with its `Row`, the
                      signature's scope key;
* `eff_manifest.txt` — one line per family: constructor names, arities and argument carriers;
* `goldens/<name>.{bin,json,ty}` and `goldens/corpus.txt` — the corpus below, encoded by the
                      rule the Lean side states (`V.bytes`), printed, and typed by
                      `Effect4.Program.typeOf` at the native signature.

What is derived and what is written by hand, precisely:

* the *families* (which Lean types are mirrored, in which mutual groups, at which parameter
  instantiation) are the list `blocks` — a decision, written here;
* every constructor name, order, arity and argument type is read from the environment
  (`InductiveVal.ctors`, `forallTelescope` on each constructor's type);
* the corpus programs and their `V` conversions are written by hand, but every constructor
  name in a `V.ctor` is a `` ``double-backtick `` name resolved at elaboration time and its
  index is looked up in the environment at run time — no index is typed by hand;
* the atom table is data in this file, checked against `nativeAtomTy` by evaluation on every
  row and on refusal probes before anything is written; a disagreement aborts the run.

This is a tool (`IO`, `Lean.Meta`); it is not part of any audited library.
-/

open Lean Meta
open Effect4.Program
open Effect4.Supervision (MaskMode ForkOptions ObserverMode)
open Effect4 (FinalizerStrategy ServiceKey)
open Effect4.Machine (FnName)

namespace EffGen

/-! ## OCaml carriers -/

/-- The OCaml type an argument or field is carried by. -/
inductive OTy
  | int | bool | string | unit
  | option (a : OTy)
  | list (a : OTy)
  | prod (a b : OTy)
  | named (n : String)
deriving Repr, BEq, Inhabited

mutual
partial def OTy.render : OTy → String
  | .int => "int"
  | .bool => "bool"
  | .string => "string"
  | .unit => "unit"
  | .option a => a.renderArg ++ " option"
  | .list a => a.renderArg ++ " list"
  | .prod a b => a.renderArg ++ " * " ++ b.renderArg
  | .named n => n
/-- As a constructor argument or a type-constructor argument: products parenthesised. -/
partial def OTy.renderArg : OTy → String
  | .prod a b => "(" ++ OTy.render (.prod a b) ++ ")"
  | t => t.render
end

/-- The OCaml constructor of `<Type>.<ctor>`: the type's OCaml name capitalised, an underscore,
the Lean constructor name verbatim. -/
def octor (oname short : String) : String := oname.capitalize ++ "_" ++ short

/-- The OCaml record field of `<Type>.<field>`. -/
def ofield (oname field : String) : String := oname ++ "_" ++ field

def shortName : Name → String
  | .str _ s => s
  | n => n.toString

/-- `(0, x₀), (1, x₁), …` -/
def enumL {α : Type} (xs : List α) : List (Nat × α) := (List.range xs.length).zip xs

/-! ## The closed world -/

structure Spec where
  leanName : Name
  oname : String
  /-- The OCaml carrier of each type parameter, by position: the instantiation the mirror is
  taken at (`Eff NativeOp`). Parameters without a carrier (instance arguments) get none; a
  field that mentions one is a refusal. -/
  params : List OTy := []

def natOp : OTy := .named "native_op"

/-- The families, grouped as the OCaml `type … and …` groups are emitted: a Lean mutual block
is one group. Order is dependency order. -/
def blocks : List (List Spec) :=
  [ [⟨`Effect4.Program.Ty, "ty", []⟩]
  , [⟨`Effect4.Program.Lit, "lit", []⟩]
  , [⟨`Effect4.Program.Term, "term", []⟩, ⟨`Effect4.Program.Terms, "terms", []⟩]
  , [⟨`Effect4.Program.CauseTerm, "cause_term", []⟩]
  , [⟨`Effect4.Supervision.MaskMode, "mask_mode", []⟩]
  , [⟨`Effect4.Supervision.ForkOptions, "fork_options", []⟩]
  , [⟨`Effect4.Supervision.ObserverMode, "observer_mode", []⟩]
  , [⟨`Effect4.FinalizerStrategy, "finalizer_strategy", []⟩]
  , [⟨`Effect4.Machine.FnName, "fn_name", []⟩]
  , [⟨`Effect4.Program.NativeOp, "native_op", []⟩]
  , [ ⟨`Effect4.Program.Eff, "eff", [natOp]⟩, ⟨`Effect4.Program.Stmt, "stmt", [natOp]⟩
    , ⟨`Effect4.Program.Stmts, "stmts", [natOp]⟩, ⟨`Effect4.Program.Effs, "effs", [natOp]⟩
    , ⟨`Effect4.Program.ActionTerm, "action_term", [natOp]⟩ ]
  , [⟨`Effect4.Program.RowKind, "row_kind", []⟩]
  , [⟨`Effect4.Program.RowShape, "row_shape", []⟩]
  , [⟨`Effect4.ServiceName, "service_name", []⟩]
  , [⟨`Effect4.ServiceTypeCode, "service_type_code", []⟩]
  , [⟨`Effect4.ServiceKey, "service_key", []⟩]
  , [⟨`Effect4.Program.Row, "row", []⟩]
  , [⟨`Effect4.Program.EffTy, "eff_ty", []⟩] ]

def allSpecs : List Spec := blocks.flatten

/-- The carrier of a Lean type expression. `Effect4.Row α` (a canonical list with a proof
field) is carried as `α list`: the one non-structural rule, for `EffTy.requires`. -/
partial def ocamlTy (pm : List (FVarId × OTy)) (e : Expr) : MetaM OTy := do
  let e ← whnfR e
  match e with
  | .fvar id =>
    match pm.find? (·.1 == id) with
    | some (_, t) => pure t
    | none => throwError "EffGen: a field mentions a parameter with no OCaml carrier: {e}"
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let .const n _ := fn | throwError "EffGen: no OCaml carrier for {e}"
    if n == ``Nat then pure .int
    else if n == ``Bool then pure .bool
    else if n == ``String then pure .string
    else if n == ``Unit || n == ``PUnit then pure .unit
    else if n == ``Option then pure (.option (← ocamlTy pm args[0]!))
    else if n == ``List then pure (.list (← ocamlTy pm args[0]!))
    else if n == ``Prod then pure (.prod (← ocamlTy pm args[0]!) (← ocamlTy pm args[1]!))
    else if n == `Effect4.Row then pure (.list (← ocamlTy pm args[0]!))
    else match allSpecs.find? (·.leanName == n) with
      | some s => pure (.named s.oname)
      | none => throwError "EffGen: no OCaml carrier for {e} (head {n})"

structure Ctor where
  name : Name
  short : String
  args : List (String × OTy)
deriving Inhabited

structure Family where
  spec : Spec
  isStruct : Bool
  ctors : List Ctor

/-- `Effect4.Program.Term`, unambiguous beside `Lean.Term`. -/
abbrev PTerm := Effect4.Program.Term

def readFamily (spec : Spec) : MetaM Family := do
  let env ← getEnv
  let info ← getConstInfoInduct spec.leanName
  let isStruct := isStructure env spec.leanName
  let ctors ← info.ctors.mapM fun c => do
    let ci ← getConstInfoCtor c
    forallTelescope ci.type fun xs _ => do
      let pm := (List.range info.numParams).filterMap fun i =>
        match spec.params[i]? with
        | some t => some (xs[i]!.fvarId!, t)
        | none => none
      let mut args : Array (String × OTy) := #[]
      for f in xs[info.numParams:] do
        let t ← inferType f
        if ← isProp t then continue
        let nm ← f.fvarId!.getUserName
        args := args.push (nm.toString, ← ocamlTy pm t)
      pure { name := c, short := shortName c, args := args.toList }
  pure { spec, isStruct, ctors }

def readBlocks : MetaM (List (List Family)) := blocks.mapM (·.mapM readFamily)

/-! ## Text helpers -/

def hex4 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "".pushn '0' (4 - s.length) ++ s

/-- A JSON string: `"` and `\` escaped, control characters as `\n \r \t \b \f` or `\u00XX`,
everything else verbatim. The OCaml renderer (`eff_json_text.ml`) follows the same rule byte
for byte. -/
def jsonStr (s : String) : String :=
  let esc (c : Char) : String :=
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n" else if c == '\r' then "\\r" else if c == '\t' then "\\t"
    else if c.toNat == 8 then "\\b" else if c.toNat == 12 then "\\f"
    else if c.toNat < 0x20 then "\\u" ++ hex4 c.toNat else c.toString
  "\"" ++ String.join (s.toList.map esc) ++ "\""

/-- An OCaml string literal. -/
def ostr (s : String) : String :=
  let esc (c : Char) : String :=
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c.toNat < 0x20 || c.toNat == 0x7f then
      let d := toString c.toNat
      "\\" ++ "".pushn '0' (3 - d.length) ++ d
    else c.toString
  "\"" ++ String.join (s.toList.map esc) ++ "\""

def header (what : String) : String :=
  "(* GENERATED by src/OCaml5/Tools/EffGen.lean — regenerate: lake env lean --run src/OCaml5/Tools/EffGen.lean <outdir>. Do not edit. *)\n" ++
  "(* " ++ what ++ " *)\n\n"

def ctorPat (oname : String) (c : Ctor) : String :=
  if c.args.isEmpty then octor oname c.short else octor oname c.short ++ " _"

def argNames (c : Ctor) : List String := (List.range c.args.length).map fun i => s!"a{i}"

def ctorPatNamed (oname : String) (c : Ctor) : String :=
  match c.args with
  | [] => octor oname c.short
  | [_] => octor oname c.short ++ " a0"
  | _ => octor oname c.short ++ " (" ++ ", ".intercalate (argNames c) ++ ")"

def ctorApp (oname : String) (c : Ctor) (args : List String) : String :=
  match args with
  | [] => octor oname c.short
  | [a] => octor oname c.short ++ " " ++ a
  | _ => octor oname c.short ++ " (" ++ ", ".intercalate args ++ ")"

/-! ## eff_types.ml -/

def emitTypeDecl (first : Bool) (f : Family) : String :=
  let kw := if first then "type" else "and"
  let o := f.spec.oname
  if f.isStruct then
    let c := f.ctors.head!
    let fields := c.args.map fun (nm, t) => "  " ++ ofield o nm ++ " : " ++ t.render ++ ";"
    kw ++ " " ++ o ++ " = {\n" ++ "\n".intercalate fields ++ "\n}\n"
  else
    let arms := f.ctors.map fun c =>
      if c.args.isEmpty then "  | " ++ octor o c.short
      else "  | " ++ octor o c.short ++ " of " ++ " * ".intercalate (c.args.map fun (_, t) => t.renderArg)
    kw ++ " " ++ o ++ " =\n" ++ "\n".intercalate arms ++ "\n"

def emitTypeTables (f : Family) : String :=
  let o := f.spec.oname
  if f.isStruct then
    let c := f.ctors.head!
    s!"let ctor_index_{o} (_ : {o}) : int = 0\n" ++
    s!"let ctor_name_{o} (_ : {o}) : string = {ostr c.short}\n" ++
    s!"let ctor_names_{o} : string list = [{ostr c.short}]\n" ++
    s!"let field_names_{o} : string list = [" ++ "; ".intercalate (c.args.map fun (nm, _) => ostr nm) ++ "]\n\n"
  else
    let idx := (enumL f.ctors).map fun (i, c) => s!"  | {ctorPat o c} -> {i}"
    let nms := f.ctors.map fun c => s!"  | {ctorPat o c} -> {ostr c.short}"
    s!"let ctor_index_{o} : {o} -> int = function\n" ++ "\n".intercalate idx ++ "\n" ++
    s!"let ctor_name_{o} : {o} -> string = function\n" ++ "\n".intercalate nms ++ "\n" ++
    s!"let ctor_names_{o} : string list = [" ++ "; ".intercalate (f.ctors.map fun c => ostr c.short) ++ "]\n\n"

def emitTypes (bs : List (List Family)) : String :=
  header "Eff_types: the Eff program IR of lean4-effect4 (src/Effect4/Program/{Eff,Native,Typing}.lean, Machine/Supervision.lean, Machine/Scope.lean, Machine/Stores.lean, Machine/Key.lean) as OCaml variants and records. Constructor order is the Lean declaration order and ctor_index_<t> is that order (by construction: read from InductiveVal.ctors). Constructors are named <Type>_<leanCtor>, record fields <type>_<leanField>. Lean Nat is OCaml int: values above max_int (2^62 - 1) have no carrier here." ++
  "\n".intercalate (bs.map fun b =>
    "\n".intercalate ((enumL b).map fun (i, f) => emitTypeDecl (i == 0) f) ++ "\n" ++
    String.join (b.map emitTypeTables))

/-! ## eff_wire.ml -/

partial def emitOf : OTy → String → String
  | .int, x => s!"Eff_frame.emit_nat b {x}"
  | .bool, x => s!"Eff_frame.emit_bool b {x}"
  | .string, x => s!"Eff_frame.emit_string b {x}"
  | .unit, x => s!"Eff_frame.emit_unit b {x}"
  | .option a, x => s!"Eff_frame.emit_option b (fun b y -> {emitOf a "y"}) {x}"
  | .list a, x => s!"Eff_frame.emit_list b (fun b y -> {emitOf a "y"}) {x}"
  | .prod a c, x => s!"Eff_frame.emit_pair b (fun b y -> {emitOf a "y"}) (fun b y -> {emitOf c "y"}) {x}"
  | .named n, x => s!"emit_{n} b {x}"

partial def decoderOf : OTy → String
  | .int => "Eff_frame.decode_nat"
  | .bool => "Eff_frame.decode_bool"
  | .string => "Eff_frame.decode_string"
  | .unit => "Eff_frame.decode_unit"
  | .option a => s!"(Eff_frame.decode_option {decoderOf a})"
  | .list a => s!"(Eff_frame.decode_list {decoderOf a})"
  | .prod a b => s!"(Eff_frame.decode_pair {decoderOf a} {decoderOf b})"
  | .named n => s!"decode_{n}"

def emitEmitter (first : Bool) (f : Family) : String :=
  let kw := if first then "let rec" else "and"
  let o := f.spec.oname
  if f.isStruct then
    let c := f.ctors.head!
    let body := "; ".intercalate (c.args.map fun (nm, t) => emitOf t s!"r.{ofield o nm}")
    let body := if c.args.isEmpty then "()" else body
    s!"{kw} emit_{o} (b : Buffer.t) (r : {o}) : unit =\n  Eff_frame.emit_ctor b 0 (fun b -> {body})\n"
  else
    let arms := (enumL f.ctors).map fun (i, c) =>
      let names := argNames c
      let body := "; ".intercalate ((c.args.zip names).map fun ((_, t), a) => emitOf t a)
      if c.args.isEmpty then s!"  | {octor o c.short} -> Eff_frame.emit_ctor b {i} (fun _ -> ())"
      else s!"  | {ctorPatNamed o c} -> Eff_frame.emit_ctor b {i} (fun b -> {body})"
    s!"{kw} emit_{o} (b : Buffer.t) (v : {o}) : unit =\n  match v with\n" ++ "\n".intercalate arms ++ "\n"

/-- The decoder arm of one constructor: the arguments decoded in order inside `[p, e)`, the
payload consumed exactly. -/
def decodeArm (i : Nat) (c : Ctor) (build : List String → String) : String :=
  let names := argNames c
  let rec nest (rest : List ((String × OTy) × String)) (depth : Nat) : String :=
    let pad := "".pushn ' ' (6 + 2 * depth)
    match rest with
    | [] => s!"{pad}if p = e then Some ({build names}, next) else None"
    | ((_, t), a) :: more =>
      s!"{pad}(match {decoderOf t} s p e with\n{pad} | None -> None\n{pad} | Some ({a}, p) ->\n" ++
      nest more (depth + 1) ++ ")"
  s!"    | {i} ->\n" ++ nest (c.args.zip names) 0

def emitDecoder (first : Bool) (f : Family) : String :=
  let kw := if first then "let rec" else "and"
  let o := f.spec.oname
  let arms :=
    if f.isStruct then
      let c := f.ctors.head!
      [decodeArm 0 c fun names =>
        if c.args.isEmpty then "()"
        else "{ " ++ "; ".intercalate ((c.args.zip names).map fun ((nm, _), a) => s!"{ofield o nm} = {a}") ++ " }"]
    else (enumL f.ctors).map fun (i, c) => decodeArm i c (ctorApp o c)
  s!"{kw} decode_{o} (s : string) (pos : int) (limit : int) : ({o} * int) option =\n" ++
  "  match Eff_frame.read_ctor s pos limit with\n  | None -> None\n  | Some (i, p, e, next) ->\n    (match i with\n" ++
  "\n".intercalate arms ++ "\n    | _ -> None)\n"

def emitWire (bs : List (List Family)) : String :=
  header "Eff_wire: the canonical bytes of every carrier of Eff_types, and the exact decoder. Rule (src/Effect4/Store/Canonical.lean): framed tag payload = tag :: be64 (length payload) ++ payload; Unit 9 [], Bool 1 [0|1], Nat 2 base-256 big-endian no leading zero, String 3 utf8, List 4 concat, none 6 [] / some 7 x, pair 5 a++b, constructor i of an inductive 10 (encode i ++ args), a structure as constructor 0 with its fields in order. Decoding is length-directed and exact: a wrong tag, a bad index, a non-canonical Nat, invalid UTF-8, a short or long payload, or (for the _exact forms) trailing bytes are refusals (by construction: every arm checks p = e; tested: goldens, property test). encode_<t> raises Invalid_argument on a negative int or a string that is not valid UTF-8 (values outside the Lean image)." ++
  "open Eff_types\n\n" ++
  "\n".intercalate (bs.map fun b =>
    String.join ((enumL b).map fun (i, f) => emitEmitter (i == 0) f) ++ "\n" ++
    String.join (b.map fun f => s!"let encode_{f.spec.oname} (v : {f.spec.oname}) : string = Eff_frame.to_string emit_{f.spec.oname} v\n") ++ "\n" ++
    String.join ((enumL b).map fun (i, f) => emitDecoder (i == 0) f) ++ "\n" ++
    String.join (b.map fun f =>
      s!"let decode_{f.spec.oname}_exact (s : string) : {f.spec.oname} option = Eff_frame.exact decode_{f.spec.oname} s\n")) ++
  "\n(* The top level: a program is an Eff over the native alphabet. *)\n" ++
  "let encode_program : eff -> string = encode_eff\n" ++
  "let decode_program : string -> (eff * int) option = fun s -> decode_eff s 0 (String.length s)\n" ++
  "let decode_program_exact : string -> eff option = decode_eff_exact\n"

/-! ## eff_json.ml -/

partial def jsonOf : OTy → String → String
  | .int, x => s!"Eff_json_text.Int {x}"
  | .bool, x => s!"Eff_json_text.Bool {x}"
  | .string, x => s!"Eff_json_text.String {x}"
  | .unit, _ => "Eff_json_text.Array []"
  | .option a, x => s!"(match {x} with None -> Eff_json_text.Null | Some y -> {jsonOf a "y"})"
  | .list a, x => s!"Eff_json_text.Array (List.map (fun y -> {jsonOf a "y"}) {x})"
  | .prod a c, x => s!"(let (y0, y1) = {x} in Eff_json_text.Array [{jsonOf a "y0"}; {jsonOf c "y1"}])"
  | .named n, x => s!"json_{n} {x}"

def emitJsonFn (first : Bool) (f : Family) : String :=
  let kw := if first then "let rec" else "and"
  let o := f.spec.oname
  if f.isStruct then
    let c := f.ctors.head!
    let fields := "; ".intercalate (c.args.map fun (nm, t) => s!"({ostr nm}, {jsonOf t s!"r.{ofield o nm}"})")
    s!"{kw} json_{o} (r : {o}) : Eff_json_text.t =\n  Eff_json_text.Object [{fields}]\n"
  else
    let arms := f.ctors.map fun c =>
      let names := argNames c
      let items := s!"Eff_json_text.String {ostr c.short}" :: (c.args.zip names).map fun ((_, t), a) => jsonOf t a
      s!"  | {ctorPatNamed o c} -> Eff_json_text.Array [{"; ".intercalate items}]"
    s!"{kw} json_{o} (v : {o}) : Eff_json_text.t =\n  match v with\n" ++ "\n".intercalate arms ++ "\n"

def emitJson (bs : List (List Family)) : String :=
  header "Eff_json: the JSON printer of every carrier of Eff_types (a printer only; there is no JSON parser). Rule: a constructor is [\"ctorName\", arg1, ...] with the Lean constructor name; a structure is {\"field\": value} with the Lean field names; lists are arrays; options null / value; unit []; pairs [a, b]; numbers, booleans and strings as themselves. Rendering (Eff_json_text.render) is compact, with the escaping stated there; the Lean side (EffGen.lean, V.json) prints the same bytes (tested: goldens)." ++
  "open Eff_types\n\n" ++
  "\n".intercalate (bs.map fun b =>
    String.join ((enumL b).map fun (i, f) => emitJsonFn (i == 0) f) ++ "\n" ++
    String.join (b.map fun f =>
      s!"let print_{f.spec.oname} (v : {f.spec.oname}) : string = Eff_json_text.render (json_{f.spec.oname} v)\n"))

/-! ## eff_manifest.txt -/

def manifest (bs : List (List Family)) : String :=
  String.join (bs.map fun b => String.join (b.map fun f =>
    let o := f.spec.oname
    if f.isStruct then
      let c := f.ctors.head!
      s!"{f.spec.leanName} ({o}) structure: " ++ " ".intercalate (c.args.map fun (nm, t) => s!"{nm}:{t.render}") ++ "\n"
    else
      s!"{f.spec.leanName} ({o}) inductive: " ++ " ".intercalate (f.ctors.map fun c =>
        if c.args.isEmpty then c.short
        else c.short ++ "(" ++ ",".intercalate (c.args.map fun (_, t) => t.render) ++ ")") ++ "\n"))

/-! ## eff_native.ml — the alphabet as data, rendered from Lean values -/

def tyO : Ty → String
  | .never => octor "ty" "never"
  | .unit => octor "ty" "unit"
  | .nat => octor "ty" "nat"
  | .int => octor "ty" "int"
  | .string => octor "ty" "string"
  | .bool => octor "ty" "bool"
  | .handle target => s!"({octor "ty" "handle"} {ostr target})"
  | .option inner => s!"({octor "ty" "option"} {tyO inner})"
  | .list inner => s!"({octor "ty" "list"} {tyO inner})"
  | .prod l r => s!"({octor "ty" "prod"} ({tyO l}, {tyO r}))"
  | .except e v => s!"({octor "ty" "except"} ({tyO e}, {tyO v}))"
  | .exitOf v e => s!"({octor "ty" "exitOf"} ({tyO v}, {tyO e}))"
  | .causeOf e => s!"({octor "ty" "causeOf"} {tyO e})"
  | .fiberOf v e => s!"({octor "ty" "fiberOf"} ({tyO v}, {tyO e}))"
  | .union l r => s!"({octor "ty" "union"} ({tyO l}, {tyO r}))"

def kindO : RowKind → String
  | .sync => octor "row_kind" "sync"
  | .async => octor "row_kind" "async"
  | .program => octor "row_kind" "program"

def shapeO : RowShape → String
  | .call => octor "row_shape" "call"
  | .value => octor "row_shape" "value"

def keyO (k : ServiceKey) : String :=
  "{ " ++ ofield "service_key" "name" ++ " = { " ++ ofield "service_name" "value" ++ " = " ++
  toString k.name.value ++ " }; " ++
  ofield "service_key" "service" ++ " = { " ++ ofield "service_type_code" "value" ++ " = " ++
  toString k.service.value ++ " } }"

def listO (xs : List String) : String := "[" ++ "; ".intercalate xs ++ "]"

def rowO (r : Row) : String :=
  "{ " ++ "; ".intercalate
    [ ofield "row" "name" ++ " = " ++ ostr r.name
    , ofield "row" "spelling" ++ " = " ++ ostr r.spelling
    , ofield "row" "shape" ++ " = " ++ shapeO r.shape
    , ofield "row" "trailing" ++ " = " ++ listO (r.trailing.map ostr)
    , ofield "row" "kind" ++ " = " ++ kindO r.kind
    , ofield "row" "request" ++ " = " ++ tyO r.request
    , ofield "row" "answer" ++ " = " ++ tyO r.answer
    , ofield "row" "error" ++ " = " ++ tyO r.error
    , ofield "row" "requires" ++ " = " ++ listO (r.requires.map keyO)
    , ofield "row" "cite" ++ " = " ++ ostr r.cite ] ++ " }"

def fnO : FnName → String
  | .incr => octor "fn_name" "incr"
  | .double => octor "fn_name" "double"
  | .zeroWhenPositive => octor "fn_name" "zeroWhenPositive"
  | .noChange => octor "fn_name" "noChange"
  | .takeAndBump => octor "fn_name" "takeAndBump"

def stratO : FinalizerStrategy → String
  | .sequential => octor "finalizer_strategy" "sequential"
  | .parallel => octor "finalizer_strategy" "parallel"

def opO : NativeOp → String
  | .refMake => octor "native_op" "refMake"
  | .refGet => octor "native_op" "refGet"
  | .refSet => octor "native_op" "refSet"
  | .refGetAndSet => octor "native_op" "refGetAndSet"
  | .refSetAndGet => octor "native_op" "refSetAndGet"
  | .refUpdate f => s!"({octor "native_op" "refUpdate"} {fnO f})"
  | .refGetAndUpdate f => s!"({octor "native_op" "refGetAndUpdate"} {fnO f})"
  | .refUpdateAndGet f => s!"({octor "native_op" "refUpdateAndGet"} {fnO f})"
  | .refUpdateSome f => s!"({octor "native_op" "refUpdateSome"} {fnO f})"
  | .refGetAndUpdateSome f => s!"({octor "native_op" "refGetAndUpdateSome"} {fnO f})"
  | .refUpdateSomeAndGet f => s!"({octor "native_op" "refUpdateSomeAndGet"} {fnO f})"
  | .refModify f => s!"({octor "native_op" "refModify"} {fnO f})"
  | .refModifySome f => s!"({octor "native_op" "refModifySome"} {fnO f})"
  | .deferredMake => octor "native_op" "deferredMake"
  | .deferredIsDone => octor "native_op" "deferredIsDone"
  | .deferredPoll => octor "native_op" "deferredPoll"
  | .deferredSucceed => octor "native_op" "deferredSucceed"
  | .deferredFail => octor "native_op" "deferredFail"
  | .deferredAwait => octor "native_op" "deferredAwait"
  | .scopeMake s => s!"({octor "native_op" "scopeMake"} {stratO s})"

def fnNames : List FnName := [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

/-- Every value of `NativeOp`, in declaration order, the parameterised constructors at every
argument. Its length is checked against the environment's constructor table in `main`. -/
def allOps : List NativeOp :=
  [.refMake, .refGet, .refSet, .refGetAndSet, .refSetAndGet] ++
  (fnNames.map NativeOp.refUpdate) ++ (fnNames.map NativeOp.refGetAndUpdate) ++
  (fnNames.map NativeOp.refUpdateAndGet) ++ (fnNames.map NativeOp.refUpdateSome) ++
  (fnNames.map NativeOp.refGetAndUpdateSome) ++ (fnNames.map NativeOp.refUpdateSomeAndGet) ++
  (fnNames.map NativeOp.refModify) ++ (fnNames.map NativeOp.refModifySome) ++
  [.deferredMake, .deferredIsDone, .deferredPoll, .deferredSucceed, .deferredFail, .deferredAwait] ++
  (FinalizerStrategy.all.map NativeOp.scopeMake)

/-- The monomorphic atoms of `nativeAtomTy`, as data: name, argument types, answer. -/
def monoAtoms : List (String × List Ty × Ty) :=
  [ ("succ", [.nat], .nat), ("pred", [.nat], .nat), ("isZero", [.nat], .bool), ("not", [.bool], .bool)
  , ("add", [.nat, .nat], .nat), ("lt", [.nat, .nat], .bool), ("eq", [.nat, .nat], .bool) ]

/-- The polymorphic atoms (`pair`, `fst`, `snd`) as OCaml arms, and the probes that check
them and the refusals against `nativeAtomTy`. -/
def polyArms : List String :=
  [ s!"  | \"pair\", [a; b] -> Some ({octor "ty" "prod"} (a, b))"
  , s!"  | \"fst\", [{octor "ty" "prod"} (a, _)] -> Some a"
  , s!"  | \"snd\", [{octor "ty" "prod"} (_, b)] -> Some b" ]

def atomProbes : List (String × List Ty × Option Ty) :=
  [ ("pair", [.nat, .bool], some (.prod .nat .bool)), ("pair", [.nat, .nat], some (.prod .nat .nat))
  , ("fst", [.prod .nat .bool], some .nat), ("snd", [.prod .nat .bool], some .bool)
  , ("fst", [.nat], none), ("snd", [.nat, .nat], none), ("pair", [.nat], none), ("pair", [], none)
  , ("succ", [.bool], none), ("succ", [], none), ("succ", [.nat, .nat], none), ("add", [.nat], none)
  , ("mul", [.nat, .nat], none), ("not", [.nat], none), ("eq", [.bool, .bool], none)
  , ("lt", [.nat, .bool], none), ("isZero", [.bool], none), ("pred", [.nat, .nat], none) ]

def checkAtoms : Except String Unit := do
  for (n, args, ans) in monoAtoms do
    unless nativeAtomTy n args = some ans do
      throw s!"atom table disagrees with nativeAtomTy on {n}"
    -- every monomorphic row refuses one argument too many and one too few
    unless nativeAtomTy n (args ++ [.nat]) = none do throw s!"nativeAtomTy accepts {n} with an extra argument"
    unless nativeAtomTy n args.tail = none do throw s!"nativeAtomTy accepts {n} with a missing argument"
  for (n, args, ans) in atomProbes do
    unless nativeAtomTy n args = ans do
      throw s!"atom probe disagrees with nativeAtomTy on {n} {repr args}"

def emitNative (nullaryOps fnOps stratOps : Nat) : String :=
  header "Eff_native: the native alphabet as data. atom_ty is nativeAtomTy (src/Effect4/Program/Native.lean): the monomorphic rows are data in EffGen.lean checked against nativeAtomTy by evaluation at generation time, the three polymorphic atoms are fixed arms checked on probes (tested at generation: a disagreement aborts). row_of is NativeOp.row evaluated on every NativeOp value (all_ops, whose length is checked against the constructor table). scope_key is nativeScopeKey." ++
  "open Eff_types\n\n" ++
  "let atom_names : string list = " ++ listO ((monoAtoms.map (ostr ·.1)) ++ [ostr "pair", ostr "fst", ostr "snd"]) ++ "\n\n" ++
  "let atom_ty (name : string) (args : ty list) : ty option =\n  match name, args with\n" ++
  "\n".intercalate (monoAtoms.map fun (n, args, ans) =>
    s!"  | {ostr n}, [{"; ".intercalate (args.map tyO)}] -> Some {tyO ans}") ++ "\n" ++
  "\n".intercalate polyArms ++ "\n  | _ -> None\n\n" ++
  s!"(* {nullaryOps} nullary operations, {fnOps} over every fn_name, {stratOps} over every finalizer_strategy: {allOps.length} values. *)\n" ++
  "let all_ops : native_op list =\n  [ " ++ "\n  ; ".intercalate (allOps.map opO) ++ " ]\n\n" ++
  "let row_of : native_op -> row = function\n" ++
  "\n".intercalate (allOps.map fun op => s!"  | {opO op} ->\n    {rowO op.row}") ++ "\n\n" ++
  "let scope_key : service_key = " ++ keyO nativeScopeKey ++ "\n" ++
  "let ref_ty : ty = " ++ tyO NativeOp.refTy ++ "\n" ++
  "let deferred_ty : ty = " ++ tyO NativeOp.deferredTy ++ "\n" ++
  "let scope_ty : ty = " ++ tyO Ty.scope ++ "\n" ++
  "let context_ty : ty = " ++ tyO Ty.context ++ "\n"

/-! ## Goldens: a generic value tree, serialised by the wire rule and by the JSON rule -/

/-- A Lean value as the wire sees it. `ctor` carries the constructor's full name; its index
is looked up in the environment when the bytes are written. -/
inductive V
  | unit
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | list (xs : List V)
  | none
  | some (x : V)
  | pair (a b : V)
  | ctor (name : Name) (args : List V)
  | struct (name : Name) (fields : List (String × V))

instance : Inhabited V := ⟨.unit⟩

/-- The constructor tag: `Tag.ctor` in the PC's pending edit of `Canonical.lean`; the value
is the wire's, restated here so the tool builds at HEAD. -/
def ctorTag : UInt8 := 10

/-- The byte rule of `src/Effect4/Store/Canonical.lean` (`framed`, `natBytes`, `Tag.*` are the
library's own), with `ctorTag` for a constructor application. -/
partial def V.bytes (idx : Name → Nat) : V → Effect4.Store.Bytes
  | .unit => Effect4.Store.framed Effect4.Store.Tag.unit []
  | .bool b => Effect4.Store.framed Effect4.Store.Tag.bool [if b then 1 else 0]
  | .nat n => Effect4.Store.framed Effect4.Store.Tag.nat (Effect4.Store.natBytes n)
  | .str s => Effect4.Store.framed Effect4.Store.Tag.string s.toUTF8.data.toList
  | .list xs => Effect4.Store.framed Effect4.Store.Tag.list (xs.map (bytes idx)).flatten
  | .none => Effect4.Store.framed Effect4.Store.Tag.none []
  | .some x => Effect4.Store.framed Effect4.Store.Tag.some (bytes idx x)
  | .pair a b => Effect4.Store.framed Effect4.Store.Tag.pair (bytes idx a ++ bytes idx b)
  | .ctor n args =>
    Effect4.Store.framed ctorTag (bytes idx (.nat (idx n)) ++ (args.map (bytes idx)).flatten)
  | .struct _ fields =>
    Effect4.Store.framed ctorTag (bytes idx (.nat 0) ++ (fields.map fun (_, v) => bytes idx v).flatten)

partial def V.json : V → String
  | .unit => "[]"
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .str s => jsonStr s
  | .list xs => "[" ++ ",".intercalate (xs.map json) ++ "]"
  | .none => "null"
  | .some x => json x
  | .pair a b => "[" ++ json a ++ "," ++ json b ++ "]"
  | .ctor n args => "[" ++ ",".intercalate (jsonStr (shortName n) :: args.map json) ++ "]"
  | .struct _ fields => "{" ++ ",".intercalate (fields.map fun (k, v) => jsonStr k ++ ":" ++ json v) ++ "}"

/-- Every constructor name a tree uses (validated against the environment before writing). -/
partial def V.names : V → List Name
  | .list xs => (xs.map names).flatten
  | .some x => names x
  | .pair a b => names a ++ names b
  | .ctor n args => n :: (args.map names).flatten
  | .struct n fields => n :: (fields.map fun (_, v) => names v).flatten
  | _ => []

/-! ### The conversions, one per family, total by pattern matching -/

def tyV : Ty → V
  | .never => .ctor ``Ty.never []
  | .unit => .ctor ``Ty.unit []
  | .nat => .ctor ``Ty.nat []
  | .int => .ctor ``Ty.int []
  | .string => .ctor ``Ty.string []
  | .bool => .ctor ``Ty.bool []
  | .handle target => .ctor ``Ty.handle [.str target]
  | .option inner => .ctor ``Ty.option [tyV inner]
  | .list inner => .ctor ``Ty.list [tyV inner]
  | .prod l r => .ctor ``Ty.prod [tyV l, tyV r]
  | .except e v => .ctor ``Ty.except [tyV e, tyV v]
  | .exitOf v e => .ctor ``Ty.exitOf [tyV v, tyV e]
  | .causeOf e => .ctor ``Ty.causeOf [tyV e]
  | .fiberOf v e => .ctor ``Ty.fiberOf [tyV v, tyV e]
  | .union l r => .ctor ``Ty.union [tyV l, tyV r]

def litV : Lit → V
  | .unit => .ctor ``Lit.unit []
  | .nat n => .ctor ``Lit.nat [.nat n]
  | .bool b => .ctor ``Lit.bool [.bool b]
  | .str s => .ctor ``Lit.str [.str s]

mutual
partial def termV : PTerm → V
  | .var i => .ctor ``Term.var [.nat i]
  | .lit l => .ctor ``Term.lit [litV l]
  | .app atom args => .ctor ``Term.app [.str atom, termsV args]
partial def termsV : Terms → V
  | .nil => .ctor ``Terms.nil []
  | .cons h t => .ctor ``Terms.cons [termV h, termsV t]
end

partial def causeV : CauseTerm → V
  | .fail e => .ctor ``CauseTerm.fail [termV e]
  | .die d => .ctor ``CauseTerm.die [termV d]
  | .interrupt none => .ctor ``CauseTerm.interrupt [.none]
  | .interrupt (some who) => .ctor ``CauseTerm.interrupt [.some (termV who)]
  | .both l r => .ctor ``CauseTerm.both [causeV l, causeV r]

def maskV : MaskMode → V
  | .interruptible => .ctor ``Effect4.Supervision.MaskMode.interruptible []
  | .uninterruptible => .ctor ``Effect4.Supervision.MaskMode.uninterruptible []
  | .inherit => .ctor ``Effect4.Supervision.MaskMode.inherit []

def optionsV (o : ForkOptions) : V :=
  .struct ``Effect4.Supervision.ForkOptions
    [("startImmediately", .bool o.startImmediately), ("daemon", .bool o.daemon), ("maskMode", maskV o.maskMode)]

def modeV : ObserverMode → V
  | .awaitValue => .ctor ``Effect4.Supervision.ObserverMode.awaitValue []
  | .joinEffect => .ctor ``Effect4.Supervision.ObserverMode.joinEffect []

def stratV : FinalizerStrategy → V
  | .sequential => .ctor ``Effect4.FinalizerStrategy.sequential []
  | .parallel => .ctor ``Effect4.FinalizerStrategy.parallel []

def fnV : FnName → V
  | .incr => .ctor ``Effect4.Machine.FnName.incr []
  | .double => .ctor ``Effect4.Machine.FnName.double []
  | .zeroWhenPositive => .ctor ``Effect4.Machine.FnName.zeroWhenPositive []
  | .noChange => .ctor ``Effect4.Machine.FnName.noChange []
  | .takeAndBump => .ctor ``Effect4.Machine.FnName.takeAndBump []

def opV : NativeOp → V
  | .refMake => .ctor ``NativeOp.refMake []
  | .refGet => .ctor ``NativeOp.refGet []
  | .refSet => .ctor ``NativeOp.refSet []
  | .refGetAndSet => .ctor ``NativeOp.refGetAndSet []
  | .refSetAndGet => .ctor ``NativeOp.refSetAndGet []
  | .refUpdate f => .ctor ``NativeOp.refUpdate [fnV f]
  | .refGetAndUpdate f => .ctor ``NativeOp.refGetAndUpdate [fnV f]
  | .refUpdateAndGet f => .ctor ``NativeOp.refUpdateAndGet [fnV f]
  | .refUpdateSome f => .ctor ``NativeOp.refUpdateSome [fnV f]
  | .refGetAndUpdateSome f => .ctor ``NativeOp.refGetAndUpdateSome [fnV f]
  | .refUpdateSomeAndGet f => .ctor ``NativeOp.refUpdateSomeAndGet [fnV f]
  | .refModify f => .ctor ``NativeOp.refModify [fnV f]
  | .refModifySome f => .ctor ``NativeOp.refModifySome [fnV f]
  | .deferredMake => .ctor ``NativeOp.deferredMake []
  | .deferredIsDone => .ctor ``NativeOp.deferredIsDone []
  | .deferredPoll => .ctor ``NativeOp.deferredPoll []
  | .deferredSucceed => .ctor ``NativeOp.deferredSucceed []
  | .deferredFail => .ctor ``NativeOp.deferredFail []
  | .deferredAwait => .ctor ``NativeOp.deferredAwait []
  | .scopeMake s => .ctor ``NativeOp.scopeMake [stratV s]

mutual
partial def effV : Eff NativeOp → V
  | .succeed v => .ctor ``Eff.succeed [termV v]
  | .fail e => .ctor ``Eff.fail [termV e]
  | .failCause c => .ctor ``Eff.failCause [causeV c]
  | .yieldError e => .ctor ``Eff.yieldError [termV e]
  | .sync t => .ctor ``Eff.sync [termV t]
  | .suspend b => .ctor ``Eff.suspend [effV b]
  | .perform op r => .ctor ``Eff.perform [opV op, termV r]
  | .bind f r => .ctor ``Eff.bind [effV f, effV r]
  | .gen body => .ctor ``Eff.gen [stmtsV body]
  | .catchCause b h => .ctor ``Eff.catchCause [effV b, effV h]
  | .matchCause b v c => .ctor ``Eff.matchCause [effV b, effV v, effV c]
  | .onExit b f => .ctor ``Eff.onExit [effV b, effV f]
  | .exit b => .ctor ``Eff.exit [effV b]
  | .uninterruptible b => .ctor ``Eff.uninterruptible [effV b]
  | .interruptible b => .ctor ``Eff.interruptible [effV b]
  | .branch t a b => .ctor ``Eff.branch [termV t, effV a, effV b]
  | .whileLoop i t s b => .ctor ``Eff.whileLoop [termV i, termV t, termV s, effV b]
  | .yieldNow p => .ctor ``Eff.yieldNow [.nat p]
  | .callback op r => .ctor ``Eff.callback [opV op, termV r]
  | .awaitFiber f m => .ctor ``Eff.awaitFiber [termV f, modeV m]
  | .withFiber a => .ctor ``Eff.withFiber [actionV a]
  | .scoped b => .ctor ``Eff.scoped [effV b]
  | .acquireRelease a r => .ctor ``Eff.acquireRelease [effV a, effV r]
  | .choose site l r => .ctor ``Eff.choose [.nat site, effV l, effV r]
partial def stmtV : Stmt NativeOp → V
  | .bindYield e => .ctor ``Stmt.bindYield [effV e]
  | .yieldDiscard e => .ctor ``Stmt.yieldDiscard [effV e]
  | .ret v => .ctor ``Stmt.ret [termV v]
  | .ifElse t a b => .ctor ``Stmt.ifElse [termV t, stmtsV a, stmtsV b]
  | .whileTrue b => .ctor ``Stmt.whileTrue [stmtsV b]
  | .breakLoop => .ctor ``Stmt.breakLoop []
partial def stmtsV : Stmts NativeOp → V
  | .nil => .ctor ``Stmts.nil []
  | .cons h t => .ctor ``Stmts.cons [stmtV h, stmtsV t]
partial def effsV : Effs NativeOp → V
  | .nil => .ctor ``Effs.nil []
  | .cons h t => .ctor ``Effs.cons [effV h, effsV t]
partial def actionV : ActionTerm NativeOp → V
  | .fork p o => .ctor ``ActionTerm.fork [effV p, optionsV o]
  | .forkIn p o s => .ctor ``ActionTerm.forkIn [effV p, optionsV o, termV s]
  | .forkScoped p o => .ctor ``ActionTerm.forkScoped [effV p, optionsV o]
  | .runIn t s => .ctor ``ActionTerm.runIn [termV t, termV s]
  | .interrupt t => .ctor ``ActionTerm.interrupt [termV t]
  | .interruptScoped t => .ctor ``ActionTerm.interruptScoped [termV t]
  | .interruptAll ts none => .ctor ``ActionTerm.interruptAll [termV ts, .none]
  | .interruptAll ts (some who) => .ctor ``ActionTerm.interruptAll [termV ts, .some (termV who)]
  | .awaitAll ts => .ctor ``ActionTerm.awaitAll [termV ts]
  | .awaitAllFailFast ts => .ctor ``ActionTerm.awaitAllFailFast [termV ts]
  | .snapshotChildren => .ctor ``ActionTerm.snapshotChildren []
  | .awaitNewChildren s => .ctor ``ActionTerm.awaitNewChildren [termV s]
  | .raceAll es => .ctor ``ActionTerm.raceAll [effsV es]
  | .setContext c => .ctor ``ActionTerm.setContext [termV c]
  | .getContext => .ctor ``ActionTerm.getContext []
  | .getId => .ctor ``ActionTerm.getId []
  | .closeScope s e => .ctor ``ActionTerm.closeScope [termV s, termV e]
end

def keyV (k : ServiceKey) : V :=
  .struct ``Effect4.ServiceKey
    [ ("name", .struct ``Effect4.ServiceName [("value", .nat k.name.value)])
    , ("service", .struct ``Effect4.ServiceTypeCode [("value", .nat k.service.value)]) ]

def effTyV (t : EffTy) : V :=
  .struct ``EffTy [("answer", tyV t.answer), ("error", tyV t.error), ("requires", .list (t.requires.elems.map keyV))]

/-! ## The corpus -/

namespace Corpus

abbrev P := Eff NativeOp

def ts (xs : List PTerm) : Terms := xs.foldr .cons .nil
def n (k : Nat) : PTerm := .lit (.nat k)
def v (i : Nat) : PTerm := .var i
def u : PTerm := .lit .unit
def opts : ForkOptions := ⟨false, false, .inherit⟩
def st (xs : List (Stmt NativeOp)) : Stmts NativeOp := xs.foldr .cons .nil
def es (xs : List P) : Effs NativeOp := xs.foldr .cons .nil
def binds (steps : List P) (last : P) : P := steps.foldr .bind last

/-- `yieldNow 0` then `7`. -/
def child : P := .bind (.yieldNow 0) (.succeed (n 7))

def p42 : P := .succeed (n 42)
def pBind : P := .bind (.succeed (n 1)) (.succeed (.app "succ" (ts [v 0])))
def pFork : P := .bind (.withFiber (.fork child opts)) (.awaitFiber (v 0) .awaitValue)
def pTwo : P :=
  binds [.withFiber (.fork child opts), .withFiber (.fork child ⟨true, false, .interruptible⟩),
         .awaitFiber (v 0) .awaitValue] (.awaitFiber (v 1) .awaitValue)
def pAwait : P := .bind (.perform .deferredMake u) (.perform .deferredAwait (v 0))
def pGen : P := .gen (st [.bindYield (.succeed (n 1)), .ret (.app "succ" (ts [v 0]))])
def pWhile : P := .whileLoop (n 0) (.app "lt" (ts [v 0, n 3])) (.app "succ" (ts [v 0])) (.yieldNow 0)
def pCatch : P := .catchCause (.fail (n 1)) (.succeed (n 0))
def pStr : P := .succeed (.lit (.str "hi \"there\"\n"))
def pFailCause : P :=
  .failCause (.both (.fail (n 1)) (.both (.die (n 2)) (.both (.interrupt (some (n 3))) (.interrupt none))))
def pYieldError : P := .yieldError (.lit (.bool true))
def pSync : P := .sync (.app "add" (ts [n 2, n 3]))
def pSuspend : P := .suspend (.succeed u)
def pMatch : P := .matchCause (.succeed (n 1)) (.succeed (.app "isZero" (ts [v 0]))) (.succeed (.lit (.bool false)))
def pOnExit : P := .onExit (.succeed (n 1)) (.yieldNow 1)
def pExit : P := .exit (.fail (n 9))
def pMasks : P := .uninterruptible (.interruptible (.succeed (n 1)))
def pBranch : P := .branch (.lit (.bool true)) (.succeed (n 1)) (.fail (n 2))
def pCallback : P := .bind (.perform .deferredMake u) (.callback .deferredAwait (v 0))
def pJoin : P := .bind (.withFiber (.fork child ⟨false, true, .uninterruptible⟩)) (.awaitFiber (v 0) .joinEffect)
def pScoped : P :=
  .scoped (.bind (.perform (.scopeMake .parallel) u)
    (.withFiber (.forkIn (.succeed (n 1)) ⟨true, true, .uninterruptible⟩ (v 0))))
def pAcquire : P := .acquireRelease (.perform .refMake (n 0)) (.perform .refGet (v 0))
def pChoose : P := .choose 3 (.succeed (n 1)) (.succeed (n 2))
def pPair : P := .succeed (.app "fst" (ts [.app "pair" (ts [n 1, .lit (.bool true)])]))
def pStmts : P :=
  .gen (st [ .bindYield (.succeed (n 0))
           , .whileTrue (st [.ifElse (.app "lt" (ts [v 0, n 3])) (st [.yieldDiscard (.yieldNow 0)]) (st [.breakLoop])])
           , .ret (v 0) ])
/-- Every fiber action, one after another; `raceAll` last. -/
def pActions : P :=
  binds
    [ .withFiber (.forkScoped child opts)                                  -- v0 : fiberOf nat never
    , .perform (.scopeMake .sequential) u                                 -- v1 : scope
    , .withFiber (.runIn (v 0) (v 1))                                     -- v2
    , .withFiber (.interrupt (v 0))                                       -- v3
    , .withFiber (.interruptScoped (v 0))                                 -- v4
    , .withFiber .snapshotChildren                                        -- v5 : list (fiberOf unknown unknown)
    , .withFiber (.awaitNewChildren (v 5))                                -- v6
    , .withFiber .getContext                                              -- v7 : context
    , .withFiber (.setContext (v 7))                                      -- v8
    , .withFiber .getId                                                   -- v9 : nat
    , .withFiber (.interruptAll (v 5) (some (v 9)))                       -- v10
    , .withFiber (.interruptAll (v 5) none)                               -- v11
    , .withFiber (.awaitAll (v 5))                                        -- v12
    , .withFiber (.awaitAllFailFast (v 5))                                -- v13
    , .exit (.succeed (n 1))                                              -- v14 : exitOf nat never
    , .withFiber (.closeScope (v 1) (v 14)) ]                             -- v15
    (.withFiber (.raceAll (es [child, .succeed (n 3)])))
/-- Every native operation, one after another; the async row through `callback` last. -/
def pOps : P :=
  binds
    [ .perform .refMake (n 1)                                             -- v0 : ref
    , .perform .refGet (v 0)                                              -- v1
    , .perform .refSet (.app "pair" (ts [v 0, n 2]))                      -- v2 : ref
    , .perform .refGetAndSet (.app "pair" (ts [v 0, n 3]))                -- v3
    , .perform .refSetAndGet (.app "pair" (ts [v 0, n 4]))                -- v4
    , .perform (.refUpdate .incr) (v 0)                                   -- v5
    , .perform (.refGetAndUpdate .double) (v 0)                           -- v6
    , .perform (.refUpdateAndGet .zeroWhenPositive) (v 0)                 -- v7
    , .perform (.refUpdateSome .noChange) (v 0)                           -- v8
    , .perform (.refGetAndUpdateSome .takeAndBump) (v 0)                  -- v9
    , .perform (.refUpdateSomeAndGet .incr) (v 0)                         -- v10
    , .perform (.refModify .double) (v 0)                                 -- v11
    , .perform (.refModifySome .noChange) (v 0)                           -- v12
    , .perform .deferredMake u                                            -- v13 : deferred
    , .perform .deferredIsDone (v 13)                                     -- v14
    , .perform .deferredPoll (v 13)                                       -- v15
    , .perform .deferredSucceed (.app "pair" (ts [v 13, n 1]))            -- v16
    , .perform .deferredFail (.app "pair" (ts [v 13, n 2]))               -- v17
    , .perform (.scopeMake .sequential) u                                 -- v18
    , .perform (.scopeMake .parallel) u ]                                 -- v19
    (.callback .deferredAwait (v 13))

-- ill-typed
def pIll : P := .succeed (.app "succ" (ts [.lit (.bool true)]))
def pIllRet : P := .gen (st [.ret (n 1), .ret (n 2)])
def pIllReq : P := .perform .refGet (n 1)
def pIllBreak : P := .gen (st [.breakLoop])
def pIllBranch : P := .branch (n 1) (.succeed (n 1)) (.succeed (n 2))
def pIllJoin : P := .branch (.lit (.bool true)) (.succeed (n 1)) (.succeed (.lit (.bool true)))
def pIllVar : P := .succeed (v 0)
def pIllCallback : P := .bind (.perform .refMake (n 0)) (.callback .refGet (v 0))
def pIllStep : P := .whileLoop (n 0) (.app "lt" (ts [v 0, n 3])) (.lit (.bool true)) (.yieldNow 0)
def pIllInterruptor : P := .failCause (.interrupt (some (.lit (.bool true))))

def corpus : List (String × P) :=
  [ ("p42", p42), ("pBind", pBind), ("pFork", pFork), ("pTwo", pTwo), ("pAwait", pAwait)
  , ("pGen", pGen), ("pWhile", pWhile), ("pCatch", pCatch), ("pStr", pStr), ("pFailCause", pFailCause)
  , ("pYieldError", pYieldError), ("pSync", pSync), ("pSuspend", pSuspend), ("pMatch", pMatch)
  , ("pOnExit", pOnExit), ("pExit", pExit), ("pMasks", pMasks), ("pBranch", pBranch)
  , ("pCallback", pCallback), ("pJoin", pJoin), ("pScoped", pScoped), ("pAcquire", pAcquire)
  , ("pChoose", pChoose), ("pPair", pPair), ("pStmts", pStmts), ("pActions", pActions), ("pOps", pOps)
  , ("pIll", pIll), ("pIllRet", pIllRet), ("pIllReq", pIllReq), ("pIllBreak", pIllBreak)
  , ("pIllBranch", pIllBranch), ("pIllJoin", pIllJoin), ("pIllVar", pIllVar)
  , ("pIllCallback", pIllCallback), ("pIllStep", pIllStep), ("pIllInterruptor", pIllInterruptor) ]

end Corpus

/-! ## Main -/

def countOps (nativeOp : Family) : Nat × Nat × Nat :=
  nativeOp.ctors.foldl (init := (0, 0, 0)) fun (nul, fn, st) c =>
    match c.args with
    | [] => (nul + 1, fn, st)
    | [(_, .named "fn_name")] => (nul, fn + 1, st)
    | [(_, .named "finalizer_strategy")] => (nul, fn, st + 1)
    | _ => (nul, fn, st)

end EffGen

open EffGen in
def main (args : List String) : IO Unit := do
  let some outDir := args.head? | throw (IO.userError "usage: EffGen <outdir>")
  let out : System.FilePath := outDir
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Program.Native }] {} 0
  let ctx : Core.Context := { fileName := "<effgen>", fileMap := default }
  let (bs, _) ← ((readBlocks.run' {}).toIO ctx { env := env })
  let families := bs.flatten
  -- constructor indices, by full name, from the environment; a structure's tree names the
  -- type (`V.struct`), normalised here to its one constructor
  let mut idx : NameMap Nat := {}
  let mut structCtor : NameMap Name := {}
  for f in families do
    for (i, c) in enumL f.ctors do
      idx := idx.insert c.name i
    if f.isStruct then structCtor := structCtor.insert f.spec.leanName f.ctors.head!.name
  let norm (n : Name) : Name := (structCtor.find? n).getD n
  let famOf (n : Name) : Option Family := families.find? (·.spec.leanName == n)
  let ctorCount (n : Name) : Nat := (famOf n).map (·.ctors.length) |>.getD 0
  -- cross-checks before anything is written
  unless fnNames.length == ctorCount `Effect4.Machine.FnName && fnNames.eraseDups.length == fnNames.length do
    throw (IO.userError "EffGen: fnNames does not enumerate FnName")
  unless FinalizerStrategy.all.length == ctorCount `Effect4.FinalizerStrategy do
    throw (IO.userError "EffGen: FinalizerStrategy.all does not enumerate FinalizerStrategy")
  let some nativeOp := famOf `Effect4.Program.NativeOp | throw (IO.userError "EffGen: NativeOp missing")
  let (nul, fn, st) := countOps nativeOp
  unless nul + fn + st == nativeOp.ctors.length do
    throw (IO.userError "EffGen: a NativeOp constructor has an argument shape this tool does not enumerate")
  unless allOps.length == nul + fn * fnNames.length + st * FinalizerStrategy.all.length do
    throw (IO.userError s!"EffGen: allOps has {allOps.length} values, the constructor table implies {nul + fn * fnNames.length + st * FinalizerStrategy.all.length}")
  unless allOps.eraseDups.length == allOps.length do throw (IO.userError "EffGen: allOps repeats a value")
  match checkAtoms with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"EffGen: {e}")
  -- the corpus: every constructor name resolves in the environment
  let trees := Corpus.corpus.map fun (nm, p) => (nm, p, effV p)
  for (nm, _, t) in trees do
    for n in t.names do
      unless idx.contains (norm n) do
        throw (IO.userError s!"EffGen: {nm} uses {n}, not a constructor of the closed world")
  let lookup (n : Name) : Nat := (idx.find? (norm n)).getD 0
  -- write
  IO.FS.createDirAll out
  IO.FS.createDirAll (out / "goldens")
  IO.FS.writeFile (out / "eff_types.ml") (emitTypes bs)
  IO.FS.writeFile (out / "eff_wire.ml") (emitWire bs)
  IO.FS.writeFile (out / "eff_json.ml") (emitJson bs)
  IO.FS.writeFile (out / "eff_native.ml") (emitNative nul fn st)
  IO.FS.writeFile (out / "eff_manifest.txt") (manifest bs)
  let mut corpusLines : Array String := #[]
  let mut coverage : NameMap Nat := {}
  for (nm, p, t) in trees do
    IO.FS.writeBinFile (out / "goldens" / (nm ++ ".bin")) (ByteArray.mk (t.bytes lookup).toArray)
    IO.FS.writeFile (out / "goldens" / (nm ++ ".json")) (t.json ++ "\n")
    let typed := Effect4.Program.typeOf nativeSignature p
    let ty := match typed with
      | some t => (effTyV t).json
      | none => "ill-typed"
    IO.FS.writeFile (out / "goldens" / (nm ++ ".ty")) (ty ++ "\n")
    corpusLines := corpusLines.push s!"{nm}\t{if typed.isSome then "well-typed" else "ill-typed"}"
    for n in t.names do
      coverage := coverage.insert (norm n) ((coverage.find? (norm n)).getD 0 + 1)
  IO.FS.writeFile (out / "goldens" / "corpus.txt") ("\n".intercalate corpusLines.toList ++ "\n")
  -- coverage of the program families by the corpus
  let mut cov : Array String := #[]
  let mut missing : Array String := #[]
  for f in families do
    if [`Effect4.Program.Ty, `Effect4.Program.RowKind, `Effect4.Program.RowShape, `Effect4.ServiceName,
        `Effect4.ServiceTypeCode, `Effect4.ServiceKey, `Effect4.Program.Row, `Effect4.Program.EffTy].contains f.spec.leanName then
      continue
    for c in f.ctors do
      let k := (coverage.find? c.name).getD 0
      cov := cov.push s!"{c.name}\t{k}"
      if k == 0 then missing := missing.push c.name.toString
  IO.FS.writeFile (out / "goldens" / "coverage.txt") ("\n".intercalate cov.toList ++ "\n")
  unless missing.isEmpty do
    throw (IO.userError s!"EffGen: the corpus reaches no {missing}")
  IO.println s!"EffGen: {families.length} families, {trees.length} corpus programs, written to {outDir}"
