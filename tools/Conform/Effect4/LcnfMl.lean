import Conform.Lcnf.SemanticsTarget
import Conform.Lcnf.Validity
import OCaml5.Lcnf.Translate
import OCaml5.Lcnf.Types
import OCaml5.Ml.Render
import Effect4

/-!
# Conform.Effect4.LcnfMl — rung 3: the emitted OCaml, read into the target semantics

**What it is.** A reader from `OCaml5.Ml.Syntax` into `Conform.Lcnf.Target`, and the
differential that uses it: translate the `Effect4.Program.Ty` closure with the *real*
translator (`OCaml5.Lcnf.translateClosure`, unchanged), read the `Ml.Decl`s it produces into
`Target.Expr`, and run that against the compiled Lean functions on the same 20,387 vectors
rung 2 uses. Nothing is re-implemented: the input is exactly the syntax tree
`OCaml5.Ml.Render` renders into `ocaml/gen/*.ml`.

    lake env lean -M4096 --run tools/Conform/Effect4/LcnfMl.lean --out <dir>

**The reader refuses by name.** Every `Ml.Expr` and `Ml.Pat` constructor outside the emitted
subset is an `Except` error naming the constructor, so "the evaluator handles what the
translator emits" is a checked claim rather than a hope. The refusals this run reports are
listed in the output.

**The two extern overrides.** `Ty.key` goes through `String.toUTF8` and `ByteArray.data`,
which have no mono body, so the translator emits `assert false` for both and the generated
`Ty.key` aborts. This driver supplies the two bindings the route is missing — `utf8_bytes`
and the identity — and says so; they are a *proposal* for two extern rows, and the
differential is what shows the proposal is right.
-/

open Lean Compiler LCNF
open Conform Conform.Lcnf
open Effect4.Program

namespace Conform.Effect4.LcnfMl

/-! ## 1. The reader -/

/-- Constructor names an OCaml target spells as a literal rather than as a constructor. -/
def litCtor? : String → Option Target.Pat
  | "true" => some (.bool true)
  | "false" => some (.bool false)
  | "()" => some .unit
  | _ => none

partial def ofPat : OCaml5.Ml.Pat → Except String Target.Pat
  | .wild => .ok .wild
  | .var n => .ok (.var n)
  | .int n => .ok (.int n)
  | .str s => .ok (.str s)
  | .ctor n args => do
    match litCtor? n, args with
    | some p, [] => .ok p
    | _, _ => return .ctor n (← args.mapM ofPat)
  | .record fs => do return .record (← fs.mapM fun (k, p) => do return (k, ← ofPat p)) false
  | .recordOpen fs => do return .record (← fs.mapM fun (k, p) => do return (k, ← ofPat p)) true
  | .tuple ps => do return .tuple (← ps.mapM ofPat)
  | .cons h t => do return .ctor "::" [← ofPat h, ← ofPat t]
  | .listPat items => do
    let ps ← items.mapM ofPat
    return ps.foldr (fun h t => .ctor "::" [h, t]) (.ctor "[]" [])
  | .constrained p _ => ofPat p
  | .alias .. => .error "Ml.Pat.alias"
  | .orPat .. => .error "Ml.Pat.orPat"
  | .char _ => .error "Ml.Pat.char"
  | .float _ => .error "Ml.Pat.float"
  | .exnPat _ => .error "Ml.Pat.exnPat"
  | .polyPat .. => .error "Ml.Pat.polyPat"
  | .lazyPat _ => .error "Ml.Pat.lazyPat"

/-- Operators and function names the target evaluates as primitives; `::` is a constructor,
not a primitive, and is handled before this. -/
def isPrimName (n : String) : Bool := (Target.primArity n).isSome

partial def ofExpr : OCaml5.Ml.Expr → Except String Target.Expr
  | .var n => .ok (.var n)
  | .int n => .ok (.int n)
  | .str s => .ok (.str s)
  | .bool b => .ok (.bool b)
  | .unit => .ok .unit
  | .ctor n args => do
    match n, args with
    | "true", [] => return .bool true
    | "false", [] => return .bool false
    | "()", [] => return .unit
    | _, _ => return .ctor n (← args.mapM ofExpr)
  | .binop "::" l r => do return .ctor "::" [← ofExpr l, ← ofExpr r]
  | .binop op l r => do
    if isPrimName op then return .prim op [← ofExpr l, ← ofExpr r]
    else .error s!"Ml.Expr.binop `{op}`"
  | .app f args => do
    let as ← args.mapM ofExpr
    match f with
    | .var n => if isPrimName n then return .prim n as else return .app (.var n) as
    | _ => return .app (← ofExpr f) as
  | .fn params body => do return .fn params (← ofExpr body)
  | .letIn n v b => do return .letIn n (← ofExpr v) (← ofExpr b)
  | .letRecIn binds b => do
    let bs ← binds.mapM fun (n, ps, body) => do return (n, ps, ← ofExpr body)
    return .letRec bs (← ofExpr b)
  | .ifThen c t e => do return .ifThen (← ofExpr c) (← ofExpr t) (← ofExpr e)
  | .matchE scrut arms => do
    let as ← arms.mapM fun
      | .mk p none body => do return (← ofPat p, ← ofExpr body)
      | .mk _ (some _) _ => .error "Ml.Arm with a guard"
    return .matchE (← ofExpr scrut) as
  | .record fs => do return .record (← fs.mapM fun (k, e) => do return (k, ← ofExpr e))
  | .field e n => do return .field (← ofExpr e) n
  | .tuple parts => do return .tuple (← parts.mapM ofExpr)
  | .listLit items => do
    let es ← items.mapM ofExpr
    return es.foldr (fun h t => .ctor "::" [h, t]) (.ctor "[]" [])
  | .annot e _ => ofExpr e
  | .assertE _ => .ok (.fail "assert false")
  | .hole note _ => .ok (.fail s!"HOLE: {note}")
  | .seq .. => .error "Ml.Expr.seq"
  | .tryWith .. => .error "Ml.Expr.tryWith"
  | .recordWith .. => .error "Ml.Expr.recordWith"
  | .setField .. => .error "Ml.Expr.setField"
  | .mkRef _ => .error "Ml.Expr.mkRef"
  | .deref _ => .error "Ml.Expr.deref"
  | .assign .. => .error "Ml.Expr.assign"
  | .raiseE _ => .error "Ml.Expr.raiseE"
  | .perform _ => .error "Ml.Expr.perform"
  | .continueK .. => .error "Ml.Expr.continueK"
  | .discontinueK .. => .error "Ml.Expr.discontinueK"
  | .matchWith .. => .error "Ml.Expr.matchWith"
  | .tryWithEff .. => .error "Ml.Expr.tryWithEff"
  | .raw _ => .error "Ml.Expr.raw"
  | .char _ => .error "Ml.Expr.char"
  | .float _ => .error "Ml.Expr.float"
  | .intOf _ => .error "Ml.Expr.intOf"
  | .lam .. => .error "Ml.Expr.lam"
  | .functionE _ => .error "Ml.Expr.functionE"
  | .letPat .. => .error "Ml.Expr.letPat"
  | .openIn .. => .error "Ml.Expr.openIn"
  | .lazyE _ => .error "Ml.Expr.lazyE"
  | .arrayLit _ => .error "Ml.Expr.arrayLit"
  | .arrayGet .. => .error "Ml.Expr.arrayGet"
  | .arraySet .. => .error "Ml.Expr.arraySet"
  | .whileE .. => .error "Ml.Expr.whileE"
  | .forE .. => .error "Ml.Expr.forE"
  | .polyCtor .. => .error "Ml.Expr.polyCtor"
  | .appL .. => .error "Ml.Expr.appL (a labelled application)"
  | .ifThenOnly .. => .error "Ml.Expr.ifThenOnly"
  | .handler .. => .error "Ml.Expr.handler"
  | .matchWithK .. => .error "Ml.Expr.matchWithK"
  | .shallowContinue .. => .error "Ml.Expr.shallowContinue"
  | .shallowDiscontinue .. => .error "Ml.Expr.shallowDiscontinue"
  | .reperform .. => .error "Ml.Expr.reperform"

/-- One `Ml.Bind` as a top-level target binding. -/
def ofBind (b : OCaml5.Ml.Bind) : Except String (String × List String × Target.Expr) := do
  unless b.lparams.isEmpty do throw "Ml.Bind.lparams"
  return (b.name, b.params.map (·.1), ← ofExpr b.body)

/-! ## 2. Marshalling `Ty` into the OCaml value domain

The OCaml constructor names come from `OCaml5.Lcnf.ctorName` — the same function the
translator uses — so a rename in `Naming` breaks this differential rather than silently
comparing two different representations. -/

def tyCtor (c : String) : String := OCaml5.Lcnf.ctorName ``Ty c

partial def tyT : Ty → Target.TValue
  | .never => .ctorV (tyCtor "never") #[]
  | .unit => .ctorV (tyCtor "unit") #[]
  | .nat => .ctorV (tyCtor "nat") #[]
  | .int => .ctorV (tyCtor "int") #[]
  | .string => .ctorV (tyCtor "string") #[]
  | .bool => .ctorV (tyCtor "bool") #[]
  | .handle t => .ctorV (tyCtor "handle") #[.str t]
  | .option i => .ctorV (tyCtor "option") #[tyT i]
  | .list i => .ctorV (tyCtor "list") #[tyT i]
  | .prod l r => .ctorV (tyCtor "prod") #[tyT l, tyT r]
  | .except e v => .ctorV (tyCtor "except") #[tyT e, tyT v]
  | .exitOf v e => .ctorV (tyCtor "exitOf") #[tyT v, tyT e]
  | .causeOf e => .ctorV (tyCtor "causeOf") #[tyT e]
  | .fiberOf v e => .ctorV (tyCtor "fiberOf") #[tyT v, tyT e]
  | .union l r => .ctorV (tyCtor "union") #[tyT l, tyT r]

def tyListT (ts : List Ty) : Target.TValue := Target.TValue.ofList (ts.map tyT)
def natListT (ns : List Nat) : Target.TValue :=
  Target.TValue.ofList (ns.map fun n => Target.TValue.int (Int.ofNat n))

/-! ## 3. The vectors (the same enumeration rung 2 uses) -/

def leaves : List Ty :=
  [.never, .unit, .nat, .int, .string, .bool, .handle "Ref.Ref<number>", .handle Ty.scopeTarget]

def layer (below right : List Ty) : List Ty :=
  (below.map Ty.option) ++ (below.map Ty.list) ++ (below.map Ty.causeOf) ++
  (below.flatMap fun a => right.flatMap fun b =>
    [.prod a b, .except a b, .exitOf a b, .fiberOf a b, .union a b])

def small : List Ty := [.never, .nat, .handle "Ref.Ref<number>"]
def d1full : List Ty := leaves ++ layer leaves leaves
def c1 : List Ty := small ++ layer small small
def c2 : List Ty := c1 ++ layer c1 small
def packageTys : List Ty :=
  (Packages.sqliteBun ++ Packages.keyValueStoreMemory).flatMap fun r =>
    [r.request, r.answer, r.error]
def vectors : List Ty := (d1full ++ c2 ++ packageTys).eraseDups

def gname (n : Name) : String := OCaml5.Lcnf.globalName n

def buildCases : Array Target.TCase := Id.run do
  let mut out : Array Target.TCase := #[]
  for t in vectors do
    let tv := tyT t
    let lbl := t.render
    out := out.push { label := lbl, bind := gname ``Ty.render, args := #[tv], expected := .str t.render }
    out := out.push { label := lbl, bind := gname ``Ty.key, args := #[tv], expected := natListT t.key }
    out := out.push { label := lbl, bind := gname ``Ty.members, args := #[tv], expected := tyListT t.members }
    out := out.push { label := lbl, bind := gname ``Ty.isNever, args := #[tv], expected := .bool t.isNever }
    out := out.push { label := lbl, bind := gname ``Ty.ofMembers, args := #[tyListT t.members],
                      expected := tyT (Ty.ofMembers t.members) }
    out := out.push { label := lbl ++ " ⊔ self", bind := gname ``Ty.join, args := #[tv, tv],
                      expected := tyT (Ty.join t t) }
    out := out.push { label := lbl ++ " ⊔ never", bind := gname ``Ty.join, args := #[tv, tyT .never],
                      expected := tyT (Ty.join t .never) }
    out := out.push { label := lbl ++ " ▷ []", bind := gname ``Ty.insertMember,
                      args := #[tv, Target.TValue.ofList []],
                      expected := tyListT (Ty.insertMember t []) }
  for a in c1 do
    for b in c1 do
      let lbl := a.render ++ " | " ++ b.render
      out := out.push { label := lbl, bind := gname ``Ty.join, args := #[tyT a, tyT b],
                        expected := tyT (Ty.join a b) }
      out := out.push { label := lbl, bind := gname ``Ty.ltKey,
                        args := #[natListT a.key, natListT b.key],
                        expected := .bool (Ty.ltKey a.key b.key) }
      out := out.push { label := lbl, bind := gname ``Ty.insertMember,
                        args := #[tyT a, tyListT [b]],
                        expected := tyListT (Ty.insertMember a [b]) }
  return out

/-! ## 4. The driver -/

structure Args where
  out : Option String := none
  fuel : Nat := 200000
  /-- Supply the two missing externs (`--bare` leaves them as the holes the route emits). -/
  supplyExterns : Bool := true
  /-- The target word width; 63 is OCaml's `int`. -/
  bits : Nat := 63
  /-- Render the same declarations as a self-contained `.ml` with a driver appended, so the
  target evaluator can be checked against `ocaml` executing the real bytes. -/
  emitMl : Option String := none
  /-- Write the expected answers (computed by Lean) beside it. -/
  emitExpected : Option String := none
  /-- Leave `GenTy.merge` out of the closure. Its `requires : Row ServiceKey` field cannot be
  spelled by `OCaml5.Lcnf.Types.kernelTy` — a structure parameterised by an instance argument
  (`[LT α]`) — so the emitted type is `lcnf_unknown` and the file does not type-check. See the
  note's §3 R2. -/
  skipGenTy : Bool := false

partial def parseArgs : List String → Args → Args
  | "--out" :: p :: rest, a => parseArgs rest { a with out := some p }
  | "--fuel" :: n :: rest, a => parseArgs rest { a with fuel := n.toNat! }
  | "--bits" :: n :: rest, a => parseArgs rest { a with bits := n.toNat! }
  | "--bare" :: rest, a => parseArgs rest { a with supplyExterns := false }
  | "--emit-ml" :: p :: rest, a => parseArgs rest { a with emitMl := some p }
  | "--emit-expected" :: p :: rest, a => parseArgs rest { a with emitExpected := some p }
  | "--skip-genty" :: rest, a => parseArgs rest { a with skipGenTy := true }
  | _ :: rest, a => parseArgs rest a
  | [], a => a

/-! ### Rendering the same declarations as real OCaml

The `.ml` this writes holds the same `Ml.Decl` list the differential reads, so `ocaml`'s
answer and the target evaluator's answer are answers about the *same* syntax tree. The two
extern holes are replaced by the bodies the proposed extern rows would supply. -/

/-- The vectors, as OCaml source, through the translator's own constructor names. -/
partial def tyOcaml : Ty → String
  | .never => tyCtor "never"
  | .unit => tyCtor "unit"
  | .nat => tyCtor "nat"
  | .int => tyCtor "int"
  | .string => tyCtor "string"
  | .bool => tyCtor "bool"
  | .handle t => tyCtor "handle" ++ " (\"" ++ t ++ "\")"
  | .option i => tyCtor "option" ++ " (" ++ tyOcaml i ++ ")"
  | .list i => tyCtor "list" ++ " (" ++ tyOcaml i ++ ")"
  | .causeOf e => tyCtor "causeOf" ++ " (" ++ tyOcaml e ++ ")"
  | .prod l r => tyCtor "prod" ++ " (" ++ tyOcaml l ++ ", " ++ tyOcaml r ++ ")"
  | .except e v => tyCtor "except" ++ " (" ++ tyOcaml e ++ ", " ++ tyOcaml v ++ ")"
  | .exitOf v e => tyCtor "exitOf" ++ " (" ++ tyOcaml v ++ ", " ++ tyOcaml e ++ ")"
  | .fiberOf v e => tyCtor "fiberOf" ++ " (" ++ tyOcaml v ++ ", " ++ tyOcaml e ++ ")"
  | .union l r => tyCtor "union" ++ " (" ++ tyOcaml l ++ ", " ++ tyOcaml r ++ ")"

/-- The six observations the three sides compare, per vector: `render`, `key`, `isNever`,
`render (join t t)`, `render (ofMembers (members t))`, `length (members t)`. All six print
without a hand-written `ty` printer, so the OCaml driver needs nothing beyond the closure. -/
def expectedLine (t : Ty) : String :=
  String.intercalate "\t"
    [ t.render, " ".intercalate (t.key.map toString), toString t.isNever
    , (Ty.join t t).render, (Ty.ofMembers t.members).render, toString t.members.length ]

def driverSource : String :=
  let vecs := ";\n  ".intercalate (vectors.map fun t => "(" ++ tyOcaml t ++ ")")
  "\n(* --- driver appended by Conform.Effect4.LcnfMl --- *)\n" ++
  "let vectors = [\n  " ++ vecs ++ "\n]\n" ++
  "let show_ints l = String.concat \" \" (List.map string_of_int l)\n" ++
  "let () = List.iter (fun t ->\n" ++
  "  Printf.printf \"%s\\t%s\\t%s\\t%s\\t%s\\t%d\\n\"\n" ++
  "    (" ++ gname ``Ty.render ++ " t)\n" ++
  "    (show_ints (" ++ gname ``Ty.key ++ " t))\n" ++
  "    (string_of_bool (" ++ gname ``Ty.isNever ++ " t))\n" ++
  "    (" ++ gname ``Ty.render ++ " (" ++ gname ``Ty.join ++ " t t))\n" ++
  "    (" ++ gname ``Ty.render ++ " (" ++ gname ``Ty.ofMembers ++ " (" ++ gname ``Ty.members ++ " t)))\n" ++
  "    (List.length (" ++ gname ``Ty.members ++ " t))) vectors\n"

def roots : Array Name :=
  #[``Ty.key, ``Ty.members, ``Ty.join, ``Ty.render, ``Ty.ltKey, ``Ty.insertMember,
    ``Ty.ofMembers, ``Ty.isNever, ``GenTy.merge]

def main (argv : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let args := parseArgs argv {}
  let env ← importModules #[{ module := `Effect4 }] {} 0
  let ctx : Core.Context := { fileName := "<conform-lcnf-ml>", fileMap := default }
  let act : CoreM UInt32 := do
    let rs := if args.skipGenTy then roots.filter (· != ``GenTy.merge) else roots
    let closure ← OCaml5.Lcnf.translateClosure rs 4000 {} {}
    let mut binds : Std.HashMap String (List String × Target.Expr) := {}
    let mut refusals : Array String := #[]
    for t in closure.decls do
      match ofBind t.bind with
      | .ok (n, ps, e) => binds := binds.insert n (ps, e)
      | .error m => refusals := refusals.push s!"{t.ocamlName}: {m}"
    -- the two extern bindings the route does not have
    let mut supplied : Array String := #[]
    if args.supplyExterns then
      let u := OCaml5.Lcnf.globalName ``String.toUTF8
      let b := OCaml5.Lcnf.globalName ``ByteArray.data
      binds := binds.insert u (["s"], .prim "utf8_bytes" [.var "s"])
      binds := binds.insert b (["b"], .var "b")
      supplied := #[u, b]
    let prog : Target.Program := { binds := binds, pe := { word := { bits := args.bits } } }
    -- the same declarations as real OCaml, for the third side of the comparison
    if let some path := args.emitMl then
      let utf8Body : OCaml5.Ml.Expr :=
        .raw "List.map Char.code (List.of_seq (String.to_seq s))"
      let externBind : String → String → OCaml5.Ml.Expr → OCaml5.Ml.Bind :=
        fun nm p body => { name := nm, params := [(p, none)], result := none, body := body }
      let decls := closure.decls.map fun t =>
        if t.leanName == ``String.toUTF8 then
          { t with bind := externBind t.ocamlName "s" utf8Body }
        else if t.leanName == ``ByteArray.data then
          { t with bind := externBind t.ocamlName "b" (.var "b") }
        else t
      let gen ← (OCaml5.Lcnf.generate (closure.realTypes) closure.mentioned {} {}).run' {} {}
      let items : List OCaml5.Ml.Decl :=
        [ .floatingAttrD "warning \"-26-27-32-33-35-37-39-69\"", .blank, gen.item, .blank ]
          ++ OCaml5.Lcnf.emit decls
      let m : OCaml5.Ml.Module :=
        { name := "ty_gen"
          header := some "Rendered by Conform.Effect4.LcnfMl from the SAME Ml.Decl list the target evaluator reads. Scratch: not a committed artefact."
          items := items }
      IO.FS.writeFile path (OCaml5.Ml.render m ++ driverSource)
      IO.println s!"wrote {path}"
    if let some path := args.emitExpected then
      IO.FS.writeFile path ("\n".intercalate (vectors.map expectedLine) ++ "\n")
      IO.println s!"wrote {path}"
    let cases := buildCases
    let rows := Target.differentialT prog args.fuel "lcnf.target.agrees" cases
    let refusalRows : Array Row := refusals.map fun m =>
      Row.unresolved "lcnf.target.reads" { kind := "declaration", path := [m] }
        "the reader has no rule for this Ml constructor"
    let all := refusalRows ++ rows
    let report : Report :=
      { tool := "conform-lcnf-target"
        pins := [ { name := "lean", value := Lean.versionString }
                , { name := "word-bits", value := toString args.bits }
                , { name := "externs-supplied", value := toString args.supplyExterns } ]
        expected := all.size
        rows := all }
    let (p, f, c, u) := report.counts
    IO.println s!"translated declarations: {closure.decls.size}, read: {binds.size}, \
      reader refusals: {refusals.size}"
    for m in refusals do IO.println s!"  refused: {m}"
    IO.println s!"externs supplied: {supplied}"
    IO.println s!"cases: {cases.size}"
    IO.println s!"pass {p}  refused {f}  counterexample {c}  unresolved {u}"
    for r in all.filter (fun r => r.outcome != .pass) |>.extract 0 10 do
      IO.println s!"  {r.outcome} {r.subject.render}: {r.message}"
    match args.out with
    | none => pure ()
    | some dir =>
      IO.FS.createDirAll dir
      let leaf := if args.supplyExterns then "target" else "target-bare"
      IO.FS.writeFile (dir ++ "/" ++ leaf ++ ".json") (report.sorted.toJson.pretty ++ "\n")
      IO.println s!"wrote {dir}/{leaf}.json"
    return report.exitCode
  let (code, _) ← (act.toIO ctx { env := env })
  return code

end Conform.Effect4.LcnfMl

def main (argv : List String) : IO UInt32 := Conform.Effect4.LcnfMl.main argv
