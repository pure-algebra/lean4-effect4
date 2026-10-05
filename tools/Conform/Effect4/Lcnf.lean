import Conform.Lcnf.Validity
import OCaml5.Lcnf.Translate

/-!
# Conform.Effect4.Lcnf — Effect4 as the first configuration of the LCNF tooling

**What it is.** The `--run` driver that points `Conform.Lcnf.Validity` at this repository's
mono closure, and the *fidelity inventory*: how faithfully each OCaml form reproduces the Lean
meaning. The value rows are read off `OCaml5.Lcnf.builtins`, where a row and its contract are
one datum. The type rows of `OCaml5.Lcnf.Types.builtinTy?` are listed here. The generic half
knows none of this: the roots and the primitive predicate live here, on the Effect4 side of
the extensibility rule (`docs/research/type-tooling/brief-common.md`).

    lake env lean -M4096 --run tools/Conform/Effect4/Lcnf.lean \
      --import Effect4.Api --out <dir> --cap 2000 Effect4.Api.run Effect4.Api.replay

**Depends on.** `Conform.Lcnf.Validity` (generic), `OCaml5.Lcnf.Translate` (the route under
audit). It is a tool: `IO`, `CoreM`, imported by nothing.
-/

open Lean Compiler LCNF
open Conform Conform.Lcnf

namespace Conform.Effect4.Lcnf

/-! ## 1. The fidelity inventory

How faithfully an OCaml row reproduces the Lean constant it stands for. The classes are the
brief's: *exact*, *exact under a stated domain*, *approximate*, *unsound*
(`OCaml5.Lcnf.Fidelity`). The class is a claim about the **row**, read against the Lean
definition. No theorem proves a row. A row names the finite controls that run it (`controls`);
a control is evidence only in the report of the run that executed it. -/

open OCaml5.Lcnf (Fidelity)

/-- One entry of the inventory. -/
structure FidRow where
  /-- The Lean constant. -/
  lean : Name
  /-- The OCaml form, as a report spells it. -/
  ocaml : String
  fidelity : Fidelity
  /-- The domain on which the row is exact (`""` when the class is `exact`). -/
  domain : String := ""
  /-- Why: the difference, or the argument that there is none. -/
  note : String
  deriving Inhabited

/-- An entry for a value row: the two columns a type row has no use for. -/
structure ValueRow extends FidRow where
  /-- The finite controls that run the row (`Conform.Effect4.CompilerControls.hostChecks`). -/
  controls : List String
  /-- The cost where it differs from Lean's. -/
  cost : String
  deriving Inhabited

/-- The value rows: one entry per row of `OCaml5.Lcnf.builtins`, computed. The table is the one
owner of a row and of its contract, so no row lacks an entry and no entry names a constant
that the route does not match. -/
def fidelityTable : List ValueRow :=
  OCaml5.Lcnf.builtins.map fun b =>
    { lean := b.lean, ocaml := b.form.spelling, fidelity := b.fidelity, domain := b.domain,
      note := b.note, controls := b.controls, cost := b.cost }

/-- The `builtinTy?` table, classified the same way (`src/OCaml5/Lcnf/Types.lean:48-62`). -/
def typeFidelityTable : List FidRow :=
  [ ⟨``Nat, "int", .domain, "n < 2^62", "OCaml `int` is 63-bit, Lean `Nat` unbounded."⟩
  , ⟨``Int, "int", .domain, "-2^62 ≤ n < 2^62", "and `Int` and `Nat` share one OCaml type, so an emitter cannot tell them apart in an annotation."⟩
  , ⟨``UInt8, "int", .exact, "", "the range 0..255 is inside `int`."⟩
  , ⟨``UInt16, "int", .exact, "", ""⟩
  , ⟨``UInt32, "int", .exact, "", ""⟩
  , ⟨``UInt64, "int", .unsound, "n < 2^62", "**the hole.** `UInt64` values reach 2^64 - 1; OCaml's `int` holds 2^62 - 1. The wire's big-endian 64-bit fields and `Effect4.Store.Val.wf`'s `… < 2 ^ 64` live in this type. Nothing in the route detects the overflow: it wraps."⟩
  , ⟨``USize, "int", .unsound, "n < 2^62", "as `UInt64` — and `USize` is the shim's index type, so it is also the type every `Array` index is spelled in."⟩
  , ⟨``Bool, "bool", .exact, "", ""⟩
  , ⟨``String, "string", .approximate, "the string is ASCII", "Lean's `String` is a sequence of Unicode scalar values; OCaml's is a byte sequence. Equality and concatenation agree; `length`, indexing and any `Char` operation do not."⟩
  , ⟨``Unit, "unit", .exact, "", ""⟩
  , ⟨``PUnit, "unit", .exact, "", ""⟩
  , ⟨``Char, "char", .unsound, "the character is ASCII", "Lean's `Char` is a Unicode scalar value (21 bits); OCaml's `char` is one byte. There is no rule for `Char` operations in `builtin?` at all, so a `Char` in code is a hole — but a `Char` in a *type* is silently `char`."⟩
  , ⟨``Float, "float", .exact, "", "both are IEEE 754 binary64. No `Float` operation has a `builtin?` row, so any arithmetic is a hole."⟩
  , ⟨``List, "list", .exact, "", ""⟩
  , ⟨``Array, "list", .approximate, "", "the shim: denotationally a sequence, operationally a different cost model (see `Array.push`, `Array.uget`)."⟩
  , ⟨``Option, "option", .exact, "", ""⟩
  , ⟨``Prod, "*", .exact, "", ""⟩
  , ⟨``Except, "result", .exact, "", "`Except ε α` is `(α, ε) result`, arguments swapped."⟩ ]

/-! ## 2. The primitive predicate

What the OCaml route does *not* descend into: a row of the builtin table and (when a table is
given) an `Extract Constant` row. This is the argument the generic walker takes. -/

def ocamlPrimitive (ex : OCaml5.Lcnf.Externs) : Name → Bool := fun n =>
  (OCaml5.Lcnf.builtin? n).isSome || ex.hasFn n

/-! ## 3. The driver -/

structure Args where
  imports : Array Name := #[`Effect4.Api]
  roots : Array Name := #[]
  cap : Nat := 4096
  out : Option String := none
  checkTypes : Bool := false
  /-- Do not treat the OCaml builtin table as primitive: walk into the stdlib too, so the
  measurement says how much of the closure the table hides. -/
  noBuiltins : Bool := false
  /-- Compile a callee whose mono body the extension does not carry, instead of recording it
  as `missing` (`Conform.Lcnf.Walk.Config.onDemand`). An **addition**: off by default, so a
  default run reads exactly what an out-of-process generator reads. -/
  onDemand : Bool := false

def parseArgs : List String → Args → Args
  | "--import" :: m :: rest, a =>
    parseArgs rest { a with imports := ((m.splitOn ",").map String.toName).toArray }
  | "--cap" :: n :: rest, a => parseArgs rest { a with cap := n.toNat! }
  | "--out" :: p :: rest, a => parseArgs rest { a with out := some p }
  | "--check-types" :: rest, a => parseArgs rest { a with checkTypes := true }
  | "--no-builtins" :: rest, a => parseArgs rest { a with noBuiltins := true }
  | "--on-demand" :: rest, a => parseArgs rest { a with onDemand := true }
  | r :: rest, a => parseArgs rest { a with roots := a.roots.push r.toName }
  | [], a => a

def main (argv : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let args := parseArgs argv {}
  if args.roots.isEmpty then
    IO.eprintln "usage: … Lcnf.lean [--import M,N] [--cap n] [--out dir] [--check-types] [--no-builtins] [--on-demand] root…"
    return 2
  let env ← importModules (args.imports.map fun m => { module := m }) {} 0
  let ctx : Core.Context := { fileName := "<conform-lcnf>", fileMap := default }
  let act : CoreM UInt32 := do
    -- the table's own check first: a row outside its contract is a stale audit
    unless OCaml5.Lcnf.problems.isEmpty do
      IO.eprintln s!"the builtin table is refused: {OCaml5.Lcnf.problems}"
      return 3
    let cfg : Walk.Config :=
      { primitive := if args.noBuiltins then (fun _ => false) else ocamlPrimitive {}
        cap := args.cap
        onDemand := args.onDemand }
    let closure ← walkClosure args.roots cfg args.checkTypes
    let manifest : Manifest :=
      { leanVersion := Lean.versionString, roots := args.roots, imports := args.imports
        closure := closure }
    let census := closure.census
    -- the human summary
    IO.println s!"roots: {args.roots}"
    IO.println s!"declarations: {closure.decls.size}  invalid: {closure.invalid.size}  \
      primitives: {closure.primitives.size}  missing: {closure.missing.size}  \
      frontier: {closure.frontier.size}  constructors: {closure.ctors.size}"
    IO.println "construct census (mono/pure fragment, 26 constructors):"
    for k in constructs do
      IO.println s!"  {k}: {census.get k}"
    IO.println s!"max local-function arity: {census.maxFunArity}, nullary local functions: {census.nullaryFuns}"
    IO.println s!"largest Nat literal: {census.maxNatLit}  (≥ 2^62: {census.bigNatLits})  \
      non-ASCII string literals: {census.nonAsciiStrLits}"
    IO.println s!"cases scrutinee types ({census.casesTypesList.length}):"
    for (n, k) in census.casesTypesList do IO.println s!"  {n}: {k}"
    IO.println s!"proj types ({census.projTypesList.length}):"
    for (n, k) in census.projTypesList do IO.println s!"  {n}: {k}"
    IO.println s!"missing ({closure.missing.size}):"
    for f in closure.missing do
      IO.println s!"  {f.name}: {f.availability} ({f.constKind}) module={f.module} moduleSystem={f.moduleIsModule}"
    IO.println s!"frontier ({closure.frontier.size}): {closure.frontier}"
    IO.println s!"invalid ({closure.invalid.size}):"
    for d in closure.invalid do
      match d.valid with
      | .error m => IO.println s!"  {d.name}: {m}"
      | .ok _ => pure ()
    IO.println s!"primitives hit ({closure.primitives.size}):"
    for n in closure.primitives do IO.println s!"  {n}"
    -- the availability catch's remedy, and its self-check. Both are silent unless asked for,
    -- so a default run's bytes are the bytes it had before the flag existed.
    if args.onDemand then
      let onDemand := closure.decls.filter (·.availability == .onDemand)
      IO.println s!"on-demand compiled ({onDemand.size}), still missing ({closure.missing.size}):"
      for d in onDemand do IO.println s!"  {d.name} ({d.size} nodes)"
      -- the mechanism's own self-check, and it is not a formality: recompile every
      -- declaration that *does* have a persisted body and say how often the in-process
      -- compile reproduces it. See the note's §2 — it usually does not.
      let mut same := 0
      let mut differ := 0
      let mut noCode := 0
      let mut noCodeInternal := 0
      let mut examples : Array String := #[]
      for d in closure.decls do
        match ← recompileAgrees? d.name with
        | none =>
          noCode := noCode + 1
          -- `Name.isInternal` is the compiler's own "the frontend could not have written
          -- this" test: `_redArg`, `_lam_N` and the `._at_.….spec_N` chains all match it,
          -- and those are exactly the names that have no kernel definition to compile.
          if d.name.isInternal then noCodeInternal := noCodeInternal + 1
        | some (alpha, sameHash) =>
          if alpha then same := same + 1
          else
            differ := differ + 1
            if examples.size < 8 then
              examples := examples.push s!"{d.name} (same DeclHash: {sameHash})"
      IO.println s!"recompiled {closure.decls.size}: alphaEqv {same}, differ {differ}, \
        no fresh body {noCode} (of which internal names: {noCodeInternal})"
      for e in examples do IO.println s!"  differs: {e}"
    -- cross-check against the real translator: the same roots through
    -- `OCaml5.Lcnf.translateClosure`, so the walker's numbers and the route's numbers are
    -- compared rather than assumed equal, and the OCaml **name collisions** are measured.
    let tc ← OCaml5.Lcnf.translateClosure args.roots args.cap {} {}
    let mut byName : Std.HashMap String (Array Name) := {}
    for t in tc.decls do
      byName := byName.insert t.ocamlName ((byName.getD t.ocamlName #[]).push t.leanName)
    let collisions := byName.toList.filter fun (_, ns) => ns.size > 1
    IO.println s!"translator: {tc.decls.size} declarations, {tc.todos.size} todos, \
      {tc.missing.size} missing, {tc.frontier.size} frontier, \
      {tc.wrapperRefs.size} wrapper refs, {tc.realTypes.size} real types"
    IO.println s!"OCaml global-name collisions ({collisions.length}):"
    for (nm, ns) in collisions do IO.println s!"  {nm} <- {ns}"
    IO.println s!"translator todos ({tc.todos.size}):"
    for t in tc.todos do IO.println s!"  {t}"
    match args.out with
    | none => pure ()
    | some dir =>
      IO.FS.createDirAll dir
      IO.FS.writeFile (dir ++ "/manifest.json") (manifest.toJson.pretty ++ "\n")
      let report := manifest.toReport
      IO.FS.writeFile (dir ++ "/report.json") (report.sorted.toJson.pretty ++ "\n")
      -- the fidelity table, as data, with the rows this closure actually hit marked
      -- a primitive is hit under its `_redArg` twin's name as often as under its own;
      -- `builtin?` itself matches on `stripRedArg n`, so the ledger must too
      let hit : Std.HashSet Name :=
        closure.primitives.foldl (fun s n => s.insert (Conform.Lcnf.stripRedArg n)) {}
      let fidJson := Json.arr (fidelityTable.toArray.map fun r =>
        Json.mkObj
          [ ("lean", Json.str r.lean.toString), ("ocaml", Json.str r.ocaml)
          , ("fidelity", Json.str (toString r.fidelity)), ("domain", Json.str r.domain)
          , ("note", Json.str r.note), ("cost", Json.str r.cost)
          , ("controls", Json.arr (r.controls.toArray.map Json.str))
          , ("hit", Json.bool (hit.contains r.lean)) ])
      let tyFidJson := Json.arr (typeFidelityTable.toArray.map fun r =>
        Json.mkObj
          [ ("lean", Json.str r.lean.toString), ("ocaml", Json.str r.ocaml)
          , ("fidelity", Json.str (toString r.fidelity)), ("domain", Json.str r.domain)
          , ("note", Json.str r.note) ])
      IO.FS.writeFile (dir ++ "/fidelity.json")
        ((Json.mkObj [("values", fidJson), ("types", tyFidJson)]).pretty ++ "\n")
      IO.println s!"wrote {dir}/manifest.json, {dir}/report.json, {dir}/fidelity.json"
      IO.eprintln report.render
    return (if closure.invalid.isEmpty then 0 else 1)
  let (code, _) ← (act.toIO ctx { env := env })
  return code

end Conform.Effect4.Lcnf

def main (argv : List String) : IO UInt32 := Conform.Effect4.Lcnf.main argv
