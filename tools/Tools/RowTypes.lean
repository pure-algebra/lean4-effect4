import Effect4.Program.Packages
import Effect4.Program.NativeAtom
import Effect4.Laws.Program.Template
import TestSupport.AcquireHandle
import Tools.ProfileJson
import Tools.TypeSpelling
import Lean.Data.Json

/-!
# Tools.RowTypes — every selectable row's target signature, rendered by the one printer

    lake env lean -M4096 --run tools/Tools/RowTypes.lean generated/row-types.tsv [--check]

`tools/target` used to carry its own `Ty` printer (`profile.ts`'s `renderTy`), a hand copy of
`Ty.renderRaw`, which had fallen four constructors behind. The lane then read `Ty.renderRaw`
itself, which prints a type as stored. A printed module normalizes first and spells the type
through `Codegen.Types.ofTy`, so the two differ at a product over a union of literals. The
expected columns of the target lane's row queries are now the spelling a printed module ships
(`Tools.TypeSpelling.spelled`), the one printer (decisions row 392 (2), P3). The projection of a
row's request by its `RowShape`, which is a rule about rows, not about TypeScript, is stated once,
here, beside the shape it reads. A type with no printed form refuses the table by name.

One line per row, tab separated:

    table  name  shape  receiver  request  answer  error  typeArgs

`request` is the argument tuple the call takes (`[string, number]`), `receiver` the method's
receiver or empty. A row with trailing arguments or declared type arguments is not a callable
adapter row for this lane. Neither is a read-modify-write row, whose call takes the function of
its binder term after the request (`printPerform`, `Codegen/PrintLeaf.lean`), nor a row whose
operation carries type arguments on the call's head (`Deferred.make<A, E>()`, `printCall`). Each
is written with an empty `request`, which the reader refuses.
`typeArgs` is the explicit instantiation the lane queries a template atom or a template row at
(`<"p0">`), its request and answer rendered at the same probes; it is empty on every other line.

The tables are the ones the lane can select: the canonical packages
(`Effect4.Program.Packages.all`) and the truth harness's host fixture. That fixture is
declared twice in the tree — `harness/truth/Truth.lean`'s `acquireHandleTable` and
`Test/Api/AcquireHandleContract.table` — so this driver reads the second and *checks* it
against the first, which the truth harness published into `harness/truth/corpus.json`
(`hostRows`): the three rows' JSON must be exactly what this table encodes, or the run
refuses. One printer, and the duplicated fixture cannot drift silently.

`--check` compares the committed file with a fresh render and exits 1 on any difference.
-/

open Effect4.Program

namespace Tools.RowTypes

/-- A type at the spelling a printed module ships (`Tools.TypeSpelling.spelled`). A type with no
printed form refuses the table, named by its normal form, since no module could state it. -/
def spell (t : Ty) : Except String String :=
  match Tools.TypeSpelling.spelled t with
  | some text => .ok text
  | none => .error s!"the type {t.render} has no printed form"

/-- The arguments a call of this shape takes, at the shipped spelling: the printer's one-level
product split. `none` where the row is not a callable adapter row. -/
def request (row : Row) : Except String (Option (String × Option String)) :=
  if !row.trailing.isEmpty || !row.typeArgs.isEmpty then pure none else
  let spread (t : Ty) : Except String String := match t with
    | .unit => pure "[]"
    | .prod l r => do pure ("[" ++ (← spell l) ++ ", " ++ (← spell r) ++ "]")
    | t => do pure ("[" ++ (← spell t) ++ "]")
  match row.shape with
  | .call => match row.request with
    | .unit => pure (some ("[]", none))
    | t => do pure (some ("[" ++ (← spell t) ++ "]", none))
  | .tupleCall => match row.request with
    | .prod _ _ => do pure (some (← spread row.request, none))
    | _ => pure none
  | .method => match row.request with
    | .prod left right => do pure (some (← spread right, some (← spell left)))
    | _ => pure none
  | .value => pure none

def shapeName : RowShape → String
  | .call => "call"
  | .value => "value"
  | .tupleCall => "tupleCall"
  | .method => "method"

/-- One line of the table, with the explicit instantiation the lane queries it at. A row this
lane cannot call keeps its name and shape with empty argument columns; the reader refuses to
select it. `callable := false` names a row whose call takes more than its request. -/
def lineAt (table : String) (row : Row) (typeArgs : String) (callable : Bool := true) :
    Except String String := do
  let called ← if callable then request row else pure none
  let (args, receiver) := match called with
    | some (args, receiver) => (args, receiver.getD "")
    | none => ("", "")
  pure (String.intercalate "\t"
    [table, row.name, shapeName row.shape, receiver, args,
      (← spell row.answer), (← spell row.error), typeArgs])

/-- One line of a row with no parameter. -/
def line (table : String) (row : Row) : Except String String := lineAt table row ""

/-- The built-in operations, one per row name: `scopeMake` prints its strategy as a trailing
argument, so one representative stands for its two rows. The core's `NativeOp.spelled`
(`src/Effect4/Program/Native.lean`) holds one operation per spelling key, a read-modify-write row
once, at its face; its first operation at each spelling is the row name's representative. -/
def nativeOps : List NativeOp :=
  NativeOp.spelled.foldl (fun acc op =>
    if acc.any (fun seen => seen.row.spelling == op.row.spelling) then acc else acc ++ [op]) []

#guard nativeOps.length = 22

/-- The probe a template atom's query instantiates parameter `i` at: a string literal type no
other type of a template can be, so an agreement at the probes is the template's own. -/
def probe (i : Nat) : Ty := .lit s!"p{i}"

/-- The explicit instantiation a template is queried at: its parameters `0 … n-1` at their
probes. They are the target's type parameters in declaration order, which is the order the
prelude spells every template in. -/
def probes (params : List Ty) : Ty.Subst :=
  match (params.flatMap Ty.varsOf).max? with
  | some n => (List.range (n + 1)).map fun i => (i, probe i)
  | none => []

/-- An argument list in the target's request syntax. -/
def renderArgs (params : List Ty) : Except String String := do
  pure ("[" ++ String.intercalate ", " (← params.mapM spell) ++ "]")

/-- The explicit instantiation a query applies: each parameter's probe, in order. -/
def typeArgsOf (σ : Ty.Subst) : Except String String := do
  if σ.isEmpty then pure "" else
    pure ("<" ++ String.intercalate ", " (← σ.mapM fun b => spell b.2) ++ ">")

/-- An atom's declared signature in the target's request syntax, with the type arguments the
query applies. A template is spelled at its probes and queried at them, so the target checks
an ordinary signature against the template's instance; `alts` and the custom rules declare
none, and what the prelude spells for them is what the lane reports. -/
def atomSignature (s : NativeAtom.Scheme) : Except String (Option (String × String × String)) :=
  match s with
  | .mono params answer => do pure (some (← renderArgs params, ← spell answer, ""))
  | .variadic param answer => do pure (some ((← spell param) ++ "[]", ← spell answer, ""))
  | .poly params answer => do
    let σ := probes params
    pure (some (← renderArgs (params.map (Ty.instantiate σ)),
      ← spell (Ty.instantiate σ answer), ← typeArgsOf σ))
  | .alts _ | .custom _ => pure none

/-- A native row's line: a template row (the `Ref` and `Deferred` rows since the state plan's
T3a) is rendered at its parameters' probes and queried at them, as a template atom is. The
parameters are those of the request, the answer and the error: `Ref.modify`'s `B` occurs in its
answer and in its binder term's result, never in its request (the state plan's T3b). A
read-modify-write row is not callable here: its call takes its function after the request (the
state plan's T5), so its request column stays empty, as when the row carried a trailing name.
The target's signatures of the eight rows were checked by the truth lane's compiler control
(`git:fa7bdc304:harness/truth/term-rows.typecheck.ts`), retired with the lane. A row whose
operation carries type arguments is not callable here either: its call takes them on its head
(the state plan's T5, part B), and its line stays as it was when the row spelled them. -/
def nativeLine (op : NativeOp) : Except String String := do
  let row := NativeOp.row op
  let σ := probes [row.request, row.answer, row.error]
  let inst : Row :=
    { row with
      request := row.request.instantiate σ
      answer := row.answer.instantiate σ
      error := row.error.instantiate σ }
  lineAt "Native" inst (← typeArgsOf σ)
    (callable := (nativeSignature.termOf op).isNone && (nativeSignature.typeArgsOf op).isEmpty)

def schemeKind : NativeAtom.Scheme → String
  | .mono _ _ => "mono"
  | .variadic _ _ => "variadic"
  | .poly .. => "poly"
  | .alts _ => "alts"
  | .custom _ => "custom"

/-- One line per atom, in the inventory's order, under the table name `Atom`. The `shape`
column carries the scheme's kind, which is what a reader of this table needs to know before
reading its request. -/
def atomLine (atom : NativeAtom) : Except String String := do
  let spec := NativeAtom.spec atom
  let (request, answer, typeArgs) := (← atomSignature spec.scheme).getD ("", "", "")
  pure (String.intercalate "\t"
    ["Atom", NativeAtom.name atom, schemeKind spec.scheme, "", request, answer, "", typeArgs])

/-- The host fixture, checked against what the truth harness published. -/
def hostRowsAgree (corpus : Lean.Json) (rows : List Row) : Except String Unit := do
  let published : List Lean.Json ← match corpus.getObjVal? "hostRows" with
    | Except.ok (Lean.Json.arr xs) => pure xs.toList
    | _ => throw "harness/truth/corpus.json has no hostRows array"
  if published.length != rows.length then
    throw s!"harness/truth/corpus.json publishes {published.length} host rows, the fixture has {rows.length}"
  for (theirs, ours) in published.zip rows do
    let mine := Tools.ProfileJson.rowJson ours
    if theirs.compress != mine.compress then
      throw s!"host row {ours.name} differs from harness/truth/corpus.json: {theirs.compress} vs {mine.compress}"
  pure ()

def render (corpus : Lean.Json) : Except String String := do
  hostRowsAgree corpus Test.Api.AcquireHandleContract.table
  let header := "# GENERATED by tools/Tools/RowTypes.lean (each type at the spelling a printed module ships, over the row tables and the atom table); do not edit\n# table\tname\tshape\treceiver\trequest\tanswer\terror\ttypeArgs\n"
  let packages ← (Packages.all.flatMap fun p => p.rows.map (p.name, ·)).mapM
    fun (table, row) => line table row
  let host ← Test.Api.AcquireHandleContract.table.mapM (line "Host")
  let native ← nativeOps.mapM nativeLine
  let atoms ← NativeAtom.all.mapM atomLine
  pure (header ++ String.intercalate "\n" (packages ++ host ++ native ++ atoms) ++ "\n")

end Tools.RowTypes

def main (args : List String) : IO UInt32 := do
  let some out := args.head? | do
    IO.eprintln "usage: RowTypes.lean <out.tsv> [--check]"; return 2
  let corpusText ← IO.FS.readFile "harness/truth/corpus.json"
  let corpus ← match Lean.Json.parse corpusText with
    | Except.ok j => pure j
    | Except.error e => do IO.eprintln s!"harness/truth/corpus.json: {e}"; return 2
  match Tools.RowTypes.render corpus with
  | Except.error e => do IO.eprintln s!"FAIL row-types: {e}"; return 1
  | Except.ok text =>
    if args.contains "--check" then
      let committed ← try IO.FS.readFile out catch _ => pure ""
      if committed == text then
        IO.println s!"PASS row-types: {out} is the shipped spelling of every selectable row"
        return 0
      IO.eprintln s!"FAIL row-types: {out} differs from a fresh render; regenerate it"
      return 1
    IO.FS.writeFile out text
    IO.println s!"wrote {out}"
    return 0
