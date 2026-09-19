import Effect4.Program.Packages
import Effect4.Program.NativeAtom
import Test.Api.AcquireHandleContract
import Tools.ProfileJson
import Lean.Data.Json

/-!
# Tools.RowTypes — every selectable row's target signature, rendered by the one printer

    lake env lean -M4096 --run tools/Tools/RowTypes.lean generated/row-types.tsv [--check]

`tools/target` used to carry its own `Ty` printer (`profile.ts`'s `renderTy`), a hand copy of
`Ty.renderRaw` that had fallen four constructors behind (`refOf`, `deferredOf`, `var`,
`unknown`) and spelled unions with parentheses. This driver replaces it: the expected columns
of the target lane's row queries are the strings `Ty.renderRaw` prints, and the projection of
a row's request by its `RowShape` — which is a rule about rows, not about TypeScript — is
stated once, here, beside the shape it reads.

One line per row, tab separated:

    table  name  shape  receiver  request  answer  error

`request` is the argument tuple the call takes (`[string, number]`), `receiver` the method's
receiver or empty. A row with trailing arguments or explicit type arguments is not a callable
adapter row for this lane and is written with an empty `request`, which the reader refuses.

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

/-- The arguments a call of this shape takes, rendered: the printer's one-level product split.
`none` where the row is not a callable adapter row. -/
def request (row : Row) : Option (String × Option String) :=
  if !row.trailing.isEmpty || !row.typeArgs.isEmpty then none else
  let render := Ty.renderRaw
  let spread : Ty → String
    | .unit => "[]"
    | .prod l r => "[" ++ render l ++ ", " ++ render r ++ "]"
    | t => "[" ++ render t ++ "]"
  match row.shape with
  | .call => some (match row.request with
      | .unit => "[]"
      | t => "[" ++ render t ++ "]", none)
  | .tupleCall => match row.request with
    | .prod _ _ => some (spread row.request, none)
    | _ => none
  | .method => match row.request with
    | .prod left right => some (spread right, some (render left))
    | _ => none
  | .value => none

def shapeName : RowShape → String
  | .call => "call"
  | .value => "value"
  | .tupleCall => "tupleCall"
  | .method => "method"

/-- One line of the table. A row this lane cannot call keeps its name and shape with empty
argument columns; the reader refuses to select it. -/
def line (table : String) (row : Row) : String :=
  let (args, receiver) := match request row with
    | some (args, receiver) => (args, receiver.getD "")
    | none => ("", "")
  String.intercalate "\t"
    [table, row.name, shapeName row.shape, receiver, args,
      Ty.renderRaw row.answer, Ty.renderRaw row.error]

/-- The built-in operations, one per row name: the read-modify-write rows differ only in the
pure function they print after the request, which is a trailing argument, so one representative
stands for the five, and `scopeMake` prints its strategy the same way. The enumeration
`Tools.TsGen.allNativeOps` is the guarded one (a `run_cmd`
there refuses a constructor added, removed or reordered); this list cannot import it, because
that module declares a root `main`. -/
def nativeOps : List NativeOp :=
  [ .refMake, .refGet, .refSet, .refGetAndSet, .refSetAndGet
  , .refUpdate .incr, .refGetAndUpdate .incr, .refUpdateAndGet .incr, .refUpdateSome .incr
  , .refGetAndUpdateSome .incr, .refUpdateSomeAndGet .incr, .refModify .incr, .refModifySome .incr
  , .deferredMake, .deferredIsDone, .deferredPoll, .deferredSucceed, .deferredFail, .deferredAwait
  , .scopeMake .sequential, .sleep, .clockNow ]

/-- An atom's declared signature in the target's request syntax, when its scheme declares one.
`alts`, `poly` and the custom rules declare none: what the prelude spells for them is what the
lane reports, and comparing it against a template with free parameters would be a claim about
an instantiation nobody made. -/
def atomSignature (s : NativeAtom.Scheme) : Option (String × String) :=
  match s with
  | .mono params answer =>
    some ("[" ++ String.intercalate ", " (params.map Ty.renderRaw) ++ "]", Ty.renderRaw answer)
  | .variadic param answer => some (Ty.renderRaw param ++ "[]", Ty.renderRaw answer)
  | .poly _ _ | .alts _ | .custom _ => none

def schemeKind : NativeAtom.Scheme → String
  | .mono _ _ => "mono"
  | .variadic _ _ => "variadic"
  | .poly _ _ => "poly"
  | .alts _ => "alts"
  | .custom _ => "custom"

/-- One line per atom, in the inventory's order, under the table name `Atom`. The `shape`
column carries the scheme's kind, which is what a reader of this table needs to know before
reading its request. -/
def atomLine (atom : NativeAtom) : String :=
  let spec := NativeAtom.spec atom
  let (request, answer) := (atomSignature spec.scheme).getD ("", "")
  String.intercalate "\t" ["Atom", NativeAtom.name atom, schemeKind spec.scheme, "", request, answer, ""]

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
  let header := "# GENERATED by tools/Tools/RowTypes.lean (Ty.renderRaw over the row tables and the atom table); do not edit\n# table\tname\tshape\treceiver\trequest\tanswer\terror\n"
  let packages := Packages.all.flatMap fun p => p.rows.map (line p.name)
  let host := Test.Api.AcquireHandleContract.table.map (line "Host")
  let native := nativeOps.map fun op => line "Native" (NativeOp.row op)
  let atoms := NativeAtom.all.map atomLine
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
        IO.println s!"PASS row-types: {out} is what Ty.renderRaw prints for every selectable row"
        return 0
      IO.eprintln s!"FAIL row-types: {out} differs from a fresh render; regenerate it"
      return 1
    IO.FS.writeFile out text
    IO.println s!"wrote {out}"
    return 0
