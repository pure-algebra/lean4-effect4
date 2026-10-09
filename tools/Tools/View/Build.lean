import Tools.View.Program
import Tools.View.Motion
import Tools.Session

/-!
# The frames of a program built by edits

Slice V1 of the visual pipeline (`docs/research/2026-10-09-visual-pipeline.md`; decisions row
336, point 10). Two functions:

- `requests`: the session requests that build a program top-down, one node at a time. `open`
  declares every hole at once: one hole for each address of a sub-program, at its checked type.
  Then each `fill` puts one node at its hole, with its nearest sub-programs as their own holes.
  Each filling has the type of the hole it fills, so every fill splices the table
  (`Sketch.table_fill`): its frame shows the session checking only the new node.
- `frames`: the pages of any run of requests, one after each request that changes the session.
  The requests run through the session tool itself (`Tools.Session.answer`), so a frame shows
  what an agent sees: the sketch, the type at each address, the edit's delta and the laws named.

The construction order is one order, top-down and left to right. A request file in any order
gives its own frames.
-/

namespace Tools.View.Build

open Effect4 Effect4.Program Effect4.Program.Wire Effect4.Store Tools.View

/-- The addresses of a program's sub-programs, in the order of `Node.addresses`. -/
def effAddresses (p : NativeEff) : List (List Nat) :=
  (Node.addresses (.eff p)).filter fun a => (((Node.eff p).at_ a).bind Node.eff?).isSome

/-- `a` is a proper prefix of `b`. -/
def below (a b : List Nat) : Bool := a.length < b.length && a.isPrefixOf b

/-- The nearest sub-programs under `a`: those below it with no sub-program between. -/
def frontier (addrs : List (List Nat)) (a : List Nat) : List (List Nat) :=
  addrs.filter fun b => below a b && !(addrs.any fun c => below a c && below c b)

/-- The hole that stands for the sub-program at `b`: its position among the addresses. -/
def holeOf (addrs : List (List Nat)) (b : List Nat) : NativeEff :=
  Sketch.hole {} (addrs.findIdx (· == b))

/-- The node at `a`, with each nearest sub-program under it replaced by its hole. -/
def filling (p : NativeEff) (addrs : List (List Nat)) (a : List Nat) : Option NativeEff := do
  let sub ← ((Node.eff p).at_ a).bind Node.eff?
  (frontier addrs a).foldlM (init := sub) fun q b =>
    ((Node.eff q).replaceAt (b.drop a.length) (.eff (holeOf addrs b))).bind Node.eff?

/-- One hole row for each sub-program, named `h0`, `h1`, …, at the type the checker gives it in
the whole program. `none` when some sub-program has no type. -/
def holeRows (p : NativeEff) (addrs : List (List Nat)) : Option RowTable :=
  let table := (EditSession.open {} { program := p }).table
  addrs.zipIdx.mapM fun (a, i) =>
    (Table.typedAt table a).map fun (_, ty) => Row.hole s!"h{i}" ty.answer ty.error ty.requires.elems

/-- **The requests that build a program top-down**: `open` with the root's hole and every hole
row, then one `fill` for each sub-program, in address order. `none` when some sub-program of the
program has no type. -/
def requests (p : NativeEff) : Option (List Tools.Session.Request) := do
  let addrs := effAddresses p
  let rows ← holeRows p addrs
  let fills ← addrs.mapM fun a =>
    (filling p addrs a).map fun q =>
      ({ op := "fill", path := a, replacement := some (hexOf q) } : Tools.Session.Request)
  let opening : Tools.Session.Request :=
    { op := "open", program := some (hexOf (holeOf addrs [])), holes := some (hexString (encodeHoles rows)) }
  pure (opening :: fills)

/-- A delta in words. -/
def deltaText : Edit.Delta → String
  | .unchanged => "unchanged"
  | .spliced shown =>
    s!"spliced: {shown.length} {if shown.length == 1 then "address" else "addresses"} checked"
  | .rechecked => "checked again"

/-- The judgment line of a session: its type, or its refusals. -/
def sessionText (l : EditSession) : String :=
  let v := l.view
  match v.type with
  | some t => "type " ++ Program.effTyText t
  | none => s!"{v.refusals.length} refused"

/-- A law's name without the namespace every law of the session shares. -/
def lawText (n : Lean.Name) : String := n.toString.replace "Effect4.Program." ""

/-- The request's operation and address. -/
def requestText (r : Tools.Session.Request) : String :=
  if r.op == "open" then "open" else s!"{r.op} {Program.bracket r.path}"

/-- One frame: its page, the address its edit names, and whether the edit spliced the table. -/
structure Frame where
  page : Page
  edit : Option (List Nat) := none
  spliced : Bool := false

/-- **The frames of a run of requests**: one page after each request that answers with a
session, titled by the request. The line under the title gives the delta and the session's type;
the foot gives the laws that the answer names. A refused request draws the session before it,
with the refusal. Every frame has the widest gutter of the sequence, so a line stands at one
column in every frame. -/
def frames (title : String) (reqs : List Tools.Session.Request) : List Frame :=
  let step (acc : Tools.Session.State × List Frame) (r : Tools.Session.Request) :
      Tools.Session.State × List Frame :=
    let (st, out) := acc
    let (st', ans) := Tools.Session.answer st r
    match st'.session with
    | none => (st', out)
    | some l =>
      if r.op == "view" || r.op == "journal" || r.op == "sketch" then (st', out)
      else
        let lit := if r.op == "open" then none else some r.path
        let (delta, spliced) := match st'.journal, ans.ok, r.op with
          | s :: _, true, "fill" => (deltaText s.delta ++ "   ", s.delta matches .spliced _)
          | s :: _, true, "omit" => (deltaText s.delta ++ "   ", s.delta matches .spliced _)
          | _, false, _ => ("refused: " ++ (ans.error.getD "") ++ "   ", false)
          | _, _, _ => ("", false)
        let laws := "laws: " ++ ", ".intercalate (ans.laws.map lawText)
        let page := Program.sessionPage l lit (title ++ " · " ++ requestText r)
          (delta ++ sessionText l) "" laws
        (st', out ++ [{ page, edit := lit, spliced }])
  let out := (reqs.foldl step ({}, [])).2
  let n := out.length
  let gutter := out.foldl (fun m f => max m (ownGutter f.page)) 0
  out.zipIdx.map fun (f, i) => { f with page := { f.page with place := s!"{i + 1} / {n}", gutter } }

end Tools.View.Build
