import Tools.View.Program
import Tools.View.Flow
import Compiler.Code.Module
import Tools.View.Motion
import Effect4.Tool.Serve

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
  The requests run through the tool itself (`Effect4.Tool.serve`), so a frame shows
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

/-- The existing top-down program plan, using hole indices instead of guessed snapshots. -/
def plan (p : NativeEff) : Option (Sketch × List (Nat × NativeEff)) := do
  let addrs := effAddresses p
  let rows ← holeRows p addrs
  let fills ← addrs.zipIdx.mapM fun (a, index) =>
    (filling p addrs a).map fun q => (index,q)
  pure (⟨holeOf addrs [],rows⟩,fills)

/-- Materialize the plan's request transcript by consuming each actual reply's snapshot. -/
def requests (p : NativeEff) : Option (List Effect4.Tool.Request) := do
  let (sketch,fills) ← plan p
  let opening : Effect4.Tool.Request := .act (.open_ "default" {} sketch)
  let (first,reply) := (Effect4.Tool.serve Check.Oracle.uncached Effect4.Tool.empty opening).value
  if !reply.result.isOk then none else do
    let (_,_,requests) ← fills.foldlM (init := (first,reply,[opening])) fun (state,previous,requests) (index,q) => do
      let now ← previous.now
      let request : Effect4.Tool.Request :=
        .act (.edit now (.commit [(.hole index,.fill q)] .keepExact))
      let (next,answer) := (Effect4.Tool.serve Check.Oracle.uncached state request).value
      if answer.result.isOk then some (next,answer,requests ++ [request]) else none
    pure requests

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
  | some t => "type " ++ Tools.Code.effTyText t
  | none => s!"{v.refusals.length} refused"

/-- A law's name without the namespace every law of the session shares. -/
def lawText (n : Lean.Name) : String := n.toString.replace "Effect4.Program." ""

/-- The request's declared method and any explicit edit place. -/
def requestText (r : Effect4.Tool.Request) : String :=
  match r with
  | .act (.edit _ (.draft edit)) => "edit " ++ Program.bracket edit.path
  | .act (.edit _ (.commit [(.hole index,_)] _)) => s!"edit hole {index}"
  | .act (.edit _ (.commit [(.at_ path _,_)] _)) => "edit " ++ Program.bracket path
  | _ => r.method

def editPath (state : Effect4.Tool.State) (request : Effect4.Tool.Request) : Option (List Nat) :=
  match request with
  | .act (.edit _ (.draft edit)) => some edit.path
  | .act (.edit _ (.commit [(place,_)] _)) => do
      let doc ← state.raw.doc
      (place.resolve doc.session.app doc.session.sketch).toOption.map Prod.fst
  | _ => none

def stepsOf (answer : Effect4.Tool.Reply) : List Edit.Step :=
  match answer.result with
  | .ok (.acted (.edited _ receipt)) | .ok (.acted (.published _ receipt)) => receipt.steps
  | _ => []

def redraws : Effect4.Tool.Request → Bool
  | .act (.open_ ..) | .act (.edit ..) | .act (.publish ..) => true
  | _ => false

def deltaOf (answer : Effect4.Tool.Reply) : String × Bool :=
  match answer.result with
  | .error _ => ("request refused   ",false)
  | .ok _ =>
    match stepsOf answer with
    | [step] => (deltaText step.delta ++ "   ",step.delta matches .spliced _)
    | [] => ("",false)
    | steps => (s!"{steps.length} edits   ",steps.all fun step => step.delta matches .spliced _)

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
def frames (title : String) (reqs : List Effect4.Tool.Request) : List Frame :=
  let step (acc : Effect4.Tool.State × List Frame) (r : Effect4.Tool.Request) :
      Effect4.Tool.State × List Frame :=
    let (st, out) := acc
    let (st', ans) := (Effect4.Tool.serve Check.Oracle.uncached st r).value
    match st'.raw.doc with
    | none => (st', out)
    | some doc =>
      if !redraws r then (st', out) else
        let l := doc.session.shown
        let lit := editPath st r
        let (delta, spliced) := deltaOf ans
        let page := Program.sessionPage l lit (title ++ " · " ++ requestText r)
          (delta ++ sessionText l) "" ""
        let holes := l.sketch.holes.map (·.name)
        let code := Program.codePanel l.sketch.program (l.app.withHoles l.sketch.holes).rows holes
        let page := { page with code }
        let page := { page with graph := some { title := "program", laid := Flow.ofPage l.sketch.program page } }
        (st', out ++ [{ page, edit := lit, spliced }])
  let out := (reqs.foldl step (Effect4.Tool.empty, [])).2
  let n := out.length
  let gutter := out.foldl (fun m f => max m (ownGutter f.page)) 0
  let out := out.map fun f => { f with page := { f.page with gutter } }
  let codeAt := out.foldl (fun m f => max m (ownCodeAt f.page)) 0
  out.zipIdx.map fun (f, i) => { f with page := { f.page with place := s!"{i + 1} / {n}", codeAt } }

end Tools.View.Build
