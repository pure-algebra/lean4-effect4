import Effect4.Tool.Protocol

/-!
# Tool.Actions — the one action interpreter

`Internal.action` runs every action against the raw state: a served request, a `dry` query and the
replay of an accepted transcript all call it. It reuses the owners: `Doc.step` for edits and
publication, `FillSet.add` for fills, `Api.Built.ofSketch` and `Live.open` for runs, and
`LiveRecord.restore` for saved runs. A refusal leaves the raw state as it was.
-/

set_option autoImplicit false
namespace Effect4.Tool
open Effect4 Effect4.Program Program.Check

namespace Internal
/-- **A run the tool holds**: where it came from, and the live run. -/
structure RunEntry where
  origin : Origin
  live : Live

/-- **The raw state**: the document, the pending fills, the runs and the document generation. -/
structure Raw where
  doc : Option Doc := none
  fills : Option FillSet := none
  runs : List RunEntry := []
  generation : Nat := 0

/-- **The document view**: snapshot, root type, refusals and every hole occurrence. -/
def docView (d : Doc) : DocView :=
  let v := d.session.view
  let holes := d.session.sketch.holes.zipIdx.flatMap fun (row,index) =>
    let paths := (Node.addresses (.eff d.session.sketch.program)).filter fun p =>
      decide ((Node.eff d.session.sketch.program).at_ p =
        some (.eff (Sketch.hole d.session.app index)))
    paths.map fun path =>
      HoleView.mk index row path ((d.session.focusAt path).map fun f => (f.env,f.ty))
  ⟨d.snap,v.type,v.refusals,holes,none⟩

/-- The current snapshot, where a document is open. -/
def current (st : Raw) : Option Snap := st.doc.map Doc.snap

/-- **The open document**, or `noDocument`. -/
def requireDoc (st : Raw) : Except Refusal Doc :=
  match st.doc with
  | none => .error .noDocument
  | some d => .ok d

/-- **The document at a snapshot**: `noDocument`, then the document's own `foreign` and `stale`. -/
def checkedDoc (st : Raw) (at_ : Snap) : Except Refusal Doc := do
  let d ← requireDoc st
  match d.check at_ with
  | .error why => throw (.doc why)
  | .ok _ => pure d

/-- The pending fills, or an empty set opened at the document. -/
def fillsFor (st : Raw) (d : Doc) : FillSet :=
  st.fills.getD (FillSet.open_ d)

/-- **Play events in order** on a live run; an unresolved selector refuses the whole list, with its
index, and the played prefix is discarded. -/
def events (id : RunId) (index : Nat) (live : Live) :
    List Run.Event → Except Refusal (Live × List Run.Verdict)
  | [] => .ok (live,[])
  | event :: rest =>
    let (next,verdict) := live.feed event
    match verdict with
    | .unresolved sel => .error (.unresolved id index sel)
    | .played _ => do
      let (last,verdicts) ← events id (index+1) next rest
      pure (last,verdict :: verdicts)

/-- The sole action interpreter; persisted replay and serving both call this definition. -/
def action (o : Oracle) (st : Raw) : Action → Checked (Except Refusal (Raw × ActionAnswer))
  | .open_ name app sketch => do
    let d ← Doc.open_ ⟨⟨name,st.generation⟩,app,sketch⟩
    pure (.ok ({st with doc := some d, fills := none, generation := st.generation+1},
      .opened (docView d)))
  | .edit at_ a => do
    match checkedDoc st at_ with
    | .error why => pure (.error why)
    | .ok d =>
      match ← d.step o at_ a with
      | .error why => pure (.error (.doc why))
      | .ok (next,receipt) => pure (.ok ({st with doc := some next},
          .edited (docView next) receipt))
  | .fill at_ batch => do
    match checkedDoc st at_ with
    | .error why => pure (.error why)
    | .ok d =>
      let fs := fillsFor st d
      if !fs.entries.isEmpty &&
          (decide (fs.anchor.doc ≠ d.snap.doc) || fs.anchor.revision != d.snap.revision) then
        pure (.error (.fillsStale fs.anchor d.snap))
      else
        let (next,outcomes) ← (if fs.entries.isEmpty then FillSet.open_ d else fs).add o batch
        pure (.ok ({st with fills := some next}, .filled outcomes))
  | .publish at_ => do
    match checkedDoc st at_ with
    | .error why => pure (.error why)
    | .ok d =>
      let fs := fillsFor st d
      if fs.entries.isEmpty then pure (.error .fillsEmpty)
      else if decide (fs.anchor.doc ≠ d.snap.doc) || fs.anchor.revision != d.snap.revision then
        pure (.error (.fillsStale fs.anchor d.snap))
      else match fs.publication with
      | .error _ => pure (.error .fillsEmpty)
      | .ok a =>
        match ← d.step o at_ a with
        | .error why => pure (.error (.doc why))
        | .ok (next,receipt) => pure (.ok ({st with doc := some next, fills := none},
            .published (docView next) receipt))
  | .reset =>
    match st.doc with
    | none => pure (.error .noDocument)
    | some d => pure (.ok ({st with fills := none},.reset (fillsFor st d).pending))
  | .start at_ budget =>
    match checkedDoc st at_ with
    | .error why => pure (.error why)
    | .ok d =>
      match Api.Built.ofSketch d.session.app d.session.sketch with
      | .error why => pure (.error (.admission why))
      | .ok built =>
        let live := ((Live.open built d.id.name budget).feed .start).1
        let origin := Origin.snapshot d.snap d.session.app d.session.sketch
        let id : RunId := ⟨st.runs.length⟩
        pure (.ok ({st with runs := st.runs ++ [⟨origin,live⟩]},
          .started id origin live.view))
  | .restore record =>
    match record.restore with
    | .error why => pure (.error (.restore why))
    | .ok live =>
      let id : RunId := ⟨st.runs.length⟩
      pure (.ok ({st with runs := st.runs ++ [⟨.standalone,live⟩]},.restored id live.view))
  | .play id input =>
    match st.runs[id.n]? with
    | none => pure (.error (.noRun id))
    | some entry =>
      match events id 0 entry.live input with
      | .error why => pure (.error why)
      | .ok (next,verdicts) =>
        pure (.ok ({st with runs := st.runs.set id.n {entry with live := next}},
          .played id verdicts next.view))
end Internal
end Effect4.Tool
