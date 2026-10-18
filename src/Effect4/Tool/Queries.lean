import Effect4.Tool.Actions

/-!
# Tool.Queries — read-only answers

`Internal.query` answers a query from the raw state and never changes it. A suggestion uses the
same `keepExact` feed as a fill (`CheckCache.suggestPage`), a preview the admitted preview owner
(`Run.Preview`), and a `dry` query the action interpreter, whose next state it discards.
-/

set_option autoImplicit false
namespace Effect4.Tool
open Effect4 Effect4.Program Program.Check
namespace Internal

/-- **Preview** the document's program through the admitted preview owner. -/
def preview (d : Doc) (q : PreviewQuery) : Except Refusal PreviewAnswer := do
  let app := d.session.app.withHoles d.session.sketch.holes
  let program := d.session.sketch.program
  match Run.Preview.admit app program with
  | .error why => throw (.preview why)
  | .ok _ =>
    let host := Run.Preview.checkedTape app
    match q with
    | .settle tape limit => pure (.settled (Run.Tree.settle app.rows limit host tape program))
    | .frames tape limit => pure (.frames (Run.Tree.frames app.rows limit host tape program))
    | .explore budget width => pure (.explored (Run.Kit.explore app budget width program))

/-- **Inspect an address**: every field the table holds there; an address with no program refuses. -/
def inspection (d : Doc) (path : List Nat) : Except Refusal Inspection :=
  match (Node.eff d.session.sketch.program).at_ path with
  | some (.eff expected) =>
    let entry := d.session.table.find? fun e => decide (e.path = path)
    let refusal := entry.bind fun e => e.result.bind Checker.refusal
    .ok ⟨path,expected,sketchSigData d.session.sketch d.session.app path,
      d.session.focusAt path,entry,refusal⟩
  | _ => .error (.noProgram path)

/-- **Answer a query** from the raw state. -/
def query (o : Oracle) (st : Raw) : Query → Checked (Except Refusal Answer)
  | .doc at_ => pure (do
      let d ← requireDoc st
      match at_ with
      | none => pure (.doc (docView d))
      | some path =>
        let found ← inspection d path
        pure (.doc {docView d with inspection := some found}))
  | .history => pure (match st.doc with
      | none => .error .noDocument
      | some d => .ok (.history d.history))
  | .fills => pure (.ok (.fills (st.fills.map FillSet.anchor)
      (st.fills.map FillSet.pending |>.getD [])))
  | .suggest at_ place supplied cursor limit => do
    match checkedDoc st at_ with
    | .error why => pure (.error why)
    | .ok d =>
      match place.resolve d.session.app d.session.sketch with
      | .error why => pure (.error (.place why))
      | .ok (path,_) =>
        match d.session.focusAt path with
        | none => pure (.error (.suggest (.noFocus path)))
        | some focus =>
          let all := CheckCache.localCandidates d path focus supplied
          let page := (all.drop cursor).take limit
          match ← CheckCache.suggestPage o d focus path page with
          | .error why => pure (.error (.suggest why))
          | .ok items =>
            let candidates := items.map fun item =>
              Candidate.mk item.program item.sourcePath item.key item.evidence
            let next := if cursor+limit < all.length then some (cursor+limit) else none
            pure (.ok (.suggested candidates next))
  | .run id form => pure (match st.runs[id.n]? with
      | none => .error (.noRun id)
      | some entry => .ok (.run id (match form with
        | .view => .view entry.live.view
        | .record => .record (LiveRecord.save entry.live)
        | .journal => .journal entry.live.run.journal)))
  | .preview q => pure (match st.doc with
      | none => .error .noDocument
      | some d => (preview d q).map Answer.preview)
  | .dry a => do
    let result ← action o st a
    pure (.ok (.dry (result.map Prod.snd)))
  | .discover => pure (.ok (.methods supportedMethods))
end Internal
end Effect4.Tool
