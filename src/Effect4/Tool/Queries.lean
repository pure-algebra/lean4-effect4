import Effect4.Tool.Actions

/-!
# Tool.Queries — read-only answers

`Internal.query` answers a query from the raw state and never changes it. A suggestion uses the
same `keepExact` feed as a fill (`Suggest.page`), a preview the admitted preview owner
(`Run.Preview`), and a `dry` query the action interpreter, whose next state it discards. The
address table is the session's own (`SourceSession.table`, the sketch's source table), and its
addresses are the program's (`Node.addresses`). A node's term slots are read where the table reads
the node: in the expansion's part that holds the address (`Sketch.tableEntry`).
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

/-- Every term slot, in declaration order (`mem_allSlots`). -/
def allSlots : List ExtSlot := [.catchIfTest, .iterateTest, .iterateStep, .iterateResult, .opTerm]

/-- Helper of `slots`: every term slot is listed. A new slot fails this proof until `allSlots`
lists it. -/
theorem mem_allSlots (slot : ExtSlot) : slot ∈ allSlots := by
  cases slot <;> decide

/-- **The term slots of the node at an address**: the one slot named, or every slot. Each is read
in the expansion's part that holds the address, at the part's signature and environment, as the
table reads the node (`Sketch.tableEntry`): the slot's term (`Node.extSlotTerm`), its environment
(`Node.extSlotEnv`) and the term's type there (`termTy`). The flag says the part's focus is typed
there, the premise of `hasTy_extSlotEnv`. A node in no part (the spine of a block's bodies) has
no slot; an address with no program refuses. -/
def slots (d : Doc) (path : List Nat) (only : Option ExtSlot) :
    Except Refusal (Bool × List SlotView) :=
  let x := d.session.sketch.expand
  match (Node.eff d.session.sketch.program).at_ path with
  | some (.eff _) =>
    match x.program.partAt (d.session.app.withHoles x.holes).signature [] path with
    | none => .ok (false,[])
    | some (part,rest) =>
      match (Node.eff part.program).at_ rest,
        (Node.eff part.program).envAt part.sig (.env part.env) rest with
      | some node, some (.env env) =>
        .ok ((focusAt part.sig part.env part.program rest).isSome,
          ((only.map ([·])).getD allSlots).filterMap fun slot =>
            let term := node.extSlotTerm part.sig slot
            let slotEnv := node.extSlotEnv part.sig env slot
            if term.isSome || slotEnv.isSome then
              some ⟨slot,term,slotEnv,term.bind fun t => slotEnv.bind fun e => termTy part.sig e t⟩
            else none)
      | _, _ => .ok (false,[])
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
        match ← Suggest.page o d path supplied cursor limit with
        | .error why => pure (.error (.suggest why))
        | .ok (items,next) => pure (.ok (.suggested items next))
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
  | .table => pure ((requireDoc st).map fun d => .table d.session.table)
  | .addresses => pure ((requireDoc st).map fun d =>
      .addresses (Node.addresses (.eff d.session.sketch.program)))
  | .slots path only => pure (do
      let d ← requireDoc st
      let found ← slots d path only
      pure (.slots path found.1 found.2))
end Internal
end Effect4.Tool
