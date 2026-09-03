import Effect4.Target.TypeScript.RegionLower
import TypeScript.Structure

/-!
# Target.TypeScript.StructuredLower

Owner: the structured form of a checked flow (plan packet P-T9b, ruling R7).
`TypeScript.Structure` (lean4-typescript v0.4.0) turns the block graph into
labelled blocks, `while (true)` loops, `break` and `continue` when the graph
is reducible; the four shapes it emits are the tagged rules below. A graph
that is not reducible keeps the dispatch form (`dispatch-fallback`). Both
forms are checked against the same Flow-runner goldens on the host, so they
agree on every trace the harness and the property loop produce; a Lean
theorem that they agree on every flow is owed (`docs/TRACE-DAG.md`).
-/

open TypeScript

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow

namespace Lowering

/-- A loop header is a labelled `while (true)`. lowering: rule.structured-loop -/
def structuredLoop (label : String) (body : List Stmt) : Stmt :=
  .whileTrue (some label) body

/-- A merge node is a labelled block wrapping everything emitted before it.
lowering: rule.structured-merge -/
def structuredMerge (label : String) (body : List Stmt) : Stmt :=
  .labelled label body

/-- A backward transfer to a loop header. lowering: rule.structured-continue -/
def structuredContinue (label : String) : Stmt :=
  .continueTo (some label)

/-- A forward transfer to a merge node or loop header. lowering: rule.structured-break -/
def structuredBreak (label : String) : Stmt :=
  .breakTo (some label)

/-- A graph that is not reducible keeps the dispatch form.
lowering: rule.dispatch-fallback -/
def dispatchFallback (rows : ServiceRow) (program : FlowProgram) : Option ProgDecl :=
  Flow.lowerDispatch rows program

end Lowering

def structuredShapes : Structure.Shapes :=
  { loop := Lowering.structuredLoop, merge := Lowering.structuredMerge,
    continueTo := Lowering.structuredContinue, breakTo := Lowering.structuredBreak }

namespace Flow

/-- The position of a block in the declaration list. -/
def position (blocks : List (RawBlock String)) (id : BlockId) : Option Nat :=
  blocks.findIdx? fun block => block.id = id

/-- The block graph of a declaration list with an entry: nodes are positions. -/
def graphOf (blocks : List (RawBlock String)) (entry : BlockId) : Structure.Graph :=
  { size := blocks.length
    entry := (position blocks entry).getD 0
    succs := fun i => match blocks[i]? with
      | some block => block.term.successors.filterMap (position blocks)
      | none => [] }

/-- The structured statements of a declaration list, or `none` when the graph
is not reducible or a body has no lowering. -/
def structuredBody (rows : ServiceRow) (table : List OpSpec) (blocks : List (RawBlock String))
    (entry : BlockId) : Option (List Stmt) :=
  let g := graphOf blocks entry
  Structure.emitWith g structuredShapes fun i transfer => do
    let block ← blocks[i]?
    lowerBlockWith rows table block fun target values => do
      let t ← position blocks target
      let control ← transfer t
      pure (Lowering.paramMove block.id target values ++ control)

/-- Whether the erased graph is reducible. -/
def reducible (program : FlowProgram) : Bool :=
  Structure.reducible (graphOf program.flow.erase.blocks program.flow.erase.entry)

/-- The structured form, or `none` for an irreducible graph. -/
def lowerStructured (rows : ServiceRow) (program : FlowProgram) : Option ProgDecl := do
  let raw := program.flow.erase
  let stmts ← structuredBody rows program.table raw.blocks raw.entry
  let declarations := raw.blocks.flatMap fun block =>
    ((List.range block.params.length).zip block.params).map fun (index, ty) =>
      Stmt.letDefinite (paramVar block.id index) ty
  let acquire :=
    (if usesFamily program.table raw then [Lowering.serviceAcquire rows] else []) ++
    (if usesDecisions raw then [Lowering.serviceAcquire decisionsRows] else [])
  pure { doc := ["Lowered from the flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (structured form)."]
         name := program.name
         paramName := program.param.1
         paramType := program.param.2
         stmts := acquire ++ declarations ++
           [ Stmt.assign (paramVar raw.entry 0) (.ident program.param.1) ] ++ stmts }

/-- The structured form when the graph is reducible, else the dispatch form. -/
def lowerBest (rows : ServiceRow) (program : FlowProgram) : Option ProgDecl :=
  match lowerStructured rows program with
  | some decl => some decl
  | none => Lowering.dispatchFallback rows program

/-- The structured rules a flow exercises, after its dispatch rules. -/
def structuredRuleSet (rows : ServiceRow) (program : FlowProgram) : List Rule :=
  let raw := program.flow.erase
  let g := graphOf raw.blocks raw.entry
  let nodes := List.range g.size
  ruleSet rows program ++
    (if Structure.reducible g then
      (if nodes.any (Structure.isLoopHeader g) then [Rule.structuredLoop, Rule.structuredContinue] else []) ++
      (if nodes.any (fun n => Structure.isMerge g n || Structure.isLoopHeader g n) then
        [Rule.structuredMerge, Rule.structuredBreak] else [])
    else [Rule.dispatchFallback])

end Flow

namespace Region

/-- The structured form of a region program: each region's blocks are a graph
of their own, entered at the region body. -/
def lowerStructured (rows : ServiceRow) (program : RegionProgram) : Option ProgDecl := do
  let flow := program.flow.flow
  let rec cases (fuel : Nat) (label : Option RegionId) (entry : BlockId) : Option (List Stmt) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let blocks := flow.blocks.filter (·.region == label)
      let erased : List (RawBlock String) := blocks.map fun block =>
        { id := block.id, params := block.params, term := flow.eraseTerm block }
      let g := Flow.graphOf erased entry
      Structure.emitWith g structuredShapes fun i transfer => do
        let block ← blocks[i]?
        let var (v : Var) : Expr := .ident (Flow.paramVar block.id v.index)
        let move (target : BlockId) (values : List Expr) : Option (List Stmt) := do
          let t ← Flow.position erased target
          let control ← transfer t
          pure (Lowering.paramMove block.id target values ++ control)
        match block.term with
        | .plain term =>
            Flow.lowerBlockWith rows program.table { id := block.id, params := block.params, term := term } move
        | .enter region body args => do
            let row ← flow.row? region
            let inner ← cases fuel (some region) body
            let name := "r" ++ toString region.value
            let rest ← move row.continue_ [.ident name]
            some (Lowering.paramMove block.id body (args.map var) ++
              Lowering.regionEnter region inner ++ rest)
        | .acquire operation request release target args => do
            let region ← block.region
            let spec ← Flow.spec? program.table operation
            let releaser ← Flow.spec? program.table release
            guard (((rows.row? releaser.name).bind (·.error)).isNone)
            let answer := "a" ++ toString block.id.value
            let rest ← move target (args.map var ++ [.ident answer])
            some (Lowering.regionAcquire answer region (familyCall rows spec (var request))
                (fun resource => familyCall rows releaser resource) :: rest)
        | .leave value => some [Lowering.regionLeave (var value)]
  let stmts ← cases (flow.regions.length + 1) none flow.entry
  let declarations := flow.blocks.flatMap fun block =>
    ((List.range block.params.length).zip block.params).map fun (index, ty) =>
      Stmt.letDefinite (Flow.paramVar block.id index) ty
  let usesChoose := flow.blocks.any fun block =>
    match block.term with | .plain term => term.isChoose | _ => false
  let acquire :=
    (if (familyOps program.table flow).isEmpty then [] else [Lowering.serviceAcquire rows]) ++
    (if usesChoose then [Lowering.serviceAcquire decisionsRows] else []) ++
    (if flow.regions.isEmpty then [] else [Lowering.serviceAcquire regionsRows])
  pure { doc := ["Lowered from the region flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (structured form, nested scopes)."]
         name := program.name
         paramName := program.param.1
         paramType := program.param.2
         stmts := acquire ++ declarations ++
           [ Stmt.assign (Flow.paramVar flow.entry 0) (.ident program.param.1) ] ++ stmts }

def lowerBest (rows : ServiceRow) (program : RegionProgram) : Option ProgDecl :=
  match lowerStructured rows program with
  | some decl => some decl
  | none => lowerDispatch rows program

end Region

/-- One module of structured-form programs (dispatch where the graph is not
reducible), plain and region flows, over the declared families. -/
def structuredModules? (families : List (ServiceRow × List FlowProgram × List RegionProgram))
    (atoms : List Import := []) (style : Style := house0) : Option String := do
  let decls ← families.mapM fun (rows, programs, regionPrograms) => do
    let lowered ← programs.mapM (Flow.lowerBest rows)
    let loweredRegions ← regionPrograms.mapM (Region.lowerBest rows)
    pure (rows.classDecl :: rows.rowsDecl :: (lowered ++ loweredRegions).map Decl.prog)
  let chooses := families.any fun (_, programs, regionPrograms) =>
    programs.any (fun program => Flow.usesDecisions program.flow.erase) ||
    regionPrograms.any (fun program => program.flow.flow.blocks.any fun block =>
      match block.term with | .plain term => term.isChoose | _ => false)
  let regions := families.any fun (_, _, regionPrograms) =>
    regionPrograms.any fun program => !program.flow.flow.regions.isEmpty
  let result := families.any fun (rows, _, _) => rows.usesResult
  let target : Module :=
    { header := ["Generated by Effect4 (Effect v4 profile, structured form).", ""] ++
        hostPin.headerLines ++ ["", "Do not edit."]
      imports := .named (["Context", "Effect"] ++ (if regions then ["Exit"] else []) ++
        (if result then ["Result"] else [])) "effect" :: atoms
      decls := (if chooses then [decisionsRows.classDecl, decisionsRows.rowsDecl] else []) ++
        (if regions then [regionsRows.classDecl, regionsRows.rowsDecl] else []) ++
        decls.flatten }
  pure (Render.module style target)

end Effect4.Target.EffectV4
