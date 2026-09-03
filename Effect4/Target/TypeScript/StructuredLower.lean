import Effect4.Target.TypeScript.RegionLower

/-!
# Target.TypeScript.StructuredLower

Owner: the structured form of a checked flow (plan packet P-T9b, ruling R7).
`TypeScript.Structure` (lean4-typescript v0.4.1) turns the block graph into
labelled blocks, `while (true)` loops, `break` and `continue` when the graph
is reducible; the four shapes it emits are the tagged rules of
`Skeleton.lean`. A graph that is not reducible keeps the dispatch form
(`dispatch-fallback`).

Since packet D3 the shapes are instantiated at `Skeleton` rather than at
`Stmt`, through `Structuring.emitWith` — the pinned package's algorithm with
the statement type as a parameter, pinned to it by `Structuring.emitWith_eq`.
Both forms are still checked against the same Flow-runner goldens on the host,
and `Skeleton.denote` (`Skeleton.lean` §7) is now the Lean subject over which
their agreement is stated; `docs/TRACE-DAG.md` records what is proved and what
is owed.
-/

open TypeScript

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow

namespace Lowering

/-- A graph that is not reducible keeps the dispatch form.
lowering: rule.dispatch-fallback -/
def dispatchFallback (rows : ServiceRow) (program : FlowProgram) : Option ProgDecl :=
  Flow.lowerDispatch rows program

end Lowering

/-- The four structured shapes, at the control skeleton. -/
def structuredShapes : Structuring.Shapes Skeleton :=
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

/-- The structured skeleton of a declaration list, or `none` when the graph is
not reducible or a body has no lowering. -/
def skeletonBody (table : List OpSpec) (blocks : List (RawBlock String)) (entry : BlockId) :
    Option (List Skeleton) :=
  let g := graphOf blocks entry
  Structuring.emitWith g structuredShapes fun i transfer => do
    let block ← blocks[i]?
    skeletonBlockWith table block fun target values => do
      let t ← position blocks target
      let control ← transfer t
      pure (Lowering.paramMove block.id target values ++ control)

/-- Whether the erased graph is reducible. -/
def reducible (program : FlowProgram) : Bool :=
  Structure.reducible (graphOf program.flow.erase.blocks program.flow.erase.entry)

/-- The control skeleton of the structured form, or `none` for an irreducible
graph. -/
def skeletonStructured (rows : ServiceRow) (program : FlowProgram) : Option (List Skeleton) := do
  let raw := program.flow.erase
  let body ← skeletonBody program.table raw.blocks raw.entry
  pure (acquisitions rows program.table raw ++ declarations raw.blocks ++
    [Skeleton.assign (.param raw.entry 0) (.input program.param.1)] ++ body)

/-- The structured form, or `none` for an irreducible graph. -/
def lowerStructured (rows : ServiceRow) (program : FlowProgram) : Option ProgDecl := do
  let body ← skeletonStructured rows program
  pure { doc := ["Lowered from the flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (structured form)."]
         name := program.name
         paramName := program.param.1
         paramType := program.param.2
         stmts := Skeleton.renderList rows body }

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

/-- The structured skeleton of a region program: each region's blocks are a
graph of their own, entered at the region body. -/
def skeletonStructuredBody (rows : ServiceRow) (table : List OpSpec) (flow : RegionFlow String) :
    Nat → Option RegionId → BlockId → Option (List Skeleton)
  | 0, _, _ => none
  | fuel + 1, label, entry =>
    let blocks := flow.blocks.filter (·.region == label)
    let erased : List (RawBlock String) := blocks.map fun block =>
      { id := block.id, params := block.params, term := flow.eraseTerm block }
    let g := Flow.graphOf erased entry
    Structuring.emitWith g structuredShapes fun i transfer => do
      let block ← blocks[i]?
      let var (v : Var) : Slot := .param block.id v.index
      let move (target : BlockId) (values : List Slot) : Option (List Skeleton) := do
        let t ← Flow.position erased target
        let control ← transfer t
        pure (Lowering.paramMove block.id target values ++ control)
      match block.term with
      | .plain term =>
          Flow.skeletonBlockWith table { id := block.id, params := block.params, term := term } move
      | .enter region entry' args => do
          let row ← flow.row? region
          let inner ← skeletonStructuredBody rows table flow fuel (some region) entry'
          let rest ← move row.continue_ [.region region]
          some (Skeleton.enterBlock block.id :: Lowering.paramMove block.id entry' (args.map var) ++
            Lowering.regionEnter region inner ++ rest)
      | .acquire operation request release target args => do
          let region ← block.region
          let spec ← Flow.spec? table operation
          let releaser ← Flow.spec? table release
          guard (((rows.row? releaser.name).bind (·.error)).isNone)
          let answer : Slot := .answer block.id
          let rest ← move target (args.map var ++ [answer])
          some (Skeleton.enterBlock block.id ::
            Lowering.regionAcquire answer region operation spec (var request) releaser :: rest)
      | .leave value => some [Skeleton.enterBlock block.id, Lowering.regionLeave (var value)]

/-- The control skeleton of the structured form of a region program. -/
def skeletonStructured (rows : ServiceRow) (program : RegionProgram) : Option (List Skeleton) := do
  let flow := program.flow.flow
  let body ← skeletonStructuredBody rows program.table flow (flow.regions.length + 1) none flow.entry
  pure (acquisitions rows program.table flow ++ declarations flow ++
    [Skeleton.assign (.param flow.entry 0) (.input program.param.1)] ++ body)

/-- The structured form of a region program. -/
def lowerStructured (rows : ServiceRow) (program : RegionProgram) : Option ProgDecl := do
  let body ← skeletonStructured rows program
  pure { doc := ["Lowered from the region flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (structured form, nested scopes)."]
         name := program.name
         paramName := program.param.1
         paramType := program.param.2
         stmts := Skeleton.renderList rows body }

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
    regionPrograms.any fun program => Region.usesChoose program.flow.flow
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
