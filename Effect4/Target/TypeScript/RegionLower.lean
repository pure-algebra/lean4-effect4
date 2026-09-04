import Effect4.Target.TypeScript.FlowLower

/-!
# Target.TypeScript.RegionLower

Owner: dispatch-form lowering of an admitted region flow (plan packet P-T7,
rulings R4 and R7). A region is a nested generator run in its own scope:

```ts
yield* regions.enter(1)
const r1 = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {
  let block1 = 1
  while (true) {
    switch (block1) {
      case 1: {
        const a1 = yield* Effect.acquireRelease(cell.acquire(b1p0),
          (a, exit) => regions.finalizer(1, exit).pipe(Effect.andThen(cell.release(a))))
        ...
      }
      case 2: { return b2p1 }
    }
  }
}), (exit) => regions.leave(1, exit)))
b3p0 = r1
block = 3
continue
```

`Effect.onExit` observes the body's exit and logs `leave`; `Effect.scoped`
then closes the scope, running every `acquireRelease` release latest-first
with that same exit, each logging `finalizer` before its own operation. The
syntax has no `try` arm, so no region ever lowers to `try/finally` (R4).

Since packet D3 the lowering is `Skeleton.renderList rows ∘ skeletonDispatch`,
and the body of a plain block inside a region is `Flow.skeletonBlockWith` with
the region's own block variable, so the two dispatch forms share one
definition instead of two copies.
-/

open TypeScript

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow
open Effects.Trace (Val)

/-- A region program: the table alphabet and its admitted region flow. -/
structure RegionProgram where
  name : String
  /-- binder, TypeScript type spelling -/
  param : String × String
  /-- TypeScript spelling of the result -/
  result : String
  table : List OpSpec
  flow : CheckedRegionFlow (tableAlphabet ⟨0⟩ table)
  /-- Whether the flow declares interrupt points (packet M2): before every
  `perform` and at every region `leave`. Off by default, so every program
  written before M2 lowers to the same bytes. -/
  interrupts : Bool := false
  /-- The regions whose bodies are uninterruptible. A point inside one defers
  (`Effect4.Flow.isMasked`); the host masks with `Effect.uninterruptible`. -/
  masked : List RegionId := []

/-- The `Regions` service every region reports to. -/
def regionsRows : ServiceRow :=
  { name := "Regions"
    ops := [ { name := "enter", index := 0, params := [("region", "Nat")],
               tsParams := [("region", "number")], answer := "Unit", tsAnswer := "void",
               cues := ["a region opens"] }
           , { name := "leave", index := 1, params := [("region", "Nat"), ("exit", "Exit")],
               tsParams := [("region", "number"), ("exit", "Exit.Exit<unknown, unknown>")],
               answer := "Unit", tsAnswer := "void", cues := ["a region closes with its body's exit"] }
           , { name := "finalizer", index := 2, params := [("region", "Nat"), ("exit", "Exit")],
               tsParams := [("region", "number"), ("exit", "Exit.Exit<unknown, unknown>")],
               answer := "Unit", tsAnswer := "void", cues := ["a release runs with the closing exit"] } ] }

namespace Region

/-- The block variable of the loop that runs a region's blocks. -/
def blockVarOf (region : RegionId) : String := "block" ++ toString region.value

/-- The body of one plain block inside the loop that owns `blockVar`: the
plain-flow body with the region's own transfer. -/
def skeletonPlain (table : List OpSpec) (interrupts : Bool) (blockVar : String)
    (block : RegionBlock String) (term : RawTerm) : Option (List Skeleton) :=
  Flow.skeletonBlockWith table interrupts { id := block.id, params := block.params, term := term }
    fun target values =>
      some (Lowering.paramMove block.id target values ++ Lowering.gotoIn blockVar target)

/-- The cases of every block labelled `label`, nested regions included;
`fuel` bounds the nesting depth. -/
def skeletonCases (rows : ServiceRow) (table : List OpSpec) (interrupts : Bool)
    (masked : List RegionId) (flow : RegionFlow String) :
    Nat → Option RegionId → String → Option (List (Nat × List Skeleton))
  | 0, _, _ => none
  | fuel + 1, label, blockVar =>
    (flow.blocks.filter (·.region == label)).mapM fun block => do
      let var (v : Var) : Slot := .param block.id v.index
      let body ← match block.term with
        | .plain term => skeletonPlain table interrupts blockVar block term
        | .enter region entry args => do
            let row ← flow.row? region
            let inner ← skeletonCases rows table interrupts masked flow fuel (some region)
              (blockVarOf region)
            let enter := if masked.contains region then Lowering.regionEnterMasked region
              else Lowering.regionEnter region
            some (Skeleton.enterBlock block.id :: Lowering.paramMove block.id entry (args.map var) ++
              enter
                [ Skeleton.letBlockIndex (blockVarOf region) entry
                , Lowering.dispatchLoopOn (blockVarOf region) inner ] ++
              [ Skeleton.assign (.param row.continue_ 0) (.region region) ] ++
              Lowering.gotoIn blockVar row.continue_)
        | .acquire operation request release target args => do
            let region ← block.region
            let spec ← Flow.spec? table operation
            let releaser ← Flow.spec? table release
            -- `Effect.acquireRelease` types its release `Effect<unknown, never, R>`:
            -- a release with an error row has no lowering (E4-TARGET-CE-012).
            guard (((rows.row? releaser.name).bind (·.error)).isNone)
            let answer : Slot := .answer block.id
            some (Skeleton.enterBlock block.id ::
              Lowering.regionAcquire answer region operation spec (var request) releaser ::
              (Lowering.paramMove block.id target (args.map var ++ [answer]) ++
               Lowering.gotoIn blockVar target))
        | .leave value => do
            let region ← block.region
            let point : List Skeleton :=
              if interrupts then [Lowering.interruptPoint (Effect4.Flow.Point.site (.leave region))]
              else []
            some (Skeleton.enterBlock block.id :: point ++ [Lowering.regionLeave (var value)])
      pure (Lowering.blockCase block.id body)

def familyOp? (table : List OpSpec) (id : OperationId) : Option OpSpec :=
  (Flow.spec? table id).bind fun spec => match spec.kind with | .family => some spec | _ => none

/-- The family operations a region flow performs, acquires, or releases. -/
def familyOps (table : List OpSpec) (flow : RegionFlow String) : List OpSpec :=
  flow.blocks.flatMap fun block =>
    match block.term with
    | .plain (.perform operation _ _ _) => (familyOp? table operation).toList
    | .acquire operation _ release _ _ =>
        (familyOp? table operation).toList ++ (familyOp? table release).toList
    | _ => []

/-- Whether any plain block of a region flow chooses. -/
def usesChoose (flow : RegionFlow String) : Bool :=
  flow.blocks.any fun block =>
    match block.term with | .plain term => term.isChoose | _ => false

/-- The parameter declarations of every block of a region flow. -/
def declarations (flow : RegionFlow String) : List Skeleton :=
  flow.blocks.flatMap fun block =>
    ((List.range block.params.length).zip block.params).map fun (index, ty) =>
      Skeleton.declare (.param block.id index) ty

/-- The services a region flow acquires at the top of its generator. -/
def acquisitions (rows : ServiceRow) (table : List OpSpec) (interrupts : Bool)
    (flow : RegionFlow String) : List Skeleton :=
  (if (familyOps table flow).isEmpty then [] else [Skeleton.acquireService rows]) ++
  (if usesChoose flow then [Skeleton.acquireService decisionsRows] else []) ++
  (if flow.regions.isEmpty then [] else [Skeleton.acquireService regionsRows]) ++
  (if interrupts then [Skeleton.acquireService interruptsRows] else [])

/-- The control skeleton of the dispatch form with nested scopes. -/
def skeletonDispatch (rows : ServiceRow) (program : RegionProgram) : Option (List Skeleton) := do
  let flow := program.flow.flow
  let cases ← skeletonCases rows program.table program.interrupts program.masked flow
    (flow.regions.length + 1) none "block"
  pure (acquisitions rows program.table program.interrupts flow ++ declarations flow ++
    [ Skeleton.assign (.param flow.entry 0) (.input program.param.1)
    , Skeleton.letBlockIndex "block" flow.entry
    , Lowering.dispatchLoop cases ])

/-- Lower an admitted region flow to the dispatch form with nested scopes. -/
def lowerDispatch (rows : ServiceRow) (program : RegionProgram) : Option ProgDecl := do
  let body ← skeletonDispatch rows program
  pure { doc := ["Lowered from the region flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (dispatch form, nested scopes)."]
         name := program.name
         paramName := program.param.1
         paramType := program.param.2
         stmts := Skeleton.renderList rows body }

/-- The rules a region flow exercises: the v2 rules of its erasure, then the
region rules it uses. -/
def ruleSet (rows : ServiceRow) (program : RegionProgram) : List Rule :=
  let erased : FlowProgram :=
    { name := program.name, param := program.param, result := program.result,
      table := program.table, flow := program.flow.checked, interrupts := program.interrupts }
  let flow := program.flow.flow
  let has (p : RegionTerm → Bool) : Bool := flow.blocks.any fun block => p block.term
  Flow.ruleSet rows erased ++
    (if has (fun t => match t with | .enter .. => true | _ => false) then [Rule.regionEnter] else []) ++
    (if has (fun t => match t with | .acquire .. => true | _ => false) then [Rule.regionAcquire] else []) ++
    (if has (fun t => match t with | .leave _ => true | _ => false) then [Rule.regionLeave] else []) ++
    (if has (fun t => match t with | .enter region .. => program.masked.contains region | _ => false)
      then [Rule.regionMasked] else [])

def errorChannel (rows : ServiceRow) (program : RegionProgram) : String :=
  let spellings := (familyOps program.table program.flow.flow).foldl (init := ([] : List String))
    fun acc spec =>
      match (rows.row? spec.name).bind (·.error) with
      | some (_, e) => if acc.contains e then acc else acc ++ [e]
      | none => acc
  if spellings.isEmpty then "never" else String.intercalate " | " spellings

def requirementChannel (rows : ServiceRow) (program : RegionProgram) : String :=
  let flow := program.flow.flow
  let parts :=
    (if (familyOps program.table flow).isEmpty then [] else [rows.name]) ++
    (if usesChoose flow then ["Decisions"] else []) ++
    (if flow.regions.isEmpty then [] else ["Regions"]) ++
    (if program.interrupts then ["Interrupts"] else [])
  if parts.isEmpty then "never" else String.intercalate " | " parts

def declarationLine (rows : ServiceRow) (program : RegionProgram) : String :=
  "export declare const " ++ program.name ++ ": (" ++ program.param.1 ++ ": " ++ program.param.2 ++
    ") => Effect.Effect<" ++ program.result ++ ", " ++ errorChannel rows program ++ ", " ++
    requirementChannel rows program ++ ">;"

/-! ## The multi-root entry, for a region flow

The same change `Flow` got (`FlowLower.lean`, `workshop/Deep/fork-lowering.md`
§(b)), for the form the fiber profile's programs actually take: spike S3's
witnesses and its compile are over `RegionFlow`
(`workshop/Deep/ForkFlow.lean`), so a fork that names a declared root names one
of *these* roots.

One extra refusal, which the plain form has no way to need: **a declared root
must sit outside every region.** The top-level dispatch loop runs exactly the
blocks whose label is `none` (`skeletonCases … none "block"`); a region's blocks
live in a nested generator with a block variable of their own, so a synthetic
case at the top level cannot continue at one. Admission already refuses an
*entry* inside a region (`Effects.RegionClause.entryInside`); this refuses the
rest, by returning `none` rather than emitting a case that jumps nowhere. -/

/-- The `Effect` type of a region flow: its three channels, as
`declarationLine` prints them. -/
def effectType (rows : ServiceRow) (program : RegionProgram) : String :=
  "Effect.Effect<" ++ program.result ++ ", " ++ errorChannel rows program ++ ", " ++
    requirementChannel rows program ++ ">"

/-- The binders a declared root is entered with: the program's own parameter for
the entry root, positional `p<i>` binders for every other. -/
def rootBinders (program : RegionProgram) (block : RegionBlock String) : List (String × String) :=
  if block.id = program.flow.flow.entry then [program.param]
  else ((List.range block.params.length).zip block.params).map
    fun (index, ty) => ("p" ++ toString index, ty)

/-- The control skeleton of the multi-root entry: the same acquisitions, the
same declarations and the same cases as `skeletonDispatch` -- literally the same
`skeletonCases` call -- with the entry assignment and the constant block index
replaced by the entry parameter and one synthetic case per declared root. -/
def skeletonEntry (rows : ServiceRow) (program : RegionProgram) : Option (List Skeleton) := do
  let flow := program.flow.flow
  let cases ← skeletonCases rows program.table program.interrupts program.masked flow
    (flow.regions.length + 1) none "block"
  let rootBlocks ← flow.roots.mapM flow.block?
  guard (rootBlocks.all fun block => block.region.isNone)
  guard (flow.blocks.all fun block => block.id.value < Lowering.rootEntryBase)
  pure (acquisitions rows program.table program.interrupts flow ++ declarations flow ++
    [ Lowering.enterAt "block" Flow.entryBinder
    , Lowering.dispatchLoop
        (rootBlocks.map (fun block =>
            Lowering.entryRootCase "block" Flow.entryBinder block.id block.params) ++ cases) ])

/-- Lower an admitted region flow to the parameterised entry generator. -/
def lowerEntry (rows : ServiceRow) (program : RegionProgram) : Option ProgDecl := do
  let body ← skeletonEntry rows program
  pure { doc := ["Lowered from the region flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (dispatch form, multi-root entry, nested scopes)."]
         name := Flow.entryName program.name
         paramName := Flow.entryBinder
         paramType := Flow.entryTy
         stmts := Skeleton.renderList rows body }

/-- The alias of one declared root of a region flow. -/
def rootAlias (rows : ServiceRow) (program : RegionProgram) (block : RegionBlock String) :
    ConstDecl :=
  let isEntry := block.id = program.flow.flow.entry
  Flow.entryAliasDecl
    (if isEntry then program.name else Flow.rootName program.name block.id)
    (Flow.entryName program.name)
    (Flow.rootAliasDoc program.name isEntry block.id "dispatch form, multi-root, nested scopes")
    (Lowering.rootEntryBase + block.id.value)
    (rootBinders program block)
    (effectType rows program)

/-- The declarations a region flow lowers to: the single exported generator for
one declared root, byte for byte (`lowerDispatch_single_root_eq`), and the
parameterised entry plus one alias per root plus the entry re-export for two or
more. -/
def lowerRoots (rows : ServiceRow) (program : RegionProgram) : Option (List Decl) :=
  if (program.flow.flow).roots.length ≤ 1 then
    (lowerDispatch rows program).map fun decl => [Decl.prog decl]
  else do
    let entry ← lowerEntry rows program
    let rootBlocks ← (program.flow.flow).roots.mapM (program.flow.flow).block?
    pure (Decl.prog entry ::
      rootBlocks.map (fun block => Decl.const (rootAlias rows program block)) ++
      [Decl.const (Flow.entryExportDecl program.name)])

/-- **The byte-identity receipt of the entry change, for region flows.** The
same statement as `Flow.lowerDispatch_single_root_eq` and for the same reason:
every region flow this library lowered before the fiber profile -- every one in
`RegionLowerContract`, `StructuredLowerContract` and the job goldens -- declares
exactly one root, so none of their bytes can move. -/
theorem lowerDispatch_single_root_eq (rows : ServiceRow) (program : RegionProgram)
    (single : (program.flow.flow).roots.length ≤ 1) :
    lowerRoots rows program = (lowerDispatch rows program).map fun decl => [Decl.prog decl] := by
  simp only [lowerRoots, if_pos single]

end Region

/-- One module of dispatch-form programs, plain flows and region flows, over
the declared families; `Decisions` and `Regions` are declared when used.

Each program contributes `lowerRoots`: one declaration for a single-root flow,
byte for byte what `lowerDispatch` emitted before the entry change
(`Flow.lowerDispatch_single_root_eq`, `Region.lowerDispatch_single_root_eq`), and
`1 + |roots| + 1` for a flow that declares more than one root. -/
def regionModules? (families : List (ServiceRow × List FlowProgram × List RegionProgram))
    (atoms : List Import := []) (style : Style := house0) : Option String := do
  let decls ← families.mapM fun (rows, programs, regionPrograms) => do
    let lowered ← programs.mapM (Flow.lowerRoots rows)
    let loweredRegions ← regionPrograms.mapM (Region.lowerRoots rows)
    pure (rows.classDecl :: rows.rowsDecl :: (lowered ++ loweredRegions).flatten)
  let chooses := families.any fun (_, programs, regionPrograms) =>
    programs.any (fun program => Flow.usesDecisions program.flow.erase) ||
    regionPrograms.any fun program => Region.usesChoose program.flow.flow
  let regions := families.any fun (_, _, regionPrograms) =>
    regionPrograms.any fun program => !program.flow.flow.regions.isEmpty
  let interrupts := families.any fun (_, programs, regionPrograms) =>
    programs.any (·.interrupts) || regionPrograms.any (·.interrupts)
  -- `Exit` used to be added by an `if regions` here; it now arrives with the
  -- `Regions` class, which is the only row that spells it, so the import line
  -- is a function of the module's own declared rows.
  let declared := (if chooses then [decisionsRows] else []) ++
    (if regions then [regionsRows] else []) ++
    (if interrupts then [interruptsRows] else []) ++ families.map (·.1)
  let target : Module :=
    { header := ["Generated by Effect4 (Effect v4 profile, dispatch form).", ""] ++
        hostPin.headerLines ++ ["", "Do not edit."]
      imports := .named (["Context", "Effect"] ++ moduleNamespaces declared atoms) "effect" :: atoms
      decls := (if chooses then [decisionsRows.classDecl, decisionsRows.rowsDecl] else []) ++
        (if regions then [regionsRows.classDecl, regionsRows.rowsDecl] else []) ++
        (if interrupts then [interruptsRows.classDecl, interruptsRows.rowsDecl] else []) ++
        decls.flatten }
  pure (Render.module style target)

end Effect4.Target.EffectV4
