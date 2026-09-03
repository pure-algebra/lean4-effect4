import Effect4.Target.TypeScript.FlowLower
import Effect4.Flow.Region

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

namespace Lowering

/-- Open a region: report it, then run its blocks as a nested generator in its
own scope whose exit `Effect.onExit` reports as `leave`; the value it returns
becomes the parameter of the region's `continue_` block.
lowering: rule.region-enter -/
def regionEnter (region : RegionId) (body : List Stmt) : List Stmt :=
  let name := "r" ++ toString region.value
  [ .yieldDiscard (.call (.ident "regions.enter") [.int region.value])
  , .scopedGen name body
      (.lambda ["exit"] (.call (.ident "regions.leave") [.int region.value, .ident "exit"])) ]

/-- Acquire inside a region: `Effect.acquireRelease` registers the release in
the enclosing scope; the release reports `finalizer` with the closing exit
before running its own operation. lowering: rule.region-acquire -/
def regionAcquire (answer : String) (region : RegionId) (acquire : Expr) (release : Expr → Expr) :
    Stmt :=
  .constYield answer (.call (.ident "Effect.acquireRelease")
    [ acquire
    , .lambda ["a", "exit"]
        (.method (.call (.ident "regions.finalizer") [.int region.value, .ident "exit"]) "pipe"
          [.call (.ident "Effect.andThen") [release (.ident "a")]]) ])

/-- Leave a region: the nested generator returns the value.
lowering: rule.region-leave -/
def regionLeave (value : Expr) : Stmt :=
  .ret value

/-- Transfer to `target` in the loop that owns `blockVar`. -/
def gotoIn (blockVar : String) (target : BlockId) : List Stmt :=
  [.assign blockVar (.int target.value), .continueTo none]

end Lowering

namespace Region

/-- The call of a family operation on a request expression. -/
def familyCall (rows : ServiceRow) (spec : OpSpec) (request : Expr) : Expr :=
  if spec.requestTy == "void" then Lowering.nullaryValue rows.receiver spec.name
  else Lowering.performCall rows.receiver spec.name [request]

/-- The body of one plain block inside the loop that owns `blockVar`. -/
def lowerPlain (rows : ServiceRow) (table : List OpSpec) (blockVar : String)
    (block : RegionBlock String) (term : RawTerm) : Option (List Stmt) :=
  let var (v : Var) : Expr := .ident (Flow.paramVar block.id v.index)
  let transfer (target : BlockId) (values : List Expr) : List Stmt :=
    Lowering.paramMove block.id target values ++ Lowering.gotoIn blockVar target
  match term with
  | .ret value => some [Lowering.flowRet (var value)]
  | .jump target args => some (transfer target (args.map var))
  | .perform operation request target args => do
      let spec ← Flow.spec? table operation
      let answer := "a" ++ toString block.id.value
      let head ← match spec.kind with
        | .family => some (Lowering.flowPerform answer (familyCall rows spec (var request)))
        | .atom => some (Lowering.flowAtom answer spec.name (var request))
        | .lit value => (Flow.literal? value).map (Lowering.flowLiteral answer)
      some (head :: transfer target (args.map var ++ [.ident answer]))
  | .choose decision left right args =>
      let name := "c" ++ toString block.id.value
      some (Lowering.chooseIf name decision
        (transfer left (args.map var)) (transfer right (args.map var)))

/-- The cases of every block labelled `label`, nested regions included;
`fuel` bounds the nesting depth. -/
def lowerCases (rows : ServiceRow) (table : List OpSpec) (flow : RegionFlow String) :
    Nat → Option RegionId → String → Option (List (Nat × List Stmt))
  | 0, _, _ => none
  | fuel + 1, label, blockVar =>
    (flow.blocks.filter (·.region == label)).mapM fun block => do
      let var (v : Var) : Expr := .ident (Flow.paramVar block.id v.index)
      let body ← match block.term with
        | .plain term => lowerPlain rows table blockVar block term
        | .enter region body args => do
            let row ← flow.row? region
            let inner ← lowerCases rows table flow fuel (some region) ("block" ++ toString region.value)
            let name := "r" ++ toString region.value
            some (Lowering.paramMove block.id body (args.map var) ++
              Lowering.regionEnter region
                [ .letInit ("block" ++ toString region.value) (.int body.value)
                , Lowering.dispatchLoopOn ("block" ++ toString region.value) inner ] ++
              [ .assign (Flow.paramVar row.continue_ 0) (.ident name) ] ++
              Lowering.gotoIn blockVar row.continue_)
        | .acquire operation request release target args => do
            let region ← block.region
            let spec ← Flow.spec? table operation
            let releaser ← Flow.spec? table release
            -- `Effect.acquireRelease` types its release `Effect<unknown, never, R>`:
            -- a release with an error row has no lowering (E4-TARGET-CE-012).
            guard (((rows.row? releaser.name).bind (·.error)).isNone)
            let answer := "a" ++ toString block.id.value
            some (Lowering.regionAcquire answer region (familyCall rows spec (var request))
                (fun resource => familyCall rows releaser resource) ::
              (Lowering.paramMove block.id target (args.map var ++ [.ident answer]) ++
               Lowering.gotoIn blockVar target))
        | .leave value => some [Lowering.regionLeave (var value)]
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

/-- Lower an admitted region flow to the dispatch form with nested scopes. -/
def lowerDispatch (rows : ServiceRow) (program : RegionProgram) : Option ProgDecl := do
  let flow := program.flow.flow
  let cases ← lowerCases rows program.table flow (flow.regions.length + 1) none "block"
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
                 "` (dispatch form, nested scopes)."]
         name := program.name
         paramName := program.param.1
         paramType := program.param.2
         stmts := acquire ++ declarations ++
           [ Stmt.assign (Flow.paramVar flow.entry 0) (.ident program.param.1)
           , Stmt.letInit "block" (.int flow.entry.value)
           , Lowering.dispatchLoop cases ] }

/-- The rules a region flow exercises: the v2 rules of its erasure, then the
region rules it uses. -/
def ruleSet (rows : ServiceRow) (program : RegionProgram) : List Rule :=
  let erased : FlowProgram :=
    { name := program.name, param := program.param, result := program.result,
      table := program.table, flow := program.flow.checked }
  let flow := program.flow.flow
  let has (p : RegionTerm → Bool) : Bool := flow.blocks.any fun block => p block.term
  Flow.ruleSet rows erased ++
    (if has (fun t => match t with | .enter .. => true | _ => false) then [Rule.regionEnter] else []) ++
    (if has (fun t => match t with | .acquire .. => true | _ => false) then [Rule.regionAcquire] else []) ++
    (if has (fun t => match t with | .leave _ => true | _ => false) then [Rule.regionLeave] else [])

def errorChannel (rows : ServiceRow) (program : RegionProgram) : String :=
  let spellings := (familyOps program.table program.flow.flow).foldl (init := ([] : List String))
    fun acc spec =>
      match (rows.row? spec.name).bind (·.error) with
      | some (_, e) => if acc.contains e then acc else acc ++ [e]
      | none => acc
  if spellings.isEmpty then "never" else String.intercalate " | " spellings

def requirementChannel (rows : ServiceRow) (program : RegionProgram) : String :=
  let flow := program.flow.flow
  let usesChoose := flow.blocks.any fun block =>
    match block.term with | .plain term => term.isChoose | _ => false
  let parts :=
    (if (familyOps program.table flow).isEmpty then [] else [rows.name]) ++
    (if usesChoose then ["Decisions"] else []) ++
    (if flow.regions.isEmpty then [] else ["Regions"])
  if parts.isEmpty then "never" else String.intercalate " | " parts

def declarationLine (rows : ServiceRow) (program : RegionProgram) : String :=
  "export declare const " ++ program.name ++ ": (" ++ program.param.1 ++ ": " ++ program.param.2 ++
    ") => Effect.Effect<" ++ program.result ++ ", " ++ errorChannel rows program ++ ", " ++
    requirementChannel rows program ++ ">;"

end Region

/-- One module of dispatch-form programs, plain flows and region flows, over
the declared families; `Decisions` and `Regions` are declared when used. -/
def regionModules? (families : List (ServiceRow × List FlowProgram × List RegionProgram))
    (atoms : List Import := []) (style : Style := house0) : Option String := do
  let decls ← families.mapM fun (rows, programs, regionPrograms) => do
    let lowered ← programs.mapM (Flow.lowerDispatch rows)
    let loweredRegions ← regionPrograms.mapM (Region.lowerDispatch rows)
    pure (rows.classDecl :: rows.rowsDecl :: (lowered ++ loweredRegions).map Decl.prog)
  let chooses := families.any fun (_, programs, regionPrograms) =>
    programs.any (fun program => Flow.usesDecisions program.flow.erase) ||
    regionPrograms.any (fun program => program.flow.flow.blocks.any fun block =>
      match block.term with | .plain term => term.isChoose | _ => false)
  let regions := families.any fun (_, _, regionPrograms) =>
    regionPrograms.any fun program => !program.flow.flow.regions.isEmpty
  let result := families.any fun (rows, _, _) => rows.usesResult
  let target : Module :=
    { header := ["Generated by Effect4 (Effect v4 profile, dispatch form).", ""] ++
        hostPin.headerLines ++ ["", "Do not edit."]
      imports := .named (["Context", "Effect"] ++ (if regions then ["Exit"] else []) ++
        (if result then ["Result"] else [])) "effect" :: atoms
      decls := (if chooses then [decisionsRows.classDecl, decisionsRows.rowsDecl] else []) ++
        (if regions then [regionsRows.classDecl, regionsRows.rowsDecl] else []) ++
        decls.flatten }
  pure (Render.module style target)

end Effect4.Target.EffectV4
