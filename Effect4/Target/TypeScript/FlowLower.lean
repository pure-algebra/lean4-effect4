import Effect4.Target.TypeScript.SkeletonRender

/-!
# Target.TypeScript.FlowLower

Owner: dispatch-form lowering of an admitted Flow graph into an Effect v4
generator (plan packet P-T9a, ruling R7). The graph language is Flow v3
(lean4-effects v0.7.0): `skeletonBlockWith` lowers its `performCatch` and
`branch` terms as well as the v2 shapes. Every admitted graph lowers to

```ts
export const incr = (n: number) =>
  Effect.gen(function* () {
    const cell = yield* Cell
    let b0p0!: number
    ...
    b0p0 = n
    let block = 0
    while (true) {
      switch (block) {
        case 0: { const a0 = yield* cell.get; b1p0 = b0p0; b1p1 = a0; block = 1; continue }
        ...
        case 5: { return b5p3 }
      }
    }
  })
```

Block parameters are variables `b<block>p<index>`; a `perform` answers into
`a<block>`, a `choose` decides into `c<block>` from the `Decisions` service.
Passing the argument list is a sequentialized parallel move: a self-edge reads
every source into a temporary before assigning. The syntax has no `try` arm,
so cleanup can never lower to `try/finally` (R4) by construction. The
structured form (P-T9b) is an optimization behind a reducibility check and
must agree with this form on every trace.

Since packet D3 the lowering is `Skeleton.renderList rows ∘ skeletonDispatch`:
`skeletonDispatch` builds the control skeleton (`Skeleton.lean`), which is the
object the agreement theorems are stated over, and `renderList` spells it. No
`Stmt` is constructed here.
-/

open TypeScript

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow
open Effects.Trace (Val)

/-- A flow program: the table alphabet it runs against and its admitted graph. -/
structure FlowProgram where
  name : String
  /-- binder, TypeScript type spelling -/
  param : String × String
  /-- TypeScript spelling of the result -/
  result : String
  table : List OpSpec
  flow : CheckedFlow (tableAlphabet ⟨0⟩ table)
  /-- Whether the flow declares interrupt points (packet M2). Off by default,
  so a program that does not declare them lowers to the bytes it lowered to
  before this field existed. -/
  interrupts : Bool := false

/-- The `Decisions` service every `choose` asks. -/
def decisionsRows : ServiceRow :=
  { name := "Decisions"
    ops := [ { name := "choose", index := 0, params := [("site", "Nat")],
               tsParams := [("site", "number")], answer := "Bool", tsAnswer := "boolean",
               cues := ["decide a choice site from the tape"] }
           , { name := "report", index := 1, params := [("site", "Nat"), ("branch", "Bool")],
               tsParams := [("site", "number"), ("branch", "boolean")],
               answer := "Unit", tsAnswer := "void",
               cues := ["a value branch reports the decision it already took"] } ] }

/-- The `Interrupts` service every interrupt point asks. `point` answers
nothing: the host service either interrupts the running fiber at that site or
lets the run continue. -/
def interruptsRows : ServiceRow :=
  { name := "Interrupts"
    ops := [{ name := "point", index := 0, params := [("site", "Nat")],
              tsParams := [("site", "number")], answer := "Unit", tsAnswer := "void",
              cues := ["an interruptible point of the run"] }] }

namespace Flow

/-- The body of one block, its answer or decision followed by the move and
the control transfer `transfer target values` supplies. When `interrupts` is
set, a `perform` is preceded by its interrupt point. -/
def skeletonBlockWith (table : List OpSpec) (interrupts : Bool) (block : RawBlock String)
    (transfer : BlockId → List Slot → Option (List Skeleton)) : Option (List Skeleton) :=
  let var (v : Var) : Slot := .param block.id v.index
  let entered (body : List Skeleton) : List Skeleton := Skeleton.enterBlock block.id :: body
  match block.term with
  | .ret value => some (entered [Lowering.flowRet (var value)])
  | .jump target args => (transfer target (args.map var)).map entered
  | .perform operation request target args => do
      let spec ← spec? table operation
      let answer : Slot := .answer block.id
      let head ← match spec.kind with
        | .family => some (Lowering.flowPerform answer operation spec (var request))
        | .atom => some (Lowering.flowAtom answer operation spec (var request))
        | .lit value =>
            (literal? value).map fun _ => Lowering.flowLiteral answer operation (var request) value
      let rest ← transfer target (args.map var ++ [answer])
      let point : List Skeleton :=
        if interrupts then [Lowering.interruptPoint (Effect4.Flow.Point.site (.perform block.id))]
        else []
      some (entered (point ++ head :: rest))
  | .choose decision left right args => do
      let name : Slot := .decision block.id
      let toLeft ← transfer left (args.map var)
      let toRight ← transfer right (args.map var)
      some (entered (Lowering.chooseIf name decision toLeft toRight))
  | .performCatch operation request target args onError errorArgs => do
      let spec ← spec? table operation
      -- Only a family operation can fail: an atom and a literal have no error
      -- row, so a caught perform of either has no lowering.
      let _ ← match spec.kind with | .family => some () | _ => none
      let answer : Slot := .answer block.id
      let value : Slot := .catchValue block.id
      let error : Slot := .catchError block.id
      let toOk ← transfer target (args.map var ++ [value])
      let toError ← transfer onError (errorArgs.map var ++ [error])
      let point : List Skeleton :=
        if interrupts then [Lowering.interruptPoint (Effect4.Flow.Point.site (.perform block.id))]
        else []
      some (entered (point ++
        Lowering.performCatchResult answer value error operation spec (var request) toOk toError))
  | .branch test site onTrue onFalse args => do
      let toTrue ← transfer onTrue (args.map var)
      let toFalse ← transfer onFalse (args.map var)
      some (entered (Lowering.branchIf (var test) site toTrue toFalse))

/-- The dispatch-form transfer: the move, then `block = target; continue`. -/
def dispatchTransfer (source : BlockId) (target : BlockId) (values : List Slot) :
    Option (List Skeleton) :=
  some (Lowering.paramMove source target values ++ Lowering.goto target)

/-- The body of one block in the dispatch form. -/
def skeletonBlock (table : List OpSpec) (interrupts : Bool) (block : RawBlock String) :
    Option (List Skeleton) :=
  skeletonBlockWith table interrupts block (dispatchTransfer block.id)

/-- The spelled body of one block in the dispatch form. -/
def lowerBlock (rows : ServiceRow) (table : List OpSpec) (interrupts : Bool)
    (block : RawBlock String) : Option (List Stmt) :=
  (Skeleton.renderList rows) <$> skeletonBlock table interrupts block

/-- Whether a block performs a family operation. -/
def performsFamily (table : List OpSpec) (block : RawBlock String) : Bool :=
  match block.term with
  | .perform operation _ _ _ =>
      match spec? table operation with
      | some spec => match spec.kind with | .family => true | _ => false
      | none => false
  | _ => false

def usesFamily (table : List OpSpec) (raw : RawFlow String) : Bool :=
  raw.blocks.any (performsFamily table)

def usesDecisions (raw : RawFlow String) : Bool :=
  raw.blocks.any (·.term.isChoose)

/-- The parameter declarations of every block of a graph. -/
def declarations (blocks : List (RawBlock String)) : List Skeleton :=
  blocks.flatMap fun block =>
    ((List.range block.params.length).zip block.params).map fun (index, ty) =>
      Skeleton.declare (.param block.id index) ty

/-- The services a plain flow acquires at the top of its generator. -/
def acquisitions (rows : ServiceRow) (table : List OpSpec) (interrupts : Bool)
    (raw : RawFlow String) : List Skeleton :=
  (if usesFamily table raw then [Skeleton.acquireService rows] else []) ++
  (if usesDecisions raw then [Skeleton.acquireService decisionsRows] else []) ++
  (if interrupts then [Skeleton.acquireService interruptsRows] else [])

/-- The control skeleton of the dispatch form. Refuses a literal without a
spelling or an operation outside the table (admission already refuses the
latter). -/
def skeletonDispatch (rows : ServiceRow) (program : FlowProgram) : Option (List Skeleton) := do
  let raw := program.flow.erase
  let cases ← raw.blocks.mapM fun block => do
    let body ← skeletonBlock program.table program.interrupts block
    pure (Lowering.blockCase block.id body)
  pure (acquisitions rows program.table program.interrupts raw ++ declarations raw.blocks ++
    [ Skeleton.assign (.param raw.entry 0) (.input program.param.1)
    , Skeleton.letBlockIndex "block" raw.entry
    , Lowering.dispatchLoop cases ])

/-- Lower an admitted graph to the dispatch form: the skeleton, spelled. -/
def lowerDispatch (rows : ServiceRow) (program : FlowProgram) : Option ProgDecl := do
  let body ← skeletonDispatch rows program
  pure { doc := ["Lowered from the flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (dispatch form)."]
         name := program.name
         paramName := program.param.1
         paramType := program.param.2
         stmts := Skeleton.renderList rows body }

/-- The rules a flow exercises, in first-use order. -/
def ruleSet (rows : ServiceRow) (program : FlowProgram) : List Rule :=
  let raw := program.flow.erase
  let step (acc : List Rule) (rule : Rule) : List Rule :=
    if acc.contains rule then acc else acc ++ [rule]
  let move (acc : List Rule) (arity : Nat) : List Rule :=
    if arity = 0 then acc else step acc .paramMove
  let start :=
    (if usesFamily program.table raw then [Rule.serviceAcquire] else []) ++
      [.dispatchLoop, .blockCase] ++ (if program.interrupts then [Rule.interruptPoint] else [])
  raw.blocks.foldl (init := start) fun acc block =>
    match block.term with
    | .ret _ => step acc .flowRet
    | .jump _ args => move acc args.length
    | .perform operation _ _ args =>
        let acc := match spec? program.table operation with
          | some spec => match spec.kind with
            | .family =>
                let acc := step (step acc .flowPerform)
                  (if spec.requestTy == "void" then .nullaryValue else .performCall)
                if spec.arity == 1 then acc else step acc .performTuple
            | .atom => step acc .flowAtom
            | .lit _ => step acc .flowLiteral
          | none => acc
        move acc (args.length + 1)
    | .choose _ _ _ args => move (step acc .chooseIf) args.length
    | .performCatch operation _ _ args _ errorArgs =>
        let acc := match spec? program.table operation with
          | some spec =>
              step (step acc .performCatch)
                (if spec.requestTy == "void" then .nullaryValue else .performCall)
          | none => acc
        move (move acc (args.length + 1)) (errorArgs.length + 1)
    | .branch _ _ _ _ args => move (step acc .branchIf) args.length
  |> fun acc => let _ := rows; acc

/-- The error channel of a flow: the error spellings of the family operations
it performs, in first-use order; `never` when none. -/
def errorChannel (rows : ServiceRow) (program : FlowProgram) : String :=
  let spellings := program.flow.erase.blocks.foldl (init := ([] : List String)) fun acc block =>
    match block.term with
    | .perform operation _ _ _ =>
        match spec? program.table operation with
        | some spec =>
            match (rows.row? spec.name).bind (·.error) with
            | some (_, e) => if acc.contains e then acc else acc ++ [e]
            | none => acc
        | none => acc
    | _ => acc
  if spellings.isEmpty then "never" else String.intercalate " | " spellings

/-- The requirement channel: the family when performed, `Decisions` when chosen. -/
def requirementChannel (rows : ServiceRow) (program : FlowProgram) : String :=
  let raw := program.flow.erase
  let parts :=
    (if usesFamily program.table raw then [rows.name] else []) ++
    (if usesDecisions raw then ["Decisions"] else []) ++
    (if program.interrupts then ["Interrupts"] else [])
  if parts.isEmpty then "never" else String.intercalate " | " parts

/-- The declaration line the pinned compiler must emit for the lowered flow. -/
def declarationLine (rows : ServiceRow) (program : FlowProgram) : String :=
  "export declare const " ++ program.name ++ ": (" ++ program.param.1 ++ ": " ++ program.param.2 ++
    ") => Effect.Effect<" ++ program.result ++ ", " ++ errorChannel rows program ++ ", " ++
    requirementChannel rows program ++ ">;"

end Flow

/-- One module of dispatch-form programs over the declared families, with the
`Decisions` service when any program chooses. -/
def flowModules? (families : List (ServiceRow × List FlowProgram))
    (atoms : List Import := []) (style : Style := house0) : Option String := do
  let decls ← families.mapM fun (rows, programs) => do
    let lowered ← programs.mapM (Flow.lowerDispatch rows)
    pure (rows.classDecl :: rows.rowsDecl :: lowered.map Decl.prog)
  let chooses := families.any fun (_, programs) =>
    programs.any fun program => Flow.usesDecisions program.flow.erase
  let interrupts := families.any fun (_, programs) => programs.any (·.interrupts)
  let result := families.any fun (rows, _) => rows.usesResult
  let target : Module :=
    { header := ["Generated by Effect4 (Effect v4 profile, dispatch form).", ""] ++
        hostPin.headerLines ++ ["", "Do not edit."]
      imports := .named (["Context", "Effect"] ++ (if result then ["Result"] else [])) "effect" :: atoms
      decls := (if chooses then [decisionsRows.classDecl, decisionsRows.rowsDecl] else []) ++
        (if interrupts then [interruptsRows.classDecl, interruptsRows.rowsDecl] else []) ++
        decls.flatten }
  pure (Render.module style target)

end Effect4.Target.EffectV4
