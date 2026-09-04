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

/-- The flow's own dispatch cases, one per declared block. Shared by the
single-root form and the multi-root entry, so "the flow's own cases are
untouched by the entry change" is one definition rather than a comparison
(`skeletonEntry_blockCases` below). -/
def blockCases (table : List OpSpec) (interrupts : Bool) (blocks : List (RawBlock String)) :
    Option (List (Nat × List Skeleton)) :=
  blocks.mapM fun block => do
    let body ← skeletonBlock table interrupts block
    pure (Lowering.blockCase block.id body)

/-- The control skeleton of the dispatch form. Refuses a literal without a
spelling or an operation outside the table (admission already refuses the
latter). -/
def skeletonDispatch (rows : ServiceRow) (program : FlowProgram) : Option (List Skeleton) := do
  let raw := program.flow.erase
  let cases ← blockCases program.table program.interrupts raw.blocks
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

/-! ## The three channels

`declarationLine` at the end of this namespace is what these are for; the
multi-root entry needs them one step earlier, because an exported root alias
writes its own type rather than leaving it to inference. -/

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

/-! ## The multi-root entry

`workshop/Deep/fork-lowering.md` §(b). A fork names a **declared root**
(`RawFlow.roots`), and the host has to be able to start that root with an
argument list; ruling 3 of `docs/research/2026-09-03-deep-plan.md:29-36` says the
lowering emits a *service call* for the fork and never `Effect.fork`, so what the
service needs is a way into this module's own generator at a chosen root.

The change is to make the generator's entry point a parameter instead of a
constant, and to add one synthetic dispatch case per declared root
(`Lowering.entryRootCase`, `lowering: rule.entry-root`). The flow's own block
cases are the same list they always were, and a flow with one declared root does
not take this path at all: `lowerRoots` is `lowerDispatch` there, byte for byte
(`lowerDispatch_single_root_eq`). -/

/-- The binder the entry request arrives in. -/
def entryBinder : String := "entry"

/-- The type of the entry request: which case to enter, and the arguments that
case binds. The argument list is the wire's untyped `Val` list, so a root-entry
case reads it at the parameter's declared type. -/
def entryTy : String := "readonly [number, ReadonlyArray<unknown>]"

/-- The name of the parameterised entry generator. -/
def entryName (name : String) : String := name ++ "__entry"

/-- The name a non-entry declared root is exported under. -/
def rootName (name : String) (root : BlockId) : String :=
  name ++ "__root" ++ toString root.value

/-- The name the entry generator is re-exported under, which is what the host
`Fibers` layer closes over (`workshop/Deep/fork-lowering.md` §(c)). -/
def entryExportName (name : String) : String := name ++ "Entry"

/-- The `Effect` type of the flow: its result, error and requirement channels,
the three `declarationLine` prints. -/
def effectType (rows : ServiceRow) (program : FlowProgram) : String :=
  "Effect.Effect<" ++ program.result ++ ", " ++ errorChannel rows program ++ ", " ++
    requirementChannel rows program ++ ">"

/-- The binders a declared root is entered with: the program's own parameter for
the entry root, and positional `p<i>` binders for every other root, since a
non-entry root's parameters have types and no names. -/
def rootBinders (program : FlowProgram) (block : RawBlock String) : List (String × String) :=
  if block.id = program.flow.erase.entry then [program.param]
  else ((List.range block.params.length).zip block.params).map
    fun (index, ty) => ("p" ++ toString index, ty)

/-- The control skeleton of the multi-root entry: the same acquisitions, the
same declarations and the same block cases as `skeletonDispatch` -- literally
the same `blockCases` call, so the flow's own cases are one definition and not a
copy -- with the entry assignment and the constant block index replaced by the
entry parameter and one synthetic case per declared root. -/
def skeletonEntry (rows : ServiceRow) (program : FlowProgram) : Option (List Skeleton) := do
  let raw := program.flow.erase
  let cases ← blockCases program.table program.interrupts raw.blocks
  let rootBlocks ← raw.roots.mapM (lookupBlock raw)
  -- The synthetic cases live above every block id; a flow that reaches the base
  -- has no multi-root lowering rather than a colliding case.
  guard (raw.blocks.all fun block => block.id.value < Lowering.rootEntryBase)
  pure (acquisitions rows program.table program.interrupts raw ++ declarations raw.blocks ++
    [ Lowering.enterAt "block" entryBinder
    , Lowering.dispatchLoop
        (rootBlocks.map (fun block =>
            Lowering.entryRootCase "block" entryBinder block.id block.params) ++ cases) ])

/-- Lower an admitted graph to the parameterised entry generator. -/
def lowerEntry (rows : ServiceRow) (program : FlowProgram) : Option ProgDecl := do
  let body ← skeletonEntry rows program
  pure { doc := ["Lowered from the flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (dispatch form, multi-root entry)."]
         name := entryName program.name
         paramName := entryBinder
         paramType := entryTy
         stmts := Skeleton.renderList rows body }

/-- `export const prog: (n: T) => Effect.Effect<…> = (n) => prog__entry([1000, [n]])`.

The exported name keeps the signature it had before the flow declared a second
root, so `declarationLine` is still the line the pinned compiler emits for it;
the type is written rather than inferred because that is what makes the emitted
`.d.ts` byte-equal to it (`TypeScript.Expr.lambda` has no per-parameter type, so
the annotation lives on the constant).

Shared by the plain and region dispatch forms: only the name, the doc line, the
binders and the effect type differ. -/
def entryAliasDecl (name entryFn doc : String) (caseIndex : Nat)
    (binders : List (String × String)) (effect : String) : ConstDecl :=
  { doc := [doc]
    name := name
    type := some ("(" ++ String.intercalate ", "
        (binders.map fun (binder, ty) => binder ++ ": " ++ ty) ++ ") => " ++ effect)
    value := .lambda (binders.map (·.1))
      (.call (.ident entryFn)
        [.arr [.int caseIndex, .arr (binders.map fun (binder, _) => .ident binder)]]) }

/-- `export const progEntry = prog__entry`: the name the host layer closes over
(`workshop/Deep/fork-lowering.md` §(c)), stable under any change to the entry
generator's own spelling. -/
def entryExportDecl (name : String) : ConstDecl :=
  { doc := ["The parameterised entry of `" ++ name ++
              "`: a declared root and its arguments."]
    name := entryExportName name
    value := .ident (entryName name) }

/-- The doc line of a root alias: the entry root keeps the program's own name,
so it is entered rather than "a declared root of". -/
def rootAliasDoc (name : String) (isEntry : Bool) (block : BlockId) (form : String) : String :=
  (if isEntry then "Enter the flow `" else "Enter the declared root of `") ++
    name ++ "` at block " ++ toString block.value ++ " (" ++ form ++ ")."

/-- The alias of one declared root of a plain flow. -/
def rootAlias (rows : ServiceRow) (program : FlowProgram) (block : RawBlock String) : ConstDecl :=
  let isEntry := block.id = program.flow.erase.entry
  entryAliasDecl
    (if isEntry then program.name else rootName program.name block.id)
    (entryName program.name)
    (rootAliasDoc program.name isEntry block.id "dispatch form, multi-root")
    (Lowering.rootEntryBase + block.id.value)
    (rootBinders program block)
    (effectType rows program)

/-- The entry re-export of a plain flow. -/
def entryAlias (program : FlowProgram) : ConstDecl := entryExportDecl program.name

/-- The declarations a flow lowers to.

A flow with one declared root is the single exported generator this lowering has
always emitted, byte for byte (`lowerDispatch_single_root_eq`). A flow with two
or more declares the parameterised entry, one exported alias per declared root
-- the entry root keeps the program's own name and signature -- and the entry
re-export: `1 + |roots| + 1` declarations instead of one. -/
def lowerRoots (rows : ServiceRow) (program : FlowProgram) : Option (List Decl) :=
  if (program.flow.erase).roots.length ≤ 1 then
    (lowerDispatch rows program).map fun decl => [Decl.prog decl]
  else do
    let entry ← lowerEntry rows program
    let rootBlocks ← (program.flow.erase).roots.mapM (lookupBlock (program.flow.erase))
    pure (Decl.prog entry ::
      rootBlocks.map (fun block => Decl.const (rootAlias rows program block)) ++
      [Decl.const (entryAlias program)])

/-- **The byte-identity receipt of the entry change.** A flow with exactly one
declared root -- which is every flow this library lowered before the fiber
profile, and every flow in the four lowering batteries -- lowers through the
multi-root emitter to exactly what `lowerDispatch` emits: the same single
`ProgDecl`, hence the same bytes.

Stated the way spike S3's `compileFork_eq_compileRegion`
(`workshop/Deep/ForkFlow.lean:616-666`) is: the new path *is* the old path on
the old inputs, so no existing golden, contract or harness fixture can move. The
four lowering batteries are the corpus that exercises it. -/
theorem lowerDispatch_single_root_eq (rows : ServiceRow) (program : FlowProgram)
    (single : (program.flow.erase).roots.length ≤ 1) :
    lowerRoots rows program = (lowerDispatch rows program).map fun decl => [Decl.prog decl] := by
  simp only [lowerRoots, if_pos single]

/-- The rules a flow exercises, in first-use order. -/
def ruleSet (rows : ServiceRow) (program : FlowProgram) : List Rule :=
  let raw := program.flow.erase
  let step (acc : List Rule) (rule : Rule) : List Rule :=
    if acc.contains rule then acc else acc ++ [rule]
  let move (acc : List Rule) (arity : Nat) : List Rule :=
    if arity = 0 then acc else step acc .paramMove
  let start :=
    (if usesFamily program.table raw then [Rule.serviceAcquire] else []) ++
      [.dispatchLoop, .blockCase] ++ (if program.interrupts then [Rule.interruptPoint] else []) ++
      (if raw.roots.length ≤ 1 then [] else [Rule.entryRoot])
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

/-- The declaration line the pinned compiler must emit for the lowered flow. -/
def declarationLine (rows : ServiceRow) (program : FlowProgram) : String :=
  "export declare const " ++ program.name ++ ": (" ++ program.param.1 ++ ": " ++ program.param.2 ++
    ") => Effect.Effect<" ++ program.result ++ ", " ++ errorChannel rows program ++ ", " ++
    requirementChannel rows program ++ ">;"

end Flow

/-- One module of dispatch-form programs over the declared families, with the
`Decisions` service when any program chooses.

Each program contributes `Flow.lowerRoots`: one declaration for a single-root
flow, byte for byte what `Flow.lowerDispatch` emitted before the entry change
(`Flow.lowerDispatch_single_root_eq`), and `1 + |roots| + 1` for a flow that
declares more than one root. -/
def flowModules? (families : List (ServiceRow × List FlowProgram))
    (atoms : List Import := []) (style : Style := house0) : Option String := do
  let decls ← families.mapM fun (rows, programs) => do
    let lowered ← programs.mapM (Flow.lowerRoots rows)
    pure (rows.classDecl :: rows.rowsDecl :: lowered.flatten)
  let chooses := families.any fun (_, programs) =>
    programs.any fun program => Flow.usesDecisions program.flow.erase
  let interrupts := families.any fun (_, programs) => programs.any (·.interrupts)
  -- The `effect` namespaces are read off the rows the module declares, so the
  -- import line names exactly what the module's own text spells.
  let declared := (if chooses then [decisionsRows] else []) ++
    (if interrupts then [interruptsRows] else []) ++ families.map (·.1)
  let target : Module :=
    { header := ["Generated by Effect4 (Effect v4 profile, dispatch form).", ""] ++
        hostPin.headerLines ++ ["", "Do not edit."]
      imports := .named (["Context", "Effect"] ++ moduleNamespaces declared atoms) "effect" :: atoms
      decls := (if chooses then [decisionsRows.classDecl, decisionsRows.rowsDecl] else []) ++
        (if interrupts then [interruptsRows.classDecl, interruptsRows.rowsDecl] else []) ++
        decls.flatten }
  pure (Render.module style target)

end Effect4.Target.EffectV4
