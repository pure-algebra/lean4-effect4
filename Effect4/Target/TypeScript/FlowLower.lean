import Effect4.Target.TypeScript.Lower
import Effect4.Target.TypeScript.ScriptFlow

/-!
# Target.TypeScript.FlowLower

Owner: dispatch-form lowering of an admitted Flow v2 graph into an Effect v4
generator (plan packet P-T9a, ruling R7). Every admitted graph lowers to

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

/-- The `Decisions` service every `choose` asks. -/
def decisionsRows : ServiceRow :=
  { name := "Decisions"
    ops := [{ name := "choose", index := 0, params := [("site", "Nat")],
              tsParams := [("site", "number")], answer := "Bool", tsAnswer := "boolean",
              cues := ["decide a choice site from the tape"] }] }

namespace Flow

/-- The variable holding parameter `index` of `block`. -/
def paramVar (block : BlockId) (index : Nat) : String :=
  "b" ++ toString block.value ++ "p" ++ toString index

/-- The row of the operation `id` in a table, if any. -/
def spec? (table : List OpSpec) (id : OperationId) : Option OpSpec :=
  table[id.value]?

end Flow

namespace Lowering

/-- Every admitted graph lowers to one dispatch loop over the block index.
lowering: rule.dispatch-loop -/
def dispatchLoop (cases : List (Nat × List Stmt)) : Stmt :=
  .whileTrue none [.switch (.ident "block") cases]

/-- One block is one `case` whose body ends in `continue` or `return`.
lowering: rule.block-case -/
def blockCase (block : BlockId) (body : List Stmt) : Nat × List Stmt :=
  (block.value, body)

/-- Pass the argument list to the target's parameters. On a self-edge every
source is read into a temporary before any parameter is assigned, so a swap
is a swap. lowering: rule.param-move -/
def paramMove (source target : BlockId) (values : List Expr) : List Stmt :=
  let indexed := (List.range values.length).zip values
  if source = target then
    (indexed.map fun (index, value) => Stmt.letInit ("m" ++ toString index) value) ++
      (indexed.map fun (index, _) =>
        Stmt.assign (Flow.paramVar target index) (.ident ("m" ++ toString index)))
  else
    indexed.map fun (index, value) => Stmt.assign (Flow.paramVar target index) value

/-- Transfer to `target`: set the block index and re-enter the loop. This is
part of `block-case`; it carries no rule of its own. -/
def goto (target : BlockId) : List Stmt :=
  [.assign "block" (.int target.value), .continueTo none]

/-- A family operation of a block answers into `a<block>`: `const a1 = yield*
cell.get` or `const a1 = yield* cell.put(b1p2)`. lowering: rule.flow-perform -/
def flowPerform (answer : String) (call : Expr) : Stmt :=
  .constYield answer call

/-- A pure atom of a block is a plain call: `let a1 = succ(b1p0)`.
lowering: rule.flow-atom -/
def flowAtom (answer atom : String) (request : Expr) : Stmt :=
  .letInit answer (.call (.ident atom) [request])

/-- A literal operation of a block is its constant: `let a1 = 5`.
lowering: rule.flow-literal -/
def flowLiteral (answer : String) (value : Expr) : Stmt :=
  .letInit answer value

/-- A `choose` asks the `Decisions` service for its site and branches:
`const c0 = yield* decisions.choose(7); if (c0) { ... } else { ... }`.
lowering: rule.choose-if -/
def chooseIf (decision : String) (site : DecisionId) (left right : List Stmt) : List Stmt :=
  [ .constYield decision (.call (.ident "decisions.choose") [.int site.value])
  , .ifElse (.ident decision) left right ]

/-- A `ret` returns the named parameter: `return b5p3`. lowering: rule.flow-ret -/
def flowRet (value : Expr) : Stmt :=
  .ret value

end Lowering

namespace Flow

/-- The constant a literal lowers to; structured values have no spelling here. -/
def literal? : Val → Option Expr
  | .nat n => some (.int n)
  | .int i => some (.int i)
  | .str s => some (.str s)
  | .bool b => some (.bool b)
  | .unit => some (.ident "undefined")
  | _ => none

/-- The body of one block: its answer or decision, then the move and transfer. -/
def lowerBlock (rows : ServiceRow) (table : List OpSpec) (block : RawBlock String) :
    Option (List Stmt) :=
  let var (v : Var) : Expr := .ident (paramVar block.id v.index)
  let transfer (target : BlockId) (values : List Expr) : List Stmt :=
    Lowering.paramMove block.id target values ++ Lowering.goto target
  match block.term with
  | .ret value => some [Lowering.flowRet (var value)]
  | .jump target args => some (transfer target (args.map var))
  | .perform operation request target args => do
      let spec ← spec? table operation
      let answer := "a" ++ toString block.id.value
      let head ← match spec.kind with
        | .family =>
            some (Lowering.flowPerform answer
              (if spec.requestTy == "void" then Lowering.nullaryValue rows.receiver spec.name
               else Lowering.performCall rows.receiver spec.name [var request]))
        | .atom => some (Lowering.flowAtom answer spec.name (var request))
        | .lit value => (literal? value).map (Lowering.flowLiteral answer)
      some (head :: transfer target (args.map var ++ [.ident answer]))
  | .choose decision left right args =>
      let name := "c" ++ toString block.id.value
      some (Lowering.chooseIf name decision
        (transfer left (args.map var)) (transfer right (args.map var)))

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

/-- Lower an admitted graph to the dispatch form. Refuses a literal without a
spelling or an operation outside the table (admission already refuses the
latter). -/
def lowerDispatch (rows : ServiceRow) (program : FlowProgram) : Option ProgDecl := do
  let raw := program.flow.erase
  let cases ← raw.blocks.mapM fun block => do
    let body ← lowerBlock rows program.table block
    pure (Lowering.blockCase block.id body)
  let declarations := raw.blocks.flatMap fun block =>
    ((List.range block.params.length).zip block.params).map fun (index, ty) =>
      Stmt.letDefinite (paramVar block.id index) ty
  let acquire :=
    (if usesFamily program.table raw then [Lowering.serviceAcquire rows] else []) ++
    (if usesDecisions raw then [Lowering.serviceAcquire decisionsRows] else [])
  pure { doc := ["Lowered from the flow `" ++ program.name ++ "` over `" ++ rows.name ++
                 "` (dispatch form)."]
         name := program.name
         paramName := program.param.1
         paramType := program.param.2
         stmts := acquire ++ declarations ++
           [ Stmt.assign (paramVar raw.entry 0) (.ident program.param.1)
           , Stmt.letInit "block" (.int raw.entry.value)
           , Lowering.dispatchLoop cases ] }

/-- The rules a flow exercises, in first-use order. -/
def ruleSet (rows : ServiceRow) (program : FlowProgram) : List Rule :=
  let raw := program.flow.erase
  let step (acc : List Rule) (rule : Rule) : List Rule :=
    if acc.contains rule then acc else acc ++ [rule]
  let move (acc : List Rule) (arity : Nat) : List Rule :=
    if arity = 0 then acc else step acc .paramMove
  let start :=
    (if usesFamily program.table raw then [Rule.serviceAcquire] else []) ++
      [.dispatchLoop, .blockCase]
  raw.blocks.foldl (init := start) fun acc block =>
    match block.term with
    | .ret _ => step acc .flowRet
    | .jump _ args => move acc args.length
    | .perform operation _ _ args =>
        let acc := match spec? program.table operation with
          | some spec => match spec.kind with
            | .family =>
                step (step acc .flowPerform)
                  (if spec.requestTy == "void" then .nullaryValue else .performCall)
            | .atom => step acc .flowAtom
            | .lit _ => step acc .flowLiteral
          | none => acc
        move acc (args.length + 1)
    | .choose _ _ _ args => move (step acc .chooseIf) args.length
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
    (if usesDecisions raw then ["Decisions"] else [])
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
  let result := families.any fun (rows, _) => rows.usesResult
  let target : Module :=
    { header := ["Generated by Effect4 (Effect v4 profile, dispatch form).", ""] ++
        hostPin.headerLines ++ ["", "Do not edit."]
      imports := .named (["Context", "Effect"] ++ (if result then ["Result"] else [])) "effect" :: atoms
      decls := (if chooses then [decisionsRows.classDecl, decisionsRows.rowsDecl] else []) ++
        decls.flatten }
  pure (Render.module style target)

end Effect4.Target.EffectV4
