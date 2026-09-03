import Effect4.Target.TypeScript.Lower
import Effect4.Target.TypeScript.ScriptFlow
import Effect4.Semantics.Runs
import Effect4.Flow.Region
import Effect4.Flow.Interrupt
import TypeScript.Structure

/-!
# Target.TypeScript.Skeleton

Owner: the control skeleton the three lowerings share (plan packet D3 of
`docs/research/2026-09-03-reification-plan.md`, specified in
`docs/research/2026-09-03-algebra-denotation.md` §3).

Before this module the dispatch form (`FlowLower.lean`), the structured form
(`StructuredLower.lean`) and the region form (`RegionLower.lean`) each emitted
`TypeScript.Stmt` directly, so "the two forms denote the same thing" had no
Lean subject: `Stmt` is syntax with no evaluator in either repository and the
only available comparison was the host.

`Skeleton` is that subject. It is the abstract control syntax the three
lowerings already shared, made first-order:

* a dispatch loop switching on a block index, labelled blocks, labelled
  `while (true)` loops, and `break`/`continue` to a label;
* assignment of a parameter variable, and the sequentialising temporaries a
  self-edge needs;
* a family, atom or literal `perform` binding an answer, a decision binding its
  branch, and an interrupt point binding nothing (packet M2);
* `return`; and
* the three region forms — enter-scoped, acquire, leave — as the region
  lowering emits them.

Two consumers sit on it and nothing else does.

* `render : ServiceRow → Skeleton → List Stmt` (§4) is a printer. It spells;
  it inspects no value and takes no decision, so no claim about the generated
  program's meaning passes through it. Its faithfulness to Effect v4 generator
  semantics stays a host receipt, permanently (`docs/TRACE-DAG.md` `targets`).
* `Skeleton.exec` and `Skeleton.denote` (§6, §7) evaluate a skeleton into
  `Program (Skel.FullSig a)` over the same signature sum
  `Effect4/Semantics/Denotation.lean` (packet D1) is being written against.
  Those names are declared locally in `namespace Skel`, each marked
  `to be unified with Denotation.lean`, so the two branches merge cleanly.

Every tagged lowering rule of the three flow forms is now a shape of this IR
(§3) rather than a shape of `Stmt`; `docs/LOWERING-COVERAGE.md` scans the whole
`Effect4/Target/TypeScript` directory, so the census is unchanged in both
directions. The refactor's acceptance test is byte identity:
`harness/trace/flow-fixture.ts` and `harness/trace/structured-fixture.ts` are
regenerated and compared with `cmp`, and the three lowering contracts keep
passing.

`TypeScript.Structure.emitWith` (lean4-typescript v0.4.1) fixes its `Shapes` at
`Stmt`. The emitter in §5 is that algorithm with the statement type as a
parameter, over the *same* graph analysis (`Structure.reducible`,
`Structure.idom`, `Structure.children`, `Structure.isMerge`,
`Structure.isLoopHeader`, `Structure.isBackEdge`, `Structure.dominates` and the
two label spellings), and `Structure.emitNode_eq` below pins the agreement at
`Stmt` as a theorem rather than leaving it to the fixture bytes. Upstreaming
the type parameter is the one lean4-typescript edit the plan schedules; this
module does not edit the pinned package.
-/

open TypeScript

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow
open Effects.Trace (Val)

/-! ## 1. Slots

Every value the lowerings move lives in a variable whose name is a function of
first-order flow data. A `Slot` is that name before it is spelled. -/

/-- A variable of a lowered program. -/
inductive Slot where
  /-- `b<block>p<index>`: parameter `index` of `block`. -/
  | param (block : BlockId) (index : Nat)
  /-- `m<index>`: the temporary a self-edge reads a source into. -/
  | temp (index : Nat)
  /-- `a<block>`: the answer a `perform` of `block` binds. -/
  | answer (block : BlockId)
  /-- `c<block>`: the branch a `choose` of `block` binds. -/
  | decision (block : BlockId)
  /-- `r<region>`: the value a nested region generator returns. -/
  | region (region : RegionId)
  /-- The program's own parameter binder. -/
  | input (binder : String)
deriving DecidableEq, Repr

namespace Slot

/-- The target spelling of a slot. -/
def name : Slot → String
  | .param block index => "b" ++ toString block.value ++ "p" ++ toString index
  | .temp index => "m" ++ toString index
  | .answer block => "a" ++ toString block.value
  | .decision block => "c" ++ toString block.value
  | .region id => "r" ++ toString id.value
  | .input binder => binder

/-- The slot as a target expression. -/
def expr (slot : Slot) : Expr := .ident slot.name

end Slot

/-! ## 2. The skeleton -/

/-- The control skeleton of a lowered flow: the abstract syntax the dispatch,
structured and region forms share. Nothing here is TypeScript; §4 spells it
and §6 evaluates it. -/
inductive Skeleton where
  /-- Bind a service receiver once at the top of the generator. -/
  | acquireService (rows : ServiceRow)
  /-- Declare a definitely-assigned parameter variable of a target type. -/
  | declare (slot : Slot) (type : String)
  /-- `target = source`. -/
  | assign (target source : Slot)
  /-- `let m<index> = source`: the read half of a parallel move. -/
  | letTemp (index : Nat) (source : Slot)
  /-- `let <var> = <block>`: introduce a dispatch index. -/
  | letBlockIndex (var : String) (target : BlockId)
  /-- `<var> = <block>; continue`: transfer inside the loop that owns `var`. -/
  | gotoBlock (var : String) (target : BlockId)
  /-- The body of `block` begins here. A marker: it spells nothing, and it is
  what makes the two compilations comparable — both enter the same blocks in
  the same order, however their control is arranged. -/
  | enterBlock (block : BlockId)
  /-- `while (true) { switch (<var>) { case n: … } }`. -/
  | dispatchLoop (var : String) (cases : List (Nat × List Skeleton))
  /-- `<label>: while (true) { body }`. -/
  | loop (label : String) (body : List Skeleton)
  /-- `<label>: { body }`. -/
  | labelled (label : String) (body : List Skeleton)
  /-- `break <label>`. -/
  | breakTo (label : String)
  /-- `continue <label>`. -/
  | continueTo (label : String)
  /-- A family operation: `const a<b> = yield* cell.get`. -/
  | perform (answer : Slot) (operation : OperationId) (spec : OpSpec) (request : Slot)
  /-- A pure atom: `let a<b> = succ(x)`. -/
  | atom (answer : Slot) (operation : OperationId) (spec : OpSpec) (request : Slot)
  /-- A literal: `let a<b> = 3`. The request is not spelled — the constant is
  the whole spelling — but the operation still consumes it. -/
  | literal (answer : Slot) (operation : OperationId) (request : Slot) (value : Val)
  /-- A decision: bind the branch from the `Decisions` service, then split. -/
  | decide (answer : Slot) (site : DecisionId) (onTrue onFalse : List Skeleton)
  /-- An interruptible point: ask the `Interrupts` service whether the
  interrupt is delivered here. The site is an interrupt site
  (`Effect4.Flow.Point.site`), disjoint from every `choose` site. -/
  | interruptPoint (site : DecisionId)
  /-- `return value`. -/
  | ret (value : Slot)
  /-- Open a region: report it, run `body` as a nested generator in its own
  scope, and bind the value it returns to `r<region>`. -/
  | enterScoped (region : RegionId) (body : List Skeleton)
  /-- Acquire a resource inside a region, registering its release. -/
  | acquire (answer : Slot) (region : RegionId) (operation : OperationId) (spec : OpSpec)
      (request : Slot) (release : OpSpec)
  /-- The nested region generator returns. -/
  | leave (value : Slot)

/-! ## 3. The lowering rules, as skeleton shapes

Every rule of the three flow forms is one tagged definition here. They moved
from `FlowLower.lean`, `RegionLower.lean` and `StructuredLower.lean` and
changed carrier — from `Stmt` to `Skeleton` — and nothing else; `render` is
the single consumer of all of them. -/

namespace Lowering

/-- Every admitted graph lowers to one dispatch loop over the block index
held in `blockVar`. lowering: rule.dispatch-loop -/
def dispatchLoopOn (blockVar : String) (cases : List (Nat × List Skeleton)) : Skeleton :=
  .dispatchLoop blockVar cases

/-- The top-level dispatch loop, over `block`. -/
def dispatchLoop (cases : List (Nat × List Skeleton)) : Skeleton :=
  dispatchLoopOn "block" cases

/-- One block is one `case` whose body ends in `continue` or `return`.
lowering: rule.block-case -/
def blockCase (block : BlockId) (body : List Skeleton) : Nat × List Skeleton :=
  (block.value, body)

/-- Transfer to `target` in the loop that owns `blockVar`. This is part of
`block-case`; it carries no rule of its own. -/
def gotoIn (blockVar : String) (target : BlockId) : List Skeleton :=
  [.gotoBlock blockVar target]

/-- Transfer to `target` in the top-level dispatch loop. -/
def goto (target : BlockId) : List Skeleton := gotoIn "block" target

/-- Pass the argument list to the target's parameters. On a self-edge every
source is read into a temporary before any parameter is assigned, so a swap
is a swap. lowering: rule.param-move -/
def paramMove (source target : BlockId) (values : List Slot) : List Skeleton :=
  let indexed := (List.range values.length).zip values
  if source = target then
    (indexed.map fun (index, value) => Skeleton.letTemp index value) ++
      (indexed.map fun (index, _) => Skeleton.assign (.param target index) (.temp index))
  else
    indexed.map fun (index, value) => Skeleton.assign (.param target index) value

/-- A family operation of a block answers into `a<block>`: `const a1 = yield*
cell.get` or `const a1 = yield* cell.put(b1p2)`. lowering: rule.flow-perform -/
def flowPerform (answer : Slot) (operation : OperationId) (spec : OpSpec) (request : Slot) :
    Skeleton :=
  .perform answer operation spec request

/-- A pure atom of a block is a plain call: `let a1 = succ(b1p0)`.
lowering: rule.flow-atom -/
def flowAtom (answer : Slot) (operation : OperationId) (spec : OpSpec) (request : Slot) :
    Skeleton :=
  .atom answer operation spec request

/-- A literal operation of a block is its constant: `let a1 = 5`.
lowering: rule.flow-literal -/
def flowLiteral (answer : Slot) (operation : OperationId) (request : Slot) (value : Val) :
    Skeleton :=
  .literal answer operation request value

/-- A `choose` asks the `Decisions` service for its site and branches:
`const c0 = yield* decisions.choose(7); if (c0) { ... } else { ... }`.
lowering: rule.choose-if -/
def chooseIf (answer : Slot) (site : DecisionId) (left right : List Skeleton) : List Skeleton :=
  [.decide answer site left right]

/-- An interruptible point of a run asks the `Interrupts` service whether the
interrupt is delivered here: `yield* interrupts.point(1000001)`. The service
answers by interrupting the fiber at that point and returning nothing
otherwise, so the point is a `void` operation and binds no slot. Emitted only
by a flow that declares interrupt points, so a flow without them lowers to the
bytes it lowered to before. lowering: rule.interrupt-point -/
def interruptPoint (site : DecisionId) : Skeleton :=
  .interruptPoint site

/-- A `ret` returns the named parameter: `return b5p3`. lowering: rule.flow-ret -/
def flowRet (value : Slot) : Skeleton :=
  .ret value

/-- Open a region: report it, then run its blocks as a nested generator in its
own scope whose exit `Effect.onExit` reports as `leave`; the value it returns
becomes the parameter of the region's `continue_` block.
lowering: rule.region-enter -/
def regionEnter (region : RegionId) (body : List Skeleton) : List Skeleton :=
  [.enterScoped region body]

/-- Acquire inside a region: `Effect.acquireRelease` registers the release in
the enclosing scope; the release reports `finalizer` with the closing exit
before running its own operation. lowering: rule.region-acquire -/
def regionAcquire (answer : Slot) (region : RegionId) (operation : OperationId) (spec : OpSpec)
    (request : Slot) (release : OpSpec) : Skeleton :=
  .acquire answer region operation spec request release

/-- Leave a region: the nested generator returns the value.
lowering: rule.region-leave -/
def regionLeave (value : Slot) : Skeleton :=
  .leave value

/-- A loop header is a labelled `while (true)`. lowering: rule.structured-loop -/
def structuredLoop (label : String) (body : List Skeleton) : Skeleton :=
  .loop label body

/-- A merge node is a labelled block wrapping everything emitted before it.
lowering: rule.structured-merge -/
def structuredMerge (label : String) (body : List Skeleton) : Skeleton :=
  .labelled label body

/-- A backward transfer to a loop header. lowering: rule.structured-continue -/
def structuredContinue (label : String) : Skeleton :=
  .continueTo label

/-- A forward transfer to a merge node or loop header. lowering: rule.structured-break -/
def structuredBreak (label : String) : Skeleton :=
  .breakTo label

/-- The call of a family operation on a request expression: an Effect value
when the operation is nullary, a method call otherwise. -/
def callOf (rows : ServiceRow) (spec : OpSpec) (request : Expr) : Expr :=
  if spec.requestTy == "void" then nullaryValue rows.receiver spec.name
  else performCall rows.receiver spec.name [request]

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

/-- The variable holding parameter `index` of `block`. -/
def paramVar (block : BlockId) (index : Nat) : String :=
  (Slot.param block index).name

/-- The row of the operation `id` in a table, if any. -/
def spec? (table : List OpSpec) (id : OperationId) : Option OpSpec :=
  table[id.value]?

end Flow

/-! ## 4. The printer -/

namespace Skeleton

mutual

/-- Spell one skeleton node. -/
def render (rows : ServiceRow) : Skeleton → List Stmt
  | .acquireService row => [Lowering.serviceAcquire row]
  | .declare slot type => [.letDefinite slot.name type]
  | .assign target source => [.assign target.name source.expr]
  | .letTemp index source => [.letInit (Slot.temp index).name source.expr]
  | .letBlockIndex var target => [.letInit var (.int target.value)]
  | .gotoBlock var target => [.assign var (.int target.value), .continueTo none]
  | .enterBlock _ => []
  | .dispatchLoop var cases =>
      [.whileTrue none [.switch (.ident var) (renderCases rows cases)]]
  | .loop label body => [.whileTrue (some label) (renderList rows body)]
  | .labelled label body => [.labelled label (renderList rows body)]
  | .breakTo label => [.breakTo (some label)]
  | .continueTo label => [.continueTo (some label)]
  | .perform answer _ spec request =>
      [.constYield answer.name (Lowering.callOf rows spec request.expr)]
  | .atom answer _ spec request =>
      [.letInit answer.name (.call (.ident spec.name) [request.expr])]
  | .literal answer _ _ value =>
      match Flow.literal? value with
      | some spelling => [.letInit answer.name spelling]
      | none => []
  | .decide answer site onTrue onFalse =>
      [ .constYield answer.name (.call (.ident "decisions.choose") [.int site.value])
      , .ifElse answer.expr (renderList rows onTrue) (renderList rows onFalse) ]
  | .interruptPoint site =>
      [.yieldDiscard (.call (.ident "interrupts.point") [.int site.value])]
  | .ret value => [.ret value.expr]
  | .enterScoped region body =>
      [ .yieldDiscard (.call (.ident "regions.enter") [.int region.value])
      , .scopedGen (Slot.region region).name (renderList rows body)
          (.lambda ["exit"]
            (.call (.ident "regions.leave") [.int region.value, .ident "exit"])) ]
  | .acquire answer region _ spec request release =>
      [ .constYield answer.name (.call (.ident "Effect.acquireRelease")
          [ Lowering.callOf rows spec request.expr
          , .lambda ["a", "exit"]
              (.method (.call (.ident "regions.finalizer") [.int region.value, .ident "exit"])
                "pipe"
                [.call (.ident "Effect.andThen") [Lowering.callOf rows release (.ident "a")]]) ]) ]
  | .leave value => [.ret value.expr]
  termination_by structural node => node

/-- Spell a statement list. -/
def renderList (rows : ServiceRow) : List Skeleton → List Stmt
  | [] => []
  | node :: rest => render rows node ++ renderList rows rest
  termination_by structural nodes => nodes

/-- Spell the cases of a dispatch switch. -/
def renderCases (rows : ServiceRow) : List (Nat × List Skeleton) → List (Nat × List Stmt)
  | [] => []
  | (index, body) :: rest => (index, renderList rows body) :: renderCases rows rest
  termination_by structural cases => cases

end

end Skeleton

/-! ## 5. Structuring at an arbitrary statement type

`TypeScript.Structure.emitWith` fixes its shapes at `Stmt`. The three
definitions below are that algorithm with the statement type as a parameter,
over the same graph analysis; `emitNode_eq` and `emitWith_eq` pin the
agreement at `Stmt`, so replacing the call in `StructuredLower.lean` by the
`Skeleton` instance changes the carrier and nothing else. -/

namespace Structuring

open TypeScript.Structure

/-- The four structured shapes at an arbitrary statement type: a loop, a merge
block, and the two transfers. -/
structure Shapes (α : Type) where
  loop : String → List α → α
  merge : String → List α → α
  continueTo : String → α
  breakTo : String → α

/-- The `Stmt` instance of `Shapes`, as `TypeScript.Structure` spells it. -/
def Shapes.ofStmt (shapes : TypeScript.Structure.Shapes) : Shapes Stmt :=
  { loop := shapes.loop, merge := shapes.merge,
    continueTo := shapes.continueTo, breakTo := shapes.breakTo }

/-- Emit one node and its dominator subtree, as `Structure.emitNode` does. -/
def emitNode {α : Type} (g : Graph) (shapes : Shapes α)
    (body : Nat → (Nat → Option (List α)) → Option (List α)) :
    Nat → Nat → Option (List α)
  | 0, _ => none
  | fuel + 1, current => do
    let transfer (target : Nat) : Option (List α) :=
      if isBackEdge g current target && isLoopHeader g target && dominates g target current then
        some [shapes.continueTo (loopLabel target)]
      else if isMerge g target || isLoopHeader g target then
        some [shapes.breakTo (blockLabel target)]
      else if idom g target == some current then
        emitNode g shapes body fuel target
      else none
    let own ← body current transfer
    let merges := (children g current).filter fun c => isMerge g c || isLoopHeader g c
    merges.foldlM (init := own) fun acc m => do
      let inner ← emitNode g shapes body fuel m
      let placed := if isLoopHeader g m then [shapes.loop (loopLabel m) inner] else inner
      pure ([shapes.merge (blockLabel m) acc] ++ placed)

/-- Emit a reducible graph from its entry, as `Structure.emitWith` does. -/
def emitWith {α : Type} (g : Graph) (shapes : Shapes α)
    (body : Nat → (Nat → Option (List α)) → Option (List α)) : Option (List α) := do
  guard (reducible g)
  let inner ← emitNode g shapes body (g.size + 1) g.entry
  pure (if isLoopHeader g g.entry then [shapes.loop (loopLabel g.entry) inner] else inner)

/-- At `Stmt` this is the pinned package's emitter, node for node. -/
theorem emitNode_eq (g : Graph) (shapes : TypeScript.Structure.Shapes)
    (body : Nat → (Nat → Option (List Stmt)) → Option (List Stmt)) :
    ∀ (fuel current : Nat),
      emitNode g (Shapes.ofStmt shapes) body fuel current =
        TypeScript.Structure.emitNode g shapes body fuel current := by
  intro fuel
  induction fuel with
  | zero => intro current; rfl
  | succ fuel ih =>
      intro current
      unfold emitNode TypeScript.Structure.emitNode
      simp only [ih]
      simp only [Shapes.ofStmt]

/-- At `Stmt` this is the pinned package's `emitWith`. -/
theorem emitWith_eq (g : Graph) (shapes : TypeScript.Structure.Shapes)
    (body : Nat → (Nat → Option (List Stmt)) → Option (List Stmt)) :
    emitWith g (Shapes.ofStmt shapes) body = TypeScript.Structure.emitWith g shapes body := by
  simp only [emitWith, TypeScript.Structure.emitWith, emitNode_eq]
  rfl

end Structuring

end Effect4.Target.EffectV4
