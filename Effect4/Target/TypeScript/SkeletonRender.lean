import Effect4.Target.TypeScript.Skeleton

/-!
# Target.TypeScript.SkeletonRender

Owner: the printer that spells a `Skeleton` as `TypeScript.Stmt`, and the two
call builders it needs.

This module exists so that the `String` boundary is a file boundary rather
than a list of names. Lean's standard character folds carry `Classical.choice`
through the proof backing UTF-8 decoding, so anything that traverses a Lean
`String` inherits it; `Effect4/Target/TypeScript/Skeleton.lean` used to hold
both the `String`-free IR and this renderer, and the claim that its laws were
stated over the IR was a convention a comment asserted (survey findings H28 and
L2). Split, the claim is structural: every declaration in `Skeleton.lean` --
including `Structuring.emitNode_eq` and `Structuring.emitWith_eq`, the bridge
saying Effect4's emitter is the pinned package's emitter node for node -- sits
at the `propext`/`Quot.sound` ceiling, and the crossings all live here.

`render` spells; it inspects no value and takes no decision, so no claim about
the generated program's meaning passes through it. Its faithfulness to Effect
v4 generator semantics stays a host receipt, permanently
(`docs/TRACE-DAG.md` `targets`). The label-scoping laws that transport a
skeleton property through it (`Effect4/Target/TypeScript/StructureLaws.lean`'s
`render_wellScoped` and its two siblings) name the printer in their statements
and are admitted by exact declaration in `Effect4Test/Audit/AxiomGate.lean`;
the skeleton-level law they transport is not.
-/

open TypeScript

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow
open Effects.Trace (Val)

/-! ## 1. The call builders -/

namespace Lowering

/-- The arguments of a call whose request slot holds a parameter tuple: the
slot destructured at the call, `jobs.run(b4p0[0], b4p0[1])`. The flow alphabet
has no pair constructor -- `plan` hands a service exactly one `Val` -- so an
operation of two or more parameters is performed with one request slot holding
the right-nested product, and the call takes it apart again. The projections
are right-nested (`x[0]`, `x[1][0]`, …, the last component the remaining tail),
the converse of the nesting `Effects.Trace.ToVal` builds from the parameter
product, so the argument at position `i` on the host is the component at
position `i` on the wire.

The argument is the request slot's *spelling*, not an expression: projecting
`[0]` off an arbitrary expression is not a thing this fragment can build, and
the version that took an `Expr` answered a single-element list for anything
that was not a bare identifier -- a two-parameter operation called with one
argument, which is exactly `E4-TARGET-CE-022`'s defect. Taking the path makes
that shape unrepresentable (`E4-TARGET-CE-026`, survey finding H15).
lowering: rule.perform-tuple -/
def tupleArgs (request : String) : Nat → List Expr
  | 0 => []
  | 1 => [.ident request]
  | n + 1 => .ident (request ++ "[0]") :: tupleArgs (request ++ "[1]") n

/-- The call of a family operation on a request slot: an Effect value when the
operation is nullary, a method call on the slot otherwise, and a method call on
the destructured slot when the operation takes two or more parameters. The
request is a `Slot` rather than an `Expr` so that every request has a spelling
`tupleArgs` can project (`E4-TARGET-CE-026`). -/
def callOf (rows : ServiceRow) (spec : OpSpec) (request : Slot) : Expr :=
  if spec.requestTy == "void" then nullaryValue rows.receiver spec.name
  else if spec.arity == 1 then performCall rows.receiver spec.name [request.expr]
  else performCall rows.receiver spec.name (tupleArgs request.path spec.arity)

end Lowering

/-! ## 2. The printer -/

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
      [.constYield answer.name (Lowering.callOf rows spec request)]
  | .atom answer _ spec request =>
      [.letInit answer.name (.call (.ident spec.name) [request.expr])]
  | .literal answer _ _ value =>
      match Flow.literal? value with
      | some spelling => [.letInit answer.name spelling]
      | none => []
  | .decide answer site onTrue onFalse =>
      [ .constYield answer.name (.call (.ident "decisions.choose") [.int site.value])
      , .ifElse answer.expr (renderList rows onTrue) (renderList rows onFalse) ]
  | .performCatch answer _ _ _ spec request onOk onError =>
      [ .constYield answer.name
          (.call (.ident "Effect.result") [Lowering.callOf rows spec request])
      , .ifElse (.call (.ident "Result.isSuccess") [answer.expr])
          (renderList rows onOk) (renderList rows onError) ]
  | .branchIf test site onTrue onFalse =>
      [ .yieldDiscard (.call (.ident "decisions.report") [.int site.value, test.expr])
      , .ifElse test.expr (renderList rows onTrue) (renderList rows onFalse) ]
  | .interruptPoint site =>
      [.yieldDiscard (.call (.ident "interrupts.point") [.int site.value])]
  | .ret value => [.ret value.expr]
  | .enterScoped region body =>
      [ .yieldDiscard (.call (.ident "regions.enter") [.int region.value])
      , .scopedGen (Slot.region region).name (renderList rows body)
          (.lambda ["exit"]
            (.call (.ident "regions.leave") [.int region.value, .ident "exit"])) ]
  | .enterScopedMasked region body =>
      [ .yieldDiscard (.call (.ident "regions.enter") [.int region.value])
      , .scopedGenMasked (Slot.region region).name (renderList rows body)
          (.lambda ["exit"]
            (.call (.ident "regions.leave") [.int region.value, .ident "exit"])) ]
  | .acquire answer region _ spec request release =>
      [ .constYield answer.name (.call (.ident "Effect.acquireRelease")
          [ Lowering.callOf rows spec request
          , .lambda ["a", "exit"]
              (.method (.call (.ident "regions.finalizer") [.int region.value, .ident "exit"])
                "pipe"
                [.call (.ident "Effect.andThen") [Lowering.callOf rows release (.input "a")]]) ]) ]
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

end Effect4.Target.EffectV4
