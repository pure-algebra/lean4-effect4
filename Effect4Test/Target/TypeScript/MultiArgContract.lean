/-
Contract packet: multi-argument operations in flows.

A family operation of `n ≥ 2` parameters is performed with ONE request `Var`
whose value is the right-nested pair `Effects.Trace.ToVal` builds from the
parameter product. Three declarations carry that, and this battery pins the
bytes each of them produces:

* `familyTable` spells the request as the product (`requestSpelling`) and keeps
  the row's parameters, so `OpSpec.arity` is the number of arguments the host
  call takes.
* `Lowering.tupleArgs` (`lowering: rule.perform-tuple`) is the projection: the
  slot destructured at the call -- `b2p0[0]`, `b2p0[1]`, right-nested beyond
  two.
* `Lowering.callOf` uses it, and the block parameter is declared at the tuple
  spelling, so the emitted module declares and calls the method at one arity.

`Rule.performTuple` is the census row. It is appended last in `Rule.all`, so
the three positional pins in the sibling contract batteries are unmoved.

The one thing a flow still cannot do is *build* the tuple, which is why the
graph below takes it from an answer (`E4-FLOW-CE-028`,
`Effect4Test/Counterexamples/Target/JobRequest.lean`).

Doc comments cannot precede `#guard` or `effect_signature`, so the receipts
carry line comments. No definition here traverses a string: a rendered module
reaches `Classical.choice`, so each module is rendered inside the `#guard` that
reads it.
-/

import Effect4.Target.TypeScript.RegionLower
import Effect4.Meta.Derive

namespace Effect4Test.Target.TypeScript.MultiArgContract

open Effects Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open _root_.TypeScript (Expr)

/-! ## 1. The request spelling -/

-- `void`, the parameter's own spelling, then the right-nested product. This is
-- what `Spelling.prod` renders, so the two faces read one slot the same way.
#guard requestSpelling [] = "void"
#guard requestSpelling [("job", "number")] = "number"
#guard requestSpelling [("conn", "JobQueue"), ("job", "number")] =
  "readonly [JobQueue, number]"
#guard requestSpelling [("a", "number"), ("b", "string"), ("c", "boolean")] =
  "readonly [number, readonly [string, boolean]]"

-- The same spelling the profile renders for the same product.
#guard (Spelling.prod (.handle "JobQueue") .nat).render = "readonly [JobQueue, number]"
#guard (Spelling.prod .nat (.prod .string .bool)).render =
  "readonly [number, readonly [string, boolean]]"

-- And the arity the wire reads off it.
#guard (Spelling.prod (.handle "JobQueue") .nat).arity = 2
#guard (Spelling.prod .nat (.prod .string .bool)).arity = 3
#guard (Spelling.except .string .nat).arity = 1

/-! ## 2. The projection

`tupleArgs` is the converse of the nesting `ToVal` builds: argument `i` on the
host is component `i` on the wire, and the last argument is the remaining tail
rather than another `[0]`.
-/

#guard Lowering.tupleArgs (Expr.ident "b2p0") 1 == [Expr.ident "b2p0"]
#guard Lowering.tupleArgs (Expr.ident "b2p0") 2 ==
  [Expr.ident "b2p0[0]", Expr.ident "b2p0[1]"]
#guard Lowering.tupleArgs (Expr.ident "b2p0") 3 ==
  [Expr.ident "b2p0[0]", Expr.ident "b2p0[1][0]", Expr.ident "b2p0[1][1]"]

-- One argument per parameter, whatever the arity.
#guard (Lowering.tupleArgs (Expr.ident "x") 2).length = 2
#guard (Lowering.tupleArgs (Expr.ident "x") 3).length = 3

/-! ## 3. The call and the slot

The packet's `run : Handle × Nat → Nat`, lowered. A doc comment cannot precede
`effect_signature`.
-/

effect_signature Ticketed where
  | take : Handle "JobQueue" × Nat ⟪ "take a ticket", "the connection and the job" ⟫
  | run (conn : Handle "JobQueue") (job : Nat) : Nat
      ⟪ "run a job on its connection", "two parameters, one request slot" ⟫

def ticketTy : String := "readonly [JobQueue, number]"

/-- The family's two rows, then the unit literal the nullary `take` needs for a
request slot of its own type. -/
def table : List OpSpec := familyTable Ticketed.rows ++
  [ { name := "unit", kind := .lit .unit, requestTy := "number", answerTy := "void" } ]

def opTake : OperationId := ⟨0⟩
def opRun : OperationId := ⟨1⟩
def opUnit : OperationId := ⟨2⟩

-- `take` answers exactly what `run` takes, which is what makes the one-slot
-- performance possible at all (`E4-FLOW-CE-028`).
#guard (table.find? (·.name == "take")).map (·.answerTy) = some ticketTy
#guard (table.find? (·.name == "run")).map (·.requestTy) = some ticketTy
#guard (table.find? (·.name == "run")).map OpSpec.arity = some 2
#guard (table.find? (·.name == "take")).map OpSpec.arity = some 1

-- The answer arity travels on the row, because `readonly [JobQueue, number]`
-- does not parse on the host: `JobQueue` is outside the wire grammar on
-- purpose, so the tracer would otherwise read the host array as a list.
#guard (Ticketed.rows.row? "take").map (·.answerArity) = some 2
#guard (Ticketed.rows.row? "run").map (·.answerArity) = some 1

def block (id : Nat) (params : List String) (term : RawTerm) : RawBlock String :=
  { id := ⟨id⟩, params := params, term := term }

/-- Take a ticket, then run it: what the nullary `take` answers is the whole
request of the two-parameter `run`. -/
def raw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ block 0 ["number"] (.perform opUnit ⟨0⟩ ⟨1⟩ [])
      , block 1 ["void"] (.perform opTake ⟨0⟩ ⟨2⟩ [])
      , block 2 [ticketTy] (.perform opRun ⟨0⟩ ⟨3⟩ [])
      , block 3 ["number"] (.ret ⟨0⟩) ] }

/-- The same graph stopping at the ticket: no operation of arity above one. -/
def control : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := ticketTy,
    blocks :=
      [ block 0 ["number"] (.perform opUnit ⟨0⟩ ⟨1⟩ [])
      , block 1 ["void"] (.perform opTake ⟨0⟩ ⟨2⟩ [])
      , block 2 [ticketTy] (.ret ⟨0⟩) ] }

#guard (admit (tableAlphabet ⟨0⟩ table) raw).isOk
#guard (admit (tableAlphabet ⟨0⟩ table) control).isOk

def program? : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow =>
      some { name := "ticketed", param := ("n", "number"), result := "number",
             table := table, flow := flow }
  | .error _ => none

def controlProgram? : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ table) control with
  | .ok flow =>
      some { name := "ticketOnly", param := ("n", "number"), result := ticketTy,
             table := table, flow := flow }
  | .error _ => none

#guard program?.isSome
#guard controlProgram?.isSome

-- The block parameter is bound as a tuple ...
#guard (program?.bind fun program => regionModules? [(Ticketed.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "let b2p0!: readonly [JobQueue, number]").length))
  = some true

-- ... and the call destructures it, at the same arity the service shape
-- declares.
#guard (program?.bind fun program => regionModules? [(Ticketed.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "yield* ticketed.run(b2p0[0], b2p0[1])").length))
  = some true
#guard (program?.bind fun program => regionModules? [(Ticketed.rows, [program], [])]).map
    (fun source => decide (1 <
      (source.splitOn "readonly run: (conn: JobQueue, job: number) => Effect.Effect<number>").length))
  = some true

-- A one-parameter operation is still called on the slot itself, with no
-- projection: the repair is arity-directed, not a blanket rewrite.
#guard (program?.bind fun program => regionModules? [(Ticketed.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "yield* ticketed.take").length)) = some true
#guard (program?.bind fun program => regionModules? [(Ticketed.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "unsupported").length)) = some false

-- The rows the trace harness reads carry the tuple answer's arity, and only
-- when it is above one.
#guard (program?.bind fun program => regionModules? [(Ticketed.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn
      "\"take\": { params: 0, answer: \"readonly [JobQueue, number]\", answerArity: 2 }").length))
  = some true
#guard (program?.bind fun program => regionModules? [(Ticketed.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "\"run\": { params: 2, answer: \"number\" }").length))
  = some true

/-! ## 4. The census

`perform-tuple` is one rule, appended last, and a flow reports it exactly when
it performs an operation of arity above one.
-/

#guard Rule.all.length = 29
-- `perform-tuple` was appended so no positional window moved; Flow v3's two rules
-- were appended after it for the same reason.
#guard (Rule.all.map Rule.id).drop 26 = ["perform-tuple", "perform-catch", "branch-if"]
#guard Rule.ofId? "perform-tuple" = some .performTuple
#guard (Rule.performTuple).id = "perform-tuple"

#guard (program?.map fun program =>
  (Effect4.Target.EffectV4.Flow.ruleSet Ticketed.rows program).contains .performTuple) = some true
#guard (controlProgram?.map fun program =>
  (Effect4.Target.EffectV4.Flow.ruleSet Ticketed.rows program).contains .performTuple) = some false

end Effect4Test.Target.TypeScript.MultiArgContract
