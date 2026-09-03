/-
Contract packet: `test/contracts/flow-structured-lowering.contract.md` (P-T9b).

The label-scoping law of the structured form (`Effect4/Target/TypeScript/
StructureLaws.lean`) and its executable receipts. The theorem covers the
`continue` half outright; the `break` half is covered here on the packet's own
flows by `wellScopedList [] []`, the strict predicate, which demands an
enclosing `label` for every `break`. Doc comments cannot precede `#guard`.
-/

import Effect4.Target.TypeScript.StructureLaws

open TypeScript

namespace Effect4Test.Target.TypeScript.StructureLawsContract

open Effects Effect4.Flow Effect4.Target.EffectV4 Effect4.Target.Structured

/-! ## The frozen surface -/

#check @Effect4.Target.Structured.wellScoped
#check @Effect4.Target.Structured.wellScopedList
#check @Effect4.Target.Structured.wellScopedCases
#check @Effect4.Target.Structured.GraphClosed
#check @Effect4.Target.Structured.BodyScoped
#check @Effect4.Target.Structured.blockLabels
#check @Effect4.Target.Structured.dominates_step
#check @Effect4.Target.Structured.dominates_entry
#check @Effect4.Target.Structured.emitNode_wellScoped
#check @Effect4.Target.Structured.emitWith_wellScoped
#check @Effect4.Target.Structured.lowerBlockWith_wellScoped
#check @Effect4.Target.Structured.graphOf_closed
#check @Effect4.Target.Structured.structuredBody_wellScoped
#check (@Effect4.Target.Structured.BreakScopedStatement : Prop)

/-! ## The predicate itself -/

-- A bare `break` or `continue` names no label and is always in scope.
#guard wellScopedList [] [] [Stmt.breakTo none, Stmt.continueTo none]
-- A labelled jump with no binder is refused.
#guard wellScopedList [] [] [Stmt.breakTo (some "L1")] = false
#guard wellScopedList [] [] [Stmt.continueTo (some "W1")] = false
-- `label L1: { break L1 }` and `W1: while (true) { continue W1 }` are in scope.
#guard wellScopedList [] [] [Stmt.labelled "L1" [Stmt.breakTo (some "L1")]]
#guard wellScopedList [] [] [Stmt.whileTrue (some "W1") [Stmt.continueTo (some "W1")]]
-- The two binders do not substitute for each other: this is the shape of
-- `E4-TARGET-CE-013`, a `continue` to a label only a block introduced.
#guard wellScopedList [] [] [Stmt.labelled "W1" [Stmt.continueTo (some "W1")]] = false
-- A nested generator is a function boundary: no jump crosses it.
#guard wellScopedList [] [] [Stmt.whileTrue (some "W1")
    [Stmt.scopedGen "r" [Stmt.continueTo (some "W1")] (.ident "onExit")]] = false

/-! ## The emitted forms are well scoped, strictly

`structuredBody_wellScoped` proves the `continue` half for every flow. These
receipts also close the `break` half on the packet's own graphs, by running the
strict predicate with empty initial scopes. -/

def cellRows : ServiceRow :=
  { name := "Cell"
    ops := [ { name := "get", index := 0, params := [], tsParams := [], answer := "Nat", tsAnswer := "number" }
           , { name := "put", index := 1, params := [("n", "Nat")], tsParams := [("n", "number")],
               answer := "Unit", tsAnswer := "void" } ] }

def program? (name : String) (table : List OpSpec) (raw : RawFlow String) : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow => some { name := name, param := ("n", raw.inputTy), result := raw.resultTy,
                       table := table, flow := flow }
  | .error _ => none

/-- The swap loop of the structured packet: a merge that is also a loop header. -/
def swapRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number", "number"], term := .choose ⟨1⟩ ⟨1⟩ ⟨2⟩ [⟨1⟩, ⟨0⟩] }
      , { id := ⟨2⟩, params := ["number", "number"], term := .ret ⟨0⟩ } ] }

def swap? : Option FlowProgram :=
  program? "swap" [{ name := "lit", kind := .lit (.nat 1), requestTy := "number",
                     answerTy := "number" }] swapRaw

/-- A straight chain: no label at all. -/
def chainRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .jump ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

-- `Flow.lowerStructured` crosses to string rendering, so it is spelled inline
-- at each use: a named wrapper here would be a test declaration reaching
-- `Classical.choice`, which the axiom gate refuses.

-- The swap loop: a merge that is also a loop header, `break L1` and `continue W1`.
#guard (swap?.bind fun program =>
    (Flow.lowerStructured cellRows program).map fun decl =>
      wellScopedList [] [] decl.stmts) = some true

-- The label-free chain.
#guard ((program? "chain" [] chainRaw).bind fun program =>
    (Flow.lowerStructured cellRows program).map fun decl =>
      wellScopedList [] [] decl.stmts) = some true

/-! ## The entry as a loop header: row `E4-TARGET-CE-013` -/

-- `choose` at site 1 back to the entry or on to a return: the entry is its own
-- loop header, so `emitWith` must wrap it in `W0: while (true)`.
def entryLoopRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨1⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

def entryLoop? : Option FlowProgram := program? "entryLoop" [] entryLoopRaw

#guard entryLoop?.isSome
#guard entryLoop?.map Flow.reducible = some true
#guard Structure.isLoopHeader
  (Flow.graphOf entryLoopRaw.blocks entryLoopRaw.entry) 0 = true

-- The emitted body is wrapped in its own loop, so the `continue W0` is bound.
#guard (entryLoop?.bind fun program =>
    (Flow.lowerStructured cellRows program).map fun decl =>
      wellScopedList [] [] decl.stmts) = some true

end Effect4Test.Target.TypeScript.StructureLawsContract
