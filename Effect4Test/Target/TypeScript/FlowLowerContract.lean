/-
Contract packet: `test/contracts/flow-dispatch-lowering.contract.md` (P-T9a, light
ceremony D2). Rendering receipts for the dispatch form, the self-edge parallel
move (`E4-TARGET-CE-011`), and the rule census in both directions.
Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Target.TypeScript.FlowLower

namespace Effect4Test.Target.TypeScript.FlowLowerContract

open TypeScript Effects Effect4.Flow Effect4.Target.EffectV4

#check @Effect4.Target.EffectV4.FlowProgram
#check (@Effect4.Target.EffectV4.decisionsRows : ServiceRow)
#check (@Effect4.Target.EffectV4.Flow.paramVar : BlockId → Nat → String)
#check @Effect4.Target.EffectV4.Flow.lowerDispatch
#check @Effect4.Target.EffectV4.Flow.ruleSet
#check @Effect4.Target.EffectV4.Flow.declarationLine
#check @Effect4.Target.EffectV4.flowModules?

/-! ## The rule census -/

example : Rule.all.length = 16 := by decide
example : Rule.all.Nodup := Rule.all_nodup
#guard (Rule.all.map Rule.id).drop 8 =
  ["dispatch-loop", "block-case", "param-move", "flow-perform", "flow-atom", "flow-literal",
   "choose-if", "flow-ret"]
#guard Rule.ofId? "param-move" = some .paramMove

/-! ## A chooser: acquires Decisions only, one case per block -/

def cellRows : ServiceRow :=
  { name := "Cell"
    ops := [ { name := "get", index := 0, params := [], tsParams := [], answer := "Nat", tsAnswer := "number" }
           , { name := "put", index := 1, params := [("n", "Nat")], tsParams := [("n", "number")],
               answer := "Unit", tsAnswer := "void" } ] }

def chooserRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨7⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ }
      , { id := ⟨2⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

def program? (name : String) (table : List OpSpec) (raw : RawFlow String) : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow => some { name := name, param := ("n", raw.inputTy), result := raw.resultTy,
                       table := table, flow := flow }
  | .error _ => none

def chooser? : Option FlowProgram := program? "chooser" [] chooserRaw

#guard chooser?.isSome

-- The chooser's dispatch form, byte for byte. (Rendering traverses strings and
-- reaches `Classical.choice`, so it stays inside the `#guard`, never in a `def`.)
#guard (chooser?.bind fun program =>
    (Flow.lowerDispatch cellRows program).map (TypeScript.Render.progDecl TypeScript.house0)) = some
  ("/** Lowered from the flow `chooser` over `Cell` (dispatch form). */\n" ++
   "export const chooser = (n: number) =>\n" ++
   "  Effect.gen(function* () {\n" ++
   "    const decisions = yield* Decisions\n" ++
   "    let b0p0!: number\n" ++
   "    let b1p0!: number\n" ++
   "    let b2p0!: number\n" ++
   "    b0p0 = n\n" ++
   "    let block = 0\n" ++
   "    while (true) {\n" ++
   "      switch (block) {\n" ++
   "        case 0: {\n" ++
   "          const c0 = yield* decisions.choose(7)\n" ++
   "          if (c0) {\n" ++
   "            b1p0 = b0p0\n" ++
   "            block = 1\n" ++
   "            continue\n" ++
   "          } else {\n" ++
   "            b2p0 = b0p0\n" ++
   "            block = 2\n" ++
   "            continue\n" ++
   "          }\n" ++
   "        }\n" ++
   "        case 1: {\n" ++
   "          return b1p0\n" ++
   "        }\n" ++
   "        case 2: {\n" ++
   "          return b2p0\n" ++
   "        }\n" ++
   "      }\n" ++
   "    }\n" ++
   "  })\n")

#guard (chooser?.map (Flow.ruleSet cellRows)) =
  some [.dispatchLoop, .blockCase, .chooseIf, .paramMove, .flowRet]
#guard (chooser?.map (Flow.declarationLine cellRows)) =
  some "export declare const chooser: (n: number) => Effect.Effect<number, never, Decisions>;"

/-! ## E4-TARGET-CE-011: a self-edge move is sequential

Attack: pass block parameters on a self-edge by assigning in order, so
`choose … ⟨1⟩ … [⟨1⟩, ⟨0⟩]` (a swap) reads an already-overwritten parameter.
Repair: `param-move` reads every source into a temporary first on a self-edge;
on any other edge the target's variables are distinct and no temporary is used. -/

def swapTable : List OpSpec :=
  [{ name := "lit", kind := .lit (.nat 1), requestTy := "number", answerTy := "number" }]

def swapRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number", "number"], term := .choose ⟨1⟩ ⟨1⟩ ⟨2⟩ [⟨1⟩, ⟨0⟩] }
      , { id := ⟨2⟩, params := ["number", "number"], term := .ret ⟨0⟩ } ] }

def swap? : Option FlowProgram := program? "swap" swapTable swapRaw

#guard swap?.isSome

-- The self-edge reads both sources into temporaries before assigning; the exit edge does not.
#guard (swap?.bind fun program => Flow.lowerBlock cellRows program.table
    { id := ⟨1⟩, params := ["number", "number"], term := .choose ⟨1⟩ ⟨1⟩ ⟨2⟩ [⟨1⟩, ⟨0⟩] }) ==
  some [ .constYield "c1" (.call (.ident "decisions.choose") [.int 1])
       , .ifElse (.ident "c1")
           [ .letInit "m0" (.ident "b1p1"), .letInit "m1" (.ident "b1p0")
           , .assign "b1p0" (.ident "m0"), .assign "b1p1" (.ident "m1")
           , .assign "block" (.int 1), .continueTo none ]
           [ .assign "b2p0" (.ident "b1p1"), .assign "b2p1" (.ident "b1p0")
           , .assign "block" (.int 2), .continueTo none ] ]

-- The literal block: `let a0 = 1`, then the move appends the answer.
#guard (swap?.bind fun program => Flow.lowerBlock cellRows program.table
    { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }) ==
  some [ .letInit "a0" (.int 1), .assign "b1p0" (.ident "b0p0"), .assign "b1p1" (.ident "a0")
       , .assign "block" (.int 1), .continueTo none ]

#guard (swap?.map (Flow.ruleSet cellRows)) =
  some [.dispatchLoop, .blockCase, .flowLiteral, .paramMove, .chooseIf, .flowRet]

/-! ## A family operation acquires the service and yields -/

def getRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

def getTable : List OpSpec :=
  [{ name := "get", kind := .family, requestTy := "number", answerTy := "number" }]

def getter? : Option FlowProgram := program? "getter" getTable getRaw

#guard getter?.isSome
#guard (getter?.bind fun program => Flow.lowerBlock cellRows program.table
    { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [] }) ==
  some [ .constYield "a0" (.call (.ident "cell.get") [.ident "b0p0"])
       , .assign "b1p0" (.ident "a0"), .assign "block" (.int 1), .continueTo none ]
#guard (getter?.map (Flow.ruleSet cellRows)) =
  some [.serviceAcquire, .dispatchLoop, .blockCase, .flowPerform, .performCall, .paramMove, .flowRet]
#guard (getter?.map (Flow.declarationLine cellRows)) =
  some "export declare const getter: (n: number) => Effect.Effect<number, never, Cell>;"

end Effect4Test.Target.TypeScript.FlowLowerContract
