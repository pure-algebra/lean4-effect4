/-
Contract packet: `test/contracts/flow-structured-lowering.contract.md` (P-T9b,
light ceremony D2). The structured form of a checked flow: reducibility, the
byte-exact form of the swap loop, the dispatch fallback on an irreducible
graph, and the rule set. Doc comments cannot precede `#guard`.
-/

import Effect4.Target.TypeScript.StructuredLower

namespace Effect4Test.Target.TypeScript.StructuredLowerContract

open TypeScript Effects Effect4.Flow Effect4.Target.EffectV4

#check @Effect4.Target.EffectV4.structuredShapes
#check @Effect4.Target.EffectV4.Flow.graphOf
#check @Effect4.Target.EffectV4.Flow.reducible
#check @Effect4.Target.EffectV4.Flow.lowerStructured
#check @Effect4.Target.EffectV4.Flow.lowerBest
#check @Effect4.Target.EffectV4.Flow.structuredRuleSet
#check @Effect4.Target.EffectV4.Region.lowerStructured
#check @Effect4.Target.EffectV4.structuredModules?

-- The structured group of the census, by id. The list itself is pinned once,
-- in `FlowLowerContract.lean`; nothing here reads a position (survey finding
-- H9).
#guard Rule.ofId? "structured-loop" = some .structuredLoop
#guard Rule.ofId? "structured-merge" = some .structuredMerge
#guard Rule.ofId? "structured-continue" = some .structuredContinue
#guard Rule.ofId? "structured-break" = some .structuredBreak
#guard Rule.ofId? "dispatch-fallback" = some .dispatchFallback
#guard [Rule.structuredLoop, .structuredMerge, .structuredContinue, .structuredBreak,
        .dispatchFallback].all (Rule.all.contains ·)

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

/-! ## The swap loop: a merge that is a loop header -/

def swapTable : List OpSpec :=
  [OpSpec.unary "lit" (.lit (.nat 1)) "number" "number"]

def swapRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number", "number"], term := .choose ⟨1⟩ ⟨1⟩ ⟨2⟩ [⟨1⟩, ⟨0⟩] }
      , { id := ⟨2⟩, params := ["number", "number"], term := .ret ⟨0⟩ } ] }

def swap? : Option FlowProgram := program? "swap" swapTable swapRaw

#guard swap?.isSome
#guard swap?.map Flow.reducible = some true

-- The structured form: the entry block breaks into the loop's label, the loop
-- continues on the left arm and returns on the right.
#guard (swap?.bind fun program =>
    (Flow.lowerStructured cellRows program).map (TypeScript.Render.progDecl TypeScript.house0)) = some
  ("/** Lowered from the flow `swap` over `Cell` (structured form). */\n" ++
   "export const swap = (n: number) =>\n" ++
   "  Effect.gen(function* () {\n" ++
   "    const decisions = yield* Decisions\n" ++
   "    let b0p0!: number\n" ++
   "    let b1p0!: number\n" ++
   "    let b1p1!: number\n" ++
   "    let b2p0!: number\n" ++
   "    let b2p1!: number\n" ++
   "    b0p0 = n\n" ++
   "    L1: {\n" ++
   "      let a0 = 1\n" ++
   "      b1p0 = b0p0\n" ++
   "      b1p1 = a0\n" ++
   "      break L1\n" ++
   "    }\n" ++
   "    W1: while (true) {\n" ++
   "      const c1 = yield* decisions.choose(1)\n" ++
   "      if (c1) {\n" ++
   "        let m0 = b1p1\n" ++
   "        let m1 = b1p0\n" ++
   "        b1p0 = m0\n" ++
   "        b1p1 = m1\n" ++
   "        continue W1\n" ++
   "      } else {\n" ++
   "        b2p0 = b1p1\n" ++
   "        b2p1 = b1p0\n" ++
   "        return b2p0\n" ++
   "      }\n" ++
   "    }\n" ++
   "  })\n")

#guard (swap?.map (Flow.structuredRuleSet cellRows)) =
  some [.dispatchLoop, .blockCase, .flowLiteral, .paramMove, .chooseIf, .flowRet,
        .structuredLoop, .structuredContinue, .structuredMerge, .structuredBreak]

/-! ## An irreducible graph keeps the dispatch form -/

def irreducibleRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨0⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .choose ⟨1⟩ ⟨2⟩ ⟨3⟩ [⟨0⟩] }
      , { id := ⟨2⟩, params := ["number"], term := .choose ⟨2⟩ ⟨1⟩ ⟨3⟩ [⟨0⟩] }
      , { id := ⟨3⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

def irreducible? : Option FlowProgram := program? "irreducible" [] irreducibleRaw

#guard irreducible?.isSome
#guard irreducible?.map Flow.reducible = some false
#guard (irreducible?.bind (Flow.lowerStructured cellRows)).isNone
-- `lowerBest` is the dispatch form there, byte for byte.
#guard (irreducible?.bind fun program =>
    (Flow.lowerBest cellRows program).map (TypeScript.Render.progDecl TypeScript.house0)) =
  (irreducible?.bind fun program =>
    (Flow.lowerDispatch cellRows program).map (TypeScript.Render.progDecl TypeScript.house0))
#guard (irreducible?.map (Flow.structuredRuleSet cellRows)) =
  some [.dispatchLoop, .blockCase, .chooseIf, .paramMove, .flowRet, .dispatchFallback]

/-! ## A straight chain needs no label at all -/

def chainRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .jump ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

#guard ((program? "chain" [] chainRaw).bind fun program =>
    (Flow.lowerStructured cellRows program).map (·.stmts)) ==
  some [ .letDefinite "b0p0" "number", .letDefinite "b1p0" "number", .assign "b0p0" (.ident "n")
       , .assign "b1p0" (.ident "b0p0"), .ret (.ident "b1p0") ]

end Effect4Test.Target.TypeScript.StructuredLowerContract
