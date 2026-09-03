/-
Contract packet: `test/contracts/flow-regions-lowering.contract.md` (P-T7, light
ceremony D2). Rendering receipts for a region flow in the dispatch form with a
nested scope, the refusal of a fallible release (`E4-TARGET-CE-012`), the rule
set and the declaration line. Doc comments cannot precede `#guard`.
-/

import Effect4.Target.TypeScript.RegionLower

namespace Effect4Test.Target.TypeScript.RegionLowerContract

open TypeScript Effects Effect4.Flow Effect4.Target.EffectV4

#check @Effect4.Target.EffectV4.RegionProgram
#check (@Effect4.Target.EffectV4.regionsRows : ServiceRow)
#check @Effect4.Target.EffectV4.Region.lowerDispatch
#check @Effect4.Target.EffectV4.Region.ruleSet
#check @Effect4.Target.EffectV4.Region.declarationLine
#check @Effect4.Target.EffectV4.regionModules?

example : Rule.all.length = 19 := by decide
#guard (Rule.all.map Rule.id).drop 16 = ["region-enter", "region-acquire", "region-leave"]

def rcellRows : ServiceRow :=
  { name := "RCell"
    ops := [ { name := "get", index := 0, params := [], tsParams := [], answer := "Nat", tsAnswer := "number" }
           , { name := "put", index := 1, params := [("n", "Nat")], tsParams := [("n", "number")],
               answer := "Unit", tsAnswer := "void" }
           , { name := "acquire", index := 2, params := [("n", "Nat")], tsParams := [("n", "number")],
               answer := "Nat", tsAnswer := "number" }
           , { name := "release", index := 3, params := [("n", "Nat")], tsParams := [("n", "number")],
               answer := "Unit", tsAnswer := "void" }
           , { name := "boom", index := 4, params := [("n", "Nat")], tsParams := [("n", "number")],
               answer := "Nat", tsAnswer := "number", error := some ("String", "string") }
           , { name := "releaseBoom", index := 5, params := [("n", "Nat")], tsParams := [("n", "number")],
               answer := "Unit", tsAnswer := "void", error := some ("String", "string") } ] }

def table : List OpSpec := familyTable rcellRows

def rblock (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) : RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

def regionFlow (regions : List (RegionRow String)) (blocks : List (RegionBlock String)) : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := regions, blocks := blocks }

def program? (name : String) (raw : RegionFlow String) : Option RegionProgram :=
  match admitRegions (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow => some { name := name, param := ("n", "number"), result := "number", table := table, flow := flow }
  | .error _ => none

/-- One resource, a clean leave. -/
def bothSucceed : RegionFlow String :=
  regionFlow [{ id := ⟨1⟩, parent := none, continue_ := ⟨3⟩, resultTy := "number" }]
    [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ [⟨0⟩])
    , rblock 1 (some 1) ["number"] (.acquire ⟨2⟩ ⟨0⟩ ⟨3⟩ ⟨2⟩ [⟨0⟩])
    , rblock 2 (some 1) ["number", "number"] (.leave ⟨1⟩)
    , rblock 3 none ["number"] (.plain (.ret ⟨0⟩)) ]

#guard (program? "regionBothSucceed" bothSucceed).isSome

-- The dispatch form with one nested scope, byte for byte.
#guard ((program? "regionBothSucceed" bothSucceed).bind fun program =>
    (Region.lowerDispatch rcellRows program).map (TypeScript.Render.progDecl TypeScript.house0)) = some
  ("/** Lowered from the region flow `regionBothSucceed` over `RCell` (dispatch form, nested scopes). */\n" ++
   "export const regionBothSucceed = (n: number) =>\n" ++
   "  Effect.gen(function* () {\n" ++
   "    const rCell = yield* RCell\n" ++
   "    const regions = yield* Regions\n" ++
   "    let b0p0!: number\n" ++
   "    let b1p0!: number\n" ++
   "    let b2p0!: number\n" ++
   "    let b2p1!: number\n" ++
   "    let b3p0!: number\n" ++
   "    b0p0 = n\n" ++
   "    let block = 0\n" ++
   "    while (true) {\n" ++
   "      switch (block) {\n" ++
   "        case 0: {\n" ++
   "          b1p0 = b0p0\n" ++
   "          yield* regions.enter(1)\n" ++
   "          const r1 = yield* Effect.scoped(Effect.onExit(Effect.gen(function* () {\n" ++
   "            let block1 = 1\n" ++
   "            while (true) {\n" ++
   "              switch (block1) {\n" ++
   "                case 1: {\n" ++
   "                  const a1 = yield* Effect.acquireRelease(rCell.acquire(b1p0), (a, exit) => regions.finalizer(1, exit).pipe(Effect.andThen(rCell.release(a))))\n" ++
   "                  b2p0 = b1p0\n" ++
   "                  b2p1 = a1\n" ++
   "                  block1 = 2\n" ++
   "                  continue\n" ++
   "                }\n" ++
   "                case 2: {\n" ++
   "                  return b2p1\n" ++
   "                }\n" ++
   "              }\n" ++
   "            }\n" ++
   "          }), (exit) => regions.leave(1, exit)))\n" ++
   "          b3p0 = r1\n" ++
   "          block = 3\n" ++
   "          continue\n" ++
   "        }\n" ++
   "        case 3: {\n" ++
   "          return b3p0\n" ++
   "        }\n" ++
   "      }\n" ++
   "    }\n" ++
   "  })\n")

#guard ((program? "regionBothSucceed" bothSucceed).map (Region.ruleSet rcellRows)) =
  some [.serviceAcquire, .dispatchLoop, .blockCase, .paramMove, .flowPerform, .performCall, .flowRet,
        .regionEnter, .regionAcquire, .regionLeave]
#guard ((program? "regionBothSucceed" bothSucceed).map (Region.declarationLine rcellRows)) =
  some "export declare const regionBothSucceed: (n: number) => Effect.Effect<number, never, RCell | Regions>;"

/-! ## E4-TARGET-CE-012: a fallible release has no lowering

`Effect.acquireRelease` types its release `Effect<unknown, never, R>`; a
release with an error row (`releaseBoom`) is admitted by the region clauses
and runs in Lean, but `lowerDispatch` refuses it rather than lowering to a
release the pinned compiler rejects (or to `orDie`, which would change its
outcome). -/

def fallibleRelease : RegionFlow String :=
  regionFlow [{ id := ⟨1⟩, parent := none, continue_ := ⟨3⟩, resultTy := "number" }]
    [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ [⟨0⟩])
    , rblock 1 (some 1) ["number"] (.acquire ⟨2⟩ ⟨0⟩ ⟨5⟩ ⟨2⟩ [⟨0⟩])
    , rblock 2 (some 1) ["number", "number"] (.leave ⟨1⟩)
    , rblock 3 none ["number"] (.plain (.ret ⟨0⟩)) ]

#guard (program? "fallible" fallibleRelease).isSome
#guard ((program? "fallible" fallibleRelease).bind fun program => Region.lowerDispatch rcellRows program).isNone

end Effect4Test.Target.TypeScript.RegionLowerContract
