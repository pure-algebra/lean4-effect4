/-
Contract packet: `test/contracts/flow-denotation.contract.md` (D1) and
`test/contracts/flow-structured-lowering.contract.md` (P-T9b), extended by
packet D3.

Receipts for `Effect4/Target/TypeScript/SkeletonSemantics.lean`: the skeleton
denotation, T3 (the dispatch form denotes the flow) and T4 on the flat fragment
(no join, no loop). The flows are the packet's own — the `incr` chain, `chooser`,
`swap` and `irreducible` of `harness/trace/Generate.lean`, rebuilt here because
the harness is not a library module.

Equality of `Program`s is not decidable — a `Program` carries a continuation —
and both `Skel.execList` and `Flow.denoteGo` are well-founded, so neither side
reduces under `rfl`. The receipts are therefore of two kinds: `#guard` for the
decidable facts each theorem's hypotheses ask for (the flow admits, the form
lowers, the graph is reducible, the graph is flat), and `example` for the
*instances* of T3 and T4 at those flows, which is what "the theorem applies
here" means when the conclusion is an equation between programs. Doc comments
cannot precede `#guard`.
-/

import Effect4.Target.TypeScript.SkeletonSemantics

open TypeScript

namespace Effect4Test.Target.TypeScript.SkeletonSemanticsContract

open Effects Effect4.Flow Effect4.Target.EffectV4
open Effects.Trace (Val)

/-! ## The frozen surface -/

#check @Effect4.Target.EffectV4.Skel.Machine
#check @Effect4.Target.EffectV4.Skel.Outcome
#check @Effect4.Target.EffectV4.Skel.simple?
#check @Effect4.Target.EffectV4.Skel.runSimple
#check @Effect4.Target.EffectV4.Skel.caseBody?
#check @Effect4.Target.EffectV4.Skel.execList
#check @Effect4.Target.EffectV4.Skel.execControl
#check @Effect4.Target.EffectV4.Skel.performOp
#check @Effect4.Target.EffectV4.Skel.afterFell
#check @Effect4.Target.EffectV4.Skel.afterBlock
#check @Effect4.Target.EffectV4.Skel.loopRun
#check @Effect4.Target.EffectV4.Skel.loopCatch
#check @Effect4.Target.EffectV4.Skel.dispatchRun
#check @Effect4.Target.EffectV4.Skel.dispatchCatch
#check @Effect4.Target.EffectV4.Skel.Holds
#check @Effect4.Target.EffectV4.Skel.start
#check @Effect4.Target.EffectV4.Skel.denoteNodes
#check @Effect4.Target.EffectV4.Skeleton.denote
#check @Effect4.Target.EffectV4.Skel.execList_skeletonBlock
#check @Effect4.Target.EffectV4.Skel.execList_skeletonBlockWith
#check @Effect4.Target.EffectV4.Skel.dispatchRun_denoteFuel
#check @Effect4.Target.EffectV4.skeletonDispatch_denote
#check @Effect4.Target.EffectV4.Skel.Flat
#check @Effect4.Target.EffectV4.Skel.flatBelow
#check @Effect4.Target.EffectV4.Skel.emitNode_flat
#check @Effect4.Target.EffectV4.Skel.execList_emitNode_flat
#check @Effect4.Target.EffectV4.skeletonStructured_denote
#check @Effect4.Target.EffectV4.skeletonStructured_denote_dispatch

/-! ## The machine, on its own -/

def blank : Skel.Machine := Skel.start "n" (.nat 7)

-- The binder holds the input and every other slot is `unit`.
#guard blank.vals (.input "n") = Val.nat 7
#guard blank.vals (.param ⟨0⟩ 0) = Val.unit
#guard blank.index "block" = 0

-- A run of simple nodes folds; a control node does not.
#guard (Skel.runSimple blank [Skeleton.enterBlock ⟨3⟩]).isSome
#guard (Skel.simple? blank (Skeleton.gotoBlock "block" ⟨1⟩)).isNone
#guard (Skel.simple? blank (Skeleton.ret (.param ⟨0⟩ 0))).isNone
#guard ((Skel.runSimple blank [Skeleton.assign (.param ⟨0⟩ 0) (.input "n")]).map
  fun m => m.vals (.param ⟨0⟩ 0)) = some (Val.nat 7)

-- The switch resolves a case by the block's own index.
#guard (Skel.caseBody? [(0, [Skeleton.enterBlock ⟨0⟩]), (1, [])] 1).map List.length = some 0
#guard (Skel.caseBody? [(0, [Skeleton.enterBlock ⟨0⟩]), (1, [])] 0).map List.length = some 1
#guard (Skel.caseBody? [(0, [])] 2).isNone

/-! ## The packet's flows -/

def cellRows : ServiceRow :=
  { name := "Cell"
    ops := [ { name := "get", index := 0, params := [], tsParams := [], answer := "Nat",
               tsAnswer := "number" }
           , { name := "put", index := 1, params := [("n", "Nat")], tsParams := [("n", "number")],
               answer := "Unit", tsAnswer := "void" } ] }

def cellTable : List OpSpec :=
  -- `get` takes a `number` request rather than the harness's `void`: the flow
  -- alphabet types a `perform`'s request by the block parameter it names, and
  -- this chain names its own input.
  [ { name := "get", kind := .family, requestTy := "number", answerTy := "number" }
  , { name := "put", kind := .family, requestTy := "number", answerTy := "void" } ]

def program? (name : String) (table : List OpSpec) (raw : RawFlow String) : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow => some { name := name, param := ("n", raw.inputTy), result := raw.resultTy,
                       table := table, flow := flow }
  | .error _ => none

/-- The shape of the harness's `incr`: read the cell, write it back, return.
A straight chain — no join and no loop. -/
def incrRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number", "number"], term := .perform ⟨1⟩ ⟨1⟩ ⟨2⟩ [⟨1⟩] }
      , { id := ⟨2⟩, params := ["number", "void"], term := .ret ⟨0⟩ } ] }

/-- `choose` at site 7 between two returns of the input: two leaves, no join. -/
def chooserRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨7⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ }
      , { id := ⟨2⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

def swapTable : List OpSpec :=
  [{ name := "lit", kind := .lit (.nat 1), requestTy := "number", answerTy := "number" }]

/-- A literal beside the input, then a chosen self-loop that swaps the two
parameters: block 1 is a loop header, so the graph is not flat. -/
def swapRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number", "number"], term := .choose ⟨1⟩ ⟨1⟩ ⟨2⟩ [⟨1⟩, ⟨0⟩] }
      , { id := ⟨2⟩, params := ["number", "number"], term := .ret ⟨0⟩ } ] }

/-- A cycle entered at two blocks: admitted, but not reducible. -/
def irreducibleRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨0⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .choose ⟨1⟩ ⟨2⟩ ⟨3⟩ [⟨0⟩] }
      , { id := ⟨2⟩, params := ["number"], term := .choose ⟨2⟩ ⟨1⟩ ⟨3⟩ [⟨0⟩] }
      , { id := ⟨3⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

theorem erase_of_program? {name : String} {table : List OpSpec} {raw : RawFlow String}
    {program : FlowProgram} (built : program? name table raw = some program) :
    program.flow.erase = raw := by
  simp only [program?] at built
  split at built
  · rename_i accepted
    obtain rfl : program = _ := (Option.some.inj built).symm
    exact erase_admit accepted
  · exact absurd built (by simp)

def incr? : Option FlowProgram := program? "incr" cellTable incrRaw
def chooser? : Option FlowProgram := program? "chooser" [] chooserRaw
def swap? : Option FlowProgram := program? "swap" swapTable swapRaw
def irreducible? : Option FlowProgram := program? "irreducible" [] irreducibleRaw

-- All four are admitted, and all four lower to a dispatch skeleton.
#guard incr?.isSome
#guard chooser?.isSome
#guard swap?.isSome
#guard irreducible?.isSome
#guard (incr?.bind (Flow.skeletonDispatch cellRows)).isSome
#guard (chooser?.bind (Flow.skeletonDispatch cellRows)).isSome
#guard (swap?.bind (Flow.skeletonDispatch cellRows)).isSome
#guard (irreducible?.bind (Flow.skeletonDispatch cellRows)).isSome

/-! ## T3 at the packet's flows

The theorem, instantiated: whatever the dispatch form of this flow is, its
denotation is the flow's denotation. -/

theorem incr_dispatch (tape : Tape) (input : Val) :
    ∀ program ∈ incr?, ∀ nodes ∈ Flow.skeletonDispatch cellRows program,
      Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
          program.param.1 nodes tape input
        = Effect4.Flow.denote program.flow tape input :=
  fun program _ nodes built => skeletonDispatch_denote cellRows program tape input built

theorem chooser_dispatch (tape : Tape) (input : Val) :
    ∀ program ∈ chooser?, ∀ nodes ∈ Flow.skeletonDispatch cellRows program,
      Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
          program.param.1 nodes tape input
        = Effect4.Flow.denote program.flow tape input :=
  fun program _ nodes built => skeletonDispatch_denote cellRows program tape input built

theorem swap_dispatch (tape : Tape) (input : Val) :
    ∀ program ∈ swap?, ∀ nodes ∈ Flow.skeletonDispatch cellRows program,
      Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
          program.param.1 nodes tape input
        = Effect4.Flow.denote program.flow tape input :=
  fun program _ nodes built => skeletonDispatch_denote cellRows program tape input built

theorem irreducible_dispatch (tape : Tape) (input : Val) :
    ∀ program ∈ irreducible?, ∀ nodes ∈ Flow.skeletonDispatch cellRows program,
      Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
          program.param.1 nodes tape input
        = Effect4.Flow.denote program.flow tape input :=
  fun program _ nodes built => skeletonDispatch_denote cellRows program tape input built

/-! ## Which graphs are flat -/

-- `incr` and `chooser` are flat: no join, no loop. `swap`'s block 1 is a loop
-- header, so T4 does not reach it; `irreducible` has no structured form at all.
#guard Skel.flatBelow (Flow.graphOf incrRaw.blocks incrRaw.entry)
#guard Skel.flatBelow (Flow.graphOf chooserRaw.blocks chooserRaw.entry)
#guard Skel.flatBelow (Flow.graphOf swapRaw.blocks swapRaw.entry) = false
#guard Structure.isLoopHeader (Flow.graphOf swapRaw.blocks swapRaw.entry) 1
#guard Structure.reducible (Flow.graphOf irreducibleRaw.blocks irreducibleRaw.entry) = false
#guard (irreducible?.bind (Flow.skeletonStructured cellRows)).isNone

-- Both flat graphs do have a structured form.
#guard (incr?.bind (Flow.skeletonStructured cellRows)).isSome
#guard (chooser?.bind (Flow.skeletonStructured cellRows)).isSome

theorem incr_flat : Skel.Flat (Flow.graphOf incrRaw.blocks incrRaw.entry) :=
  Skel.flat_of_flatBelow _ (Skel.graphOf_bounded _ _) (by decide)

theorem chooser_flat : Skel.Flat (Flow.graphOf chooserRaw.blocks chooserRaw.entry) :=
  Skel.flat_of_flatBelow _ (Skel.graphOf_bounded _ _) (by decide)

/-! ## T4 at the flat flows

The two forms of a flat flow denote the same `Program`. -/

theorem incr_structured_dispatch (tape : Tape) (input : Val) :
    ∀ program ∈ incr?, ∀ structured ∈ Flow.skeletonStructured cellRows program,
      ∀ dispatch ∈ Flow.skeletonDispatch cellRows program,
        Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
            program.param.1 structured tape input
          = Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
            program.param.1 dispatch tape input := by
  intro program admitted structured builtStructured dispatch builtDispatch
  refine skeletonStructured_denote_dispatch cellRows program tape input ?_ builtStructured
    builtDispatch
  rw [erase_of_program? admitted]
  exact incr_flat

theorem chooser_structured_dispatch (tape : Tape) (input : Val) :
    ∀ program ∈ chooser?, ∀ structured ∈ Flow.skeletonStructured cellRows program,
      ∀ dispatch ∈ Flow.skeletonDispatch cellRows program,
        Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
            program.param.1 structured tape input
          = Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
            program.param.1 dispatch tape input := by
  intro program admitted structured builtStructured dispatch builtDispatch
  refine skeletonStructured_denote_dispatch cellRows program tape input ?_ builtStructured
    builtDispatch
  rw [erase_of_program? admitted]
  exact chooser_flat

end Effect4Test.Target.TypeScript.SkeletonSemanticsContract
