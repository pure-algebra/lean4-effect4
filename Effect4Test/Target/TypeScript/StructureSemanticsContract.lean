/-
Independent breaker packet: test/contracts/structure-semantics.contract.md.
Actual ordinary-Flow outputs, complete Programs, explicit sufficient fuel.
Controls are independent of the proposed public theorems.
-/

import Effect4.Target.TypeScript.StructureSemantics
import Effect4Test.Target.TypeScript.StructuredLowerContract

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open TypeScript Effects Effect4 Effect4.Flow Effect4.Target.EffectV4
open Effects.Trace (Val)

namespace Effect4Test.Target.TypeScript.StructureSemanticsContract

open Effect4Test.Target.TypeScript.StructuredLowerContract
  (program? cellRows swapRaw swapTable irreducibleRaw)

private def operations : List OpSpec :=
  [ { name := "inc", kind := .family, requestTy := "number", answerTy := "number" }
  , { name := "timesTen", kind := .family, requestTy := "number", answerTy := "number" } ]

-- Two real merges. The second merge is dominated by the first, not entry.
private def nestedMerge : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩,
    inputTy := "number", resultTy := "number", blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨7⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨3⟩ [] }
      , { id := ⟨2⟩, params := ["number"], term := .perform ⟨1⟩ ⟨0⟩ ⟨3⟩ [] }
      , { id := ⟨3⟩, params := ["number"], term := .choose ⟨8⟩ ⟨4⟩ ⟨5⟩ [⟨0⟩] }
      , { id := ⟨4⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨6⟩ [] }
      , { id := ⟨5⟩, params := ["number"], term := .perform ⟨1⟩ ⟨0⟩ ⟨6⟩ [] }
      , { id := ⟨6⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

-- Continue the inner loop, leave it, then continue the outer loop.
private def nestedLoops : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩,
    inputTy := "number", resultTy := "number", blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .jump ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .choose ⟨7⟩ ⟨2⟩ ⟨5⟩ [⟨0⟩] }
      , { id := ⟨2⟩, params := ["number"], term := .choose ⟨8⟩ ⟨3⟩ ⟨4⟩ [⟨0⟩] }
      , { id := ⟨3⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨2⟩ [] }
      , { id := ⟨4⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [] }
      , { id := ⟨5⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

-- The same nested loops with the outer header itself as entry. Removing
-- block 0 also separates graph positions from source block identifiers.
private def entryLoops : RawFlow String :=
  { nestedLoops with entry := ⟨1⟩, roots := [⟨1⟩], blocks := nestedLoops.blocks.tail }

private def mergeTape : Tape := [⟨⟨7⟩, true⟩, ⟨⟨8⟩, false⟩]
private def loopTape : Tape :=
  [⟨⟨7⟩, true⟩, ⟨⟨8⟩, true⟩, ⟨⟨8⟩, false⟩, ⟨⟨7⟩, false⟩]

-- All alphabet operations remain algebraic, including literal-spelled ones.
-- This independent handler deliberately answers the swap's literal with 8.
private def service (table : List OpSpec) : FlowService (tableAlphabet ⟨0⟩ table) Id where
  handle op request := match request with
    | .nat n => if op.val = 0 then .nat (n + 1) else .nat (10 * n)
    | _ => .str "arbitrary answer"
  pure _ := false

private def readProgram (table : List OpSpec)
    (meaning : Program (FullSig (tableAlphabet ⟨0⟩ table)) (RunResult × Tape)) :=
  (interpretRun (service table) (tableNameOf ⟨0⟩ table) meaning).run []

private def observed (structured : Bool) (table : List OpSpec) (raw : RawFlow String)
    (tape : Tape) (extra : Nat := 0) (input : Val := .nat 7) :
    Option ((RunResult × Tape) × Effect4.Trace.Log) := do
  let program ← program? "probe" table raw
  let nodes ← if structured then Flow.skeletonStructured cellRows program
    else Flow.skeletonDispatch cellRows program
  pure (readProgram program.table
    (Skeleton.denote (tableAlphabet ⟨0⟩ program.table)
      (fuelFor program.flow.erase tape + extra) program.param.1 nodes tape input))

private def sourceObserved (table : List OpSpec) (raw : RawFlow String)
    (tape : Tape) (input : Val := .nat 7) :
    ((RunResult × Tape) × Effect4.Trace.Log) :=
  readProgram table (denoteFuel (fuelFor raw tape) raw raw.entry [input] tape)

private def resultOf (table : List OpSpec) (raw : RawFlow String) (tape : Tape)
    (extra : Nat := 0) (input : Val := .nat 7) : Option (RunResult × Tape) :=
  (observed true table raw tape extra input).map (·.1)

/-! Existing-meaning controls: no new theorem is used below. -/

#guard (program? "merge" operations nestedMerge).isSome
#guard (program? "loops" operations nestedLoops).isSome
#guard Skel.flatBelow (Flow.graphOf nestedMerge.blocks nestedMerge.entry) = false
#guard Skel.flatBelow (Flow.graphOf nestedLoops.blocks nestedLoops.entry) = false
#guard Structure.isMerge (Flow.graphOf nestedMerge.blocks nestedMerge.entry) 3
#guard Structure.isMerge (Flow.graphOf nestedMerge.blocks nestedMerge.entry) 6
#guard Structure.idom (Flow.graphOf nestedMerge.blocks nestedMerge.entry) 6 = some 3
#guard Structure.isLoopHeader (Flow.graphOf nestedLoops.blocks nestedLoops.entry) 1
#guard Structure.isLoopHeader (Flow.graphOf nestedLoops.blocks nestedLoops.entry) 2
#guard Skel.flatBelow (Flow.graphOf swapRaw.blocks swapRaw.entry) = false
#guard ((program? "irreducible" [] irreducibleRaw).bind (Flow.skeletonStructured cellRows)).isNone

#guard observed true operations nestedMerge mergeTape =
  some (sourceObserved operations nestedMerge mergeTape)
#guard observed true operations nestedMerge mergeTape =
  observed false operations nestedMerge mergeTape
#guard resultOf operations nestedMerge mergeTape = some (.done (.nat 80), [])
#guard resultOf operations nestedMerge [⟨⟨7⟩, false⟩, ⟨⟨8⟩, true⟩] =
  some (.done (.nat 71), [])
#guard (observed true operations nestedMerge mergeTape).map (·.2) = some
  [.decide 7 true, .op "inc" (.nat 7), .answer "inc" (.nat 8),
   .decide 8 false, .op "timesTen" (.nat 8), .answer "timesTen" (.nat 80),
   .done (.success (.nat 80))]
#guard observed true operations nestedMerge mergeTape 37 =
  observed true operations nestedMerge mergeTape

#guard observed true operations nestedLoops loopTape =
  some (sourceObserved operations nestedLoops loopTape)
#guard observed true operations nestedLoops loopTape =
  observed false operations nestedLoops loopTape
#guard resultOf operations nestedLoops loopTape = some (.done (.nat 9), [])
#guard resultOf operations nestedLoops [⟨⟨7⟩, false⟩] = some (.done (.nat 7), [])
#guard observed true operations nestedLoops loopTape 37 =
  observed true operations nestedLoops loopTape
#guard resultOf operations nestedLoops [] = some (.frontier (.unansweredDecision ⟨7⟩), [])
#guard resultOf operations nestedLoops [⟨⟨7⟩, true⟩, ⟨⟨8⟩, true⟩] =
  some (.frontier (.unansweredDecision ⟨8⟩), [])
#guard observed true operations nestedLoops [⟨⟨7⟩, true⟩, ⟨⟨8⟩, true⟩] =
  some (sourceObserved operations nestedLoops [⟨⟨7⟩, true⟩, ⟨⟨8⟩, true⟩])
#guard resultOf operations nestedLoops [⟨⟨7⟩, true⟩, ⟨⟨99⟩, false⟩] =
  some (.refusedSite ⟨8⟩ ⟨99⟩, [⟨⟨99⟩, false⟩])
#guard observed true operations nestedLoops [⟨⟨7⟩, true⟩, ⟨⟨99⟩, false⟩] =
  some (sourceObserved operations nestedLoops [⟨⟨7⟩, true⟩, ⟨⟨99⟩, false⟩])
#guard resultOf operations nestedLoops (loopTape ++ [⟨⟨99⟩, true⟩]) =
  some (.done (.nat 9), [⟨⟨99⟩, true⟩])

#guard (program? "entryLoops" operations entryLoops).isSome
#guard Structure.isLoopHeader (Flow.graphOf entryLoops.blocks entryLoops.entry)
  (Flow.graphOf entryLoops.blocks entryLoops.entry).entry
#guard observed true operations entryLoops loopTape =
  some (sourceObserved operations entryLoops loopTape)
#guard observed true operations entryLoops loopTape =
  observed false operations entryLoops loopTape
#guard resultOf operations entryLoops loopTape = some (.done (.nat 9), [])

#guard observed true swapTable swapRaw [⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩] =
  some (sourceObserved swapTable swapRaw [⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩])
#guard resultOf swapTable swapRaw [⟨⟨1⟩, false⟩] = some (.done (.nat 8), [])
#guard resultOf swapTable swapRaw [⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩] = some (.done (.nat 7), [])
#guard resultOf swapTable swapRaw [⟨⟨1⟩, true⟩, ⟨⟨1⟩, true⟩, ⟨⟨1⟩, false⟩] =
  some (.done (.nat 8), [])
#guard observed true swapTable swapRaw [⟨⟨1⟩, true⟩] =
  some (sourceObserved swapTable swapRaw [⟨⟨1⟩, true⟩])
#guard resultOf swapTable swapRaw [⟨⟨1⟩, true⟩, ⟨⟨9⟩, false⟩] =
  some (.refusedSite ⟨1⟩ ⟨9⟩, [⟨⟨9⟩, false⟩])
#guard resultOf swapTable swapRaw [⟨⟨1⟩, false⟩] 0 (.bool true) =
  some (.done (.str "arbitrary answer"), [])


/- BEGIN STRUCTURE-SEMANTICS-SURFACE -/

#check (@Effect4.Target.EffectV4.skeletonStructured_denote_of_fuelFor_le :
  (rows : ServiceRow) → (program : FlowProgram) → (fuel : Nat) →
  (tape : Tape) → (input : Val) → {nodes : List Skeleton} →
  fuelFor program.flow.erase tape ≤ fuel → program.interrupts = false →
  Flow.skeletonStructured rows program = some nodes →
  Skeleton.denote (tableAlphabet ⟨0⟩ program.table) fuel program.param.1 nodes tape input =
    Effect4.Flow.denote program.flow tape input)

#check (@Effect4.Target.EffectV4.skeletonStructured_denote_dispatch_of_emitted :
  (rows : ServiceRow) → (program : FlowProgram) → (tape : Tape) → (input : Val) →
  {structured dispatch : List Skeleton} → program.interrupts = false →
  Flow.skeletonStructured rows program = some structured →
  Flow.skeletonDispatch rows program = some dispatch →
  Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
      program.param.1 structured tape input =
    Skeleton.denote (tableAlphabet ⟨0⟩ program.table) (fuelFor program.flow.erase tape)
      program.param.1 dispatch tape input)

-- The old flat statement remains separately available with its old meaning.
#check @Effect4.Target.EffectV4.skeletonStructured_denote_dispatch

-- Complete Program equality transports through every handler, including
-- handlers that refuse an operation, fail, or retain an external state.
example {M : Type → Type} [Monad M] (rows : ServiceRow) (program : FlowProgram)
    (fuel : Nat) (tape : Tape) (input : Val) {nodes : List Skeleton}
    (enough : fuelFor program.flow.erase tape ≤ fuel)
    (noInterrupts : program.interrupts = false)
    (built : Flow.skeletonStructured rows program = some nodes)
    (handler : Handler (FullSig (tableAlphabet ⟨0⟩ program.table)) M) :
    interpret handler
      (Skeleton.denote (tableAlphabet ⟨0⟩ program.table) fuel program.param.1 nodes tape input) =
    interpret handler (Effect4.Flow.denote program.flow tape input) :=
  congrArg (interpret handler)
    (skeletonStructured_denote_of_fuelFor_le rows program fuel tape input enough noInterrupts built)

/- END STRUCTURE-SEMANTICS-SURFACE -/

end Effect4Test.Target.TypeScript.StructureSemanticsContract
