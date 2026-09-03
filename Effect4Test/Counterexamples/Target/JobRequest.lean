/-
Counterexample the job-runner packet found in the target lane
(`test/counterexamples/REGISTER.md`, `E4-TARGET-CE-022`): a family operation of
more than one parameter has no flow request spelling, and nothing on the path
from `effect_signature` to the generated module says so.

The program that provoked it is `docs/research/2026-09-03-job-runner.md`: the
packet's `run : Handle × Nat → Nat !! String` had to become
`run : Nat → Nat !! String`, with the connection carried by `connect`, `next`
and `disconnect` alone.
-/

import Effect4.Target.TypeScript.RegionLower
import Effect4.Meta.Derive

namespace Effect4Test.Counterexamples.Target.JobRequest

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

/-! ## `E4-TARGET-CE-022` — a two-parameter operation has no flow request

*Attacked statement.* "Every operation an `effect_signature` admits can be
performed by a flow: the alphabet a family induces (`familyTable`) spells every
row's request, and the dispatch lowering calls every row."

Three declarations make it false, and none of them refuses:

* `Effect4.Target.EffectV4.familyTable` matches `row.tsParams` and writes the
  string `"unsupported"` for any row with more than one parameter. It is a type
  spelling like any other from there on: admission compares it with block
  parameter types by equality, so a graph built over it is *admitted*, and the
  lowering declares `let b0p0!: unsupported`.
* `Effect4.Target.EffectV4.Lowering.callOf` builds `receiver.op(request)` from
  exactly one expression, whatever the row's arity, so the call the module emits
  passes one argument to a method the same module declares with two.
* `RawTerm.perform` names one request `Var` and no term of the flow language
  builds a pair from two variables — an atom is a unary pure wire function
  (`OpKind.atom`, `tableService`) — so even a correct tuple spelling would have
  nothing to put in the slot.

*Forced repair.* Refuse the row where it is first misspelled: `familyTable`
must return `Option (List OpSpec)` and fail on a row with more than one
parameter, so a family with such an operation has no flow alphabet at all and
the refusal is a `none` rather than a module that does not type-check. Lifting
the restriction instead is a packet of its own: a pairing former in `RawTerm`,
a tuple spelling in `tsOfType`, an arity-aware `callOf`, and the wire question
of whether a request pair is `Val.pair` (which is what a two-argument host call
already encodes) or a list.
-/

-- The packet's `run`, spelled the way the packet writes it. A doc comment
-- cannot precede `effect_signature`.
effect_signature Paired where
  | run (conn : Handle "JobQueue") (job : Nat) : Nat
      ⟪ "run a job on a connection", "the shape a flow cannot perform" ⟫

-- The same operation with the connection dropped: what the job runner had to
-- write instead.
effect_signature Single where
  | run (job : Nat) : Nat ⟪ "run a job", "the shape a flow can perform" ⟫

/-- Whether `needle` occurs in `haystack`. -/
def has (haystack needle : String) : Bool := (haystack.splitOn needle).length > 1

def pairedTable : List OpSpec := familyTable Paired.rows
def singleTable : List OpSpec := familyTable Single.rows

-- The row itself is well formed: the DSL admits it and gives it two TypeScript
-- parameters, each with a real spelling.
#guard (Paired.rows.row? "run").map (·.tsParams) =
  some [("conn", "JobQueue"), ("job", "number")]

-- The induced flow alphabet does not. `familyTable` gives up on the request and
-- writes a string that is not a TypeScript type.
#guard (pairedTable.find? (·.name == "run")).map (·.requestTy) = some "unsupported"
#guard (singleTable.find? (·.name == "run")).map (·.requestTy) = some "number"

def block (id : Nat) (params : List String) (term : RawTerm) : RawBlock String :=
  { id := ⟨id⟩, params := params, term := term }

/-- A one-`perform` graph over the two-parameter row. Its entry parameter has
the type `familyTable` invented, because that is the only type the request slot
can have. -/
def pairedRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩,
    inputTy := "unsupported", resultTy := "number",
    blocks :=
      [ block 0 ["unsupported"] (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [])
      , block 1 ["number"] (.ret ⟨0⟩) ] }

-- Nothing refuses it. The graph is admitted, invented type and all.
#guard (admit (tableAlphabet ⟨0⟩ pairedTable) pairedRaw).isOk

def pairedProgram? : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ pairedTable) pairedRaw with
  | .ok flow =>
      some { name := "pairedRun", param := ("n", "unsupported"), result := "number",
             table := pairedTable, flow := flow }
  | .error _ => none

#guard pairedProgram?.isSome

def pairedModule : Option String :=
  pairedProgram?.bind fun program => regionModules? [(Paired.rows, [program], [])]

#guard pairedModule.isSome

-- The module declares the method with two parameters ...
#guard pairedModule.map (fun source =>
  has source "readonly run: (conn: JobQueue, job: number) => Effect.Effect<number>") = some true

-- ... and calls it with one, which is the whole counterexample: the generated
-- module is internally inconsistent and the pipeline emitted it without a word.
#guard pairedModule.map (fun source => has source "yield* paired.run(b0p0)") = some true

-- The invented type reaches the generated source as a variable declaration.
#guard pairedModule.map (fun source => has source "let b0p0!: unsupported") = some true

-- The single-parameter reading of the same operation is consistent: one
-- declared parameter, one argument at the call.
def singleProgram? : Option FlowProgram :=
  let raw : RawFlow String :=
    { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
      blocks := [ block 0 ["number"] (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ []), block 1 ["number"] (.ret ⟨0⟩) ] }
  match admit (tableAlphabet ⟨0⟩ singleTable) raw with
  | .ok flow =>
      some { name := "singleRun", param := ("n", "number"), result := "number",
             table := singleTable, flow := flow }
  | .error _ => none

def singleModule : Option String :=
  singleProgram?.bind fun program => regionModules? [(Single.rows, [program], [])]

#guard singleModule.map (fun source =>
  has source "readonly run: (job: number) => Effect.Effect<number>") = some true
#guard singleModule.map (fun source => has source "yield* single.run(b0p0)") = some true
#guard singleModule.map (fun source => has source "unsupported") = some false

end Effect4Test.Counterexamples.Target.JobRequest
