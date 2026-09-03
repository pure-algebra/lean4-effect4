/-
Counterexample the job-runner packet found in the target lane
(`test/counterexamples/REGISTER.md`). Two rows live here.

`E4-TARGET-CE-022` is the original: a family operation of more than one
parameter had no flow request spelling, and nothing on the path from
`effect_signature` to the generated module said so. It is repaired, and the
first half of this file is the repair, stated as receipts over the same
declarations the attack named.

`E4-FLOW-CE-028` is what the repair leaves standing, and it is the reason the
job runner is shaped the way it is: a flow cannot *build* a pair. `plan` hands
a service exactly one `Val`, an atom is a unary pure wire function, and no term
of the flow language pairs two block slots. A two-parameter request can only
occupy a slot some answer already filled, so the pair has to arrive as an
answer -- `Jobs.next` hands out a job ticket -- and a flow over an operation
whose parameters come from two independent slots is still not writable.

The program both rows come from is `docs/research/2026-09-03-job-runner.md`.

No definition here traverses a string: a rendered module reaches
`Classical.choice`, so every module is rendered inside the `#guard` that reads
it and the file declares no string-traversing constant.
-/

import Effect4.Target.TypeScript.RegionLower
import Effect4.Meta.Derive

namespace Effect4Test.Counterexamples.Target.JobRequest

open Effects Effect4 Effect4.Flow Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val)

/-! ## `E4-TARGET-CE-022` — a two-parameter operation, performed (repaired)

*Attacked statement.* "Every operation an `effect_signature` admits can be
performed by a flow: the alphabet a family induces (`familyTable`) spells every
row's request, and the dispatch lowering calls every row."

It used to be false three times over: `familyTable` wrote the string
`"unsupported"` for the request of any row with more than one parameter,
admission compared that invented spelling with block parameter types by
equality and admitted a graph over it, and `Lowering.callOf` built
`receiver.op(request)` from exactly one expression whatever the arity — so the
emitted module declared `run` with two parameters and called it with one.

*The repair, as landed.* `familyTable` spells a request of `n` parameters as
the right-nested product `Effects.Trace.ToVal` builds from the parameter
product, which is the same spelling `Spelling.prod` renders; `OpSpec` carries
the parameters, so `OpSpec.arity` is the number of arguments the call takes;
and `Lowering.callOf` destructures the request slot at the call through
`Lowering.tupleArgs` (`lowering: rule.perform-tuple`). Nothing invents a type
and nothing emits a call the same module's declaration refuses.
-/

-- The packet's `run`, spelled the way the packet writes it. A doc comment
-- cannot precede `effect_signature`.
effect_signature Paired where
  | run (conn : Handle "JobQueue") (job : Nat) : Nat
      ⟪ "run a job on a connection", "the shape the flow now performs" ⟫

-- The same operation with the connection dropped: what the job runner used to
-- have to write instead.
effect_signature Single where
  | run (job : Nat) : Nat ⟪ "run a job", "the one-parameter reading" ⟫

-- A three-parameter reading, to pin that the request spelling nests to the
-- right rather than flattening.
effect_signature Triple where
  | run (conn : Handle "JobQueue") (job : Nat) (attempt : Nat) : Nat
      ⟪ "run a numbered attempt of a job on a connection" ⟫

def pairedTable : List OpSpec := familyTable Paired.rows
def singleTable : List OpSpec := familyTable Single.rows
def tripleTable : List OpSpec := familyTable Triple.rows

-- The row is well formed and the DSL gives it two TypeScript parameters, each
-- with a real spelling. That much was already true when the attack fired.
#guard (Paired.rows.row? "run").map (·.tsParams) =
  some [("conn", "JobQueue"), ("job", "number")]

-- The induced flow alphabet now spells the request instead of giving up. The
-- string `"unsupported"` is gone from the pipeline.
#guard (pairedTable.find? (·.name == "run")).map (·.requestTy) =
  some "readonly [JobQueue, number]"
#guard (singleTable.find? (·.name == "run")).map (·.requestTy) = some "number"
#guard (tripleTable.find? (·.name == "run")).map (·.requestTy) =
  some "readonly [JobQueue, readonly [number, number]]"

-- Arity is the number of arguments the call takes, not the depth of the slot.
#guard (pairedTable.find? (·.name == "run")).map OpSpec.arity = some 2
#guard (singleTable.find? (·.name == "run")).map OpSpec.arity = some 1
#guard (tripleTable.find? (·.name == "run")).map OpSpec.arity = some 3

def block (id : Nat) (params : List String) (term : RawTerm) : RawBlock String :=
  { id := ⟨id⟩, params := params, term := term }

/-- A one-`perform` graph over the two-parameter row. Its entry parameter is
the request tuple: one slot, holding what `ToVal` builds from the parameter
product. -/
def pairedRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩,
    inputTy := "readonly [JobQueue, number]", resultTy := "number",
    blocks :=
      [ block 0 ["readonly [JobQueue, number]"] (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [])
      , block 1 ["number"] (.ret ⟨0⟩) ] }

-- It is admitted, and now for the right reason: the slot's type is the
-- request's own spelling.
#guard (admit (tableAlphabet ⟨0⟩ pairedTable) pairedRaw).isOk

def pairedProgram? : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ pairedTable) pairedRaw with
  | .ok flow =>
      some { name := "pairedRun", param := ("n", "readonly [JobQueue, number]"),
             result := "number", table := pairedTable, flow := flow }
  | .error _ => none

#guard pairedProgram?.isSome

-- The module declares the method with two parameters ...
#guard (pairedProgram?.bind fun program => regionModules? [(Paired.rows, [program], [])]).map
    (fun source => decide (1 <
      (source.splitOn "readonly run: (conn: JobQueue, job: number) => Effect.Effect<number>").length))
  = some true

-- ... and calls it with two, taken apart from the one slot the flow could give
-- it. This is the repair: the emitted module is internally consistent.
#guard (pairedProgram?.bind fun program => regionModules? [(Paired.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "yield* paired.run(b0p0[0], b0p0[1])").length))
  = some true

-- The slot is declared at the tuple spelling, and `unsupported` reaches no
-- generated byte.
#guard (pairedProgram?.bind fun program => regionModules? [(Paired.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "let b0p0!: readonly [JobQueue, number]").length))
  = some true
#guard (pairedProgram?.bind fun program => regionModules? [(Paired.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "unsupported").length)) = some false

-- The one-parameter reading of the same operation is untouched: one declared
-- parameter, one argument at the call, no projection.
def singleProgram? : Option FlowProgram :=
  let raw : RawFlow String :=
    { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
      blocks := [ block 0 ["number"] (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ []), block 1 ["number"] (.ret ⟨0⟩) ] }
  match admit (tableAlphabet ⟨0⟩ singleTable) raw with
  | .ok flow =>
      some { name := "singleRun", param := ("n", "number"), result := "number",
             table := singleTable, flow := flow }
  | .error _ => none

#guard (singleProgram?.bind fun program => regionModules? [(Single.rows, [program], [])]).map
    (fun source => decide (1 <
      (source.splitOn "readonly run: (job: number) => Effect.Effect<number>").length)) = some true
#guard (singleProgram?.bind fun program => regionModules? [(Single.rows, [program], [])]).map
    (fun source => decide (1 < (source.splitOn "yield* single.run(b0p0)").length)) = some true

/-! ## `E4-FLOW-CE-028` — a flow cannot build a pair

*Attacked statement.* "With an arity-aware request spelling, a flow can perform
any operation of the family: the request slot holds the tuple, so a graph
assembles one from the values it is carrying."

It cannot. The former that fills a slot is `perform`, and `perform` names one
request `Var`; the pure rows that could compute one are literals (which answer
a constant) and atoms (which are unary wire functions, `OpKind.atom` and
`tableService`). Nothing takes two variables and answers their pair. So a
two-parameter operation is performable only when some *answer* already has the
tuple's type, which is why `Jobs.next` answers a job ticket rather than a job
id and why `Jobs.attempt` needs the `snd` atom to get the job back out.

*Forced repair.* Add a pairing former to `RawTerm`/`RegionTerm` — a term
`pair (left right : Var) (target : BlockId)` whose answer is the product of the
two slots' types — with arms in the plain and region runners, all three
lowerings and the admission clause that types it; or state everywhere that a
flow performs a multi-parameter operation only on a tuple it received.
-/

/-- The graph the attack wants: two `number` slots and a `perform` of the
two-parameter row that pairs them. There is no term for it, so the closest
legal graph performs the operation on a slot of the *wrong* type — the first
component alone. -/
def unpairedRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ block 0 ["number"] (.perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [])
      , block 1 ["number"] (.ret ⟨0⟩) ] }

-- Admission refuses it, and that refusal is the whole content of the row: the
-- request slot must already have the tuple's type, and no former builds one.
#guard (admit (tableAlphabet ⟨0⟩ pairedTable) unpairedRaw).isOk = false

-- The two readings of the ticket are one spelling, which is why the job runner
-- can perform `run` at all: an answer of that type *is* a legal request slot.
#guard (pairedTable.find? (·.name == "run")).map (·.requestTy) = some "readonly [JobQueue, number]"

-- And the only way to take one apart again is a unary atom, whose request is
-- the tuple and whose answer is a component. `Atoms.snd` in
-- `harness/trace/Generate.lean` is that atom; a hand-written row is unary
-- because a table row carries no parameters at all.
def sndRow : OpSpec :=
  { name := "snd", kind := .atom, requestTy := "readonly [JobQueue, number]",
    answerTy := "number" }

#guard sndRow.arity = 1
#guard sndRow.params = []

end Effect4Test.Counterexamples.Target.JobRequest
