import Effect4.Meta.Derive
import Effect4.Runtime.Scope
import Effect4.Target.TypeScript.Trace
import Effect4.Target.TypeScript.Lower
import Effect4.Target.TypeScript.ScriptFlow
import Effect4.Target.TypeScript.ScriptDenotation
import Effect4.Target.TypeScript.FlowLower
import Effect4.Target.TypeScript.RegionLower
import Effect4.Target.TypeScript.StructuredLower
import Effect4.Flow.Region
import Effect4.Semantics.Approximation
import Effect4.Semantics.RegionSimulation
import Effect4.Semantics.RegionDenotation
import Effect4.Concurrency.FiberFamily
import Effect4.Stateful.RefFamily
import Effect4.Stateful.DeferredFamily
import Effect4.Runtime.ScopeFamily
import Effect4.Context.ContextFamily
import Effect4.Layer.LayerFamily

/-!
The trace harness family. `main fixture` prints the generated Effect v4 module,
`main golden <program>` prints the Lean-expected trace of one program under
the empty tape, and `main masks` prints the registered mask table. Every
golden is the traced service's log plus the outcome, rendered by
`Effect4.Target.TypeScript.Trace`; `check.sh` byte-compares the outputs with
`fixture.ts` and `generated/traces/` and then runs the host.
-/

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4 Effect4.FiberFamily Effect4.LayerFamily
  Effect4.DeferredFamily Effect4.ScopeFamily Effect4.ContextFamily

/-! ## Golden admission: what the host can carry exactly

A JavaScript number is an IEEE-754 double, so above `2^53 - 1` it is not the
integer it prints and a row carrying one would be a fiction. `Effects.Trace.Val`
is unbounded, so the refusal has to be stated here, at emission: a golden whose
log leaves the safe range is not written at all. The host tracer refuses the
same values from the other side (`harness/trace/tracer.ts` `wire`), so neither
face can quietly produce a row the other cannot.
counterexample: E4-TARGET-CE-015 -/

/-- `Number.MAX_SAFE_INTEGER`: `2^53 - 1`. -/
def hostSafeInteger : Nat := 9007199254740991

/-- Whether every number in a value is one the host carries exactly. -/
def valAdmissible : Effects.Trace.Val → Bool
  | .unit | .none | .bool _ | .str _ => true
  | .nat n => n ≤ hostSafeInteger
  | .int i => -(hostSafeInteger : Int) ≤ i && i ≤ (hostSafeInteger : Int)
  | .pair left right => valAdmissible left && valAdmissible right
  | .some value => valAdmissible value

def outcomeAdmissible : Effects.Trace.Outcome Effects.Trace.Val → Bool
  | .success v | .failure v | .defect v => valAdmissible v
  | .interrupted => true

def eventAdmissible : Effect4.Trace.Event → Bool
  | .op _ v | .answer _ v | .failed _ v => valAdmissible v
  | .leave _ o | .finalizer _ o | .done o => outcomeAdmissible o
  | .decide _ _ | .enter _ | .frontier => true

/-- Emit a golden only if the host can carry every number in it. -/
def admitted (name : String) (log : Effect4.Trace.Log) (rendered : String) : IO String :=
  if log.all eventAdmissible then pure rendered
  else throw (IO.userError
    s!"refusing to emit golden {name}: a value leaves the host-exact range (at most {hostSafeInteger})")

effect_signature Cell where
  | get : Nat ⟪ "read the cell", "current value" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell", "store" ⟫

-- The pure atoms of the harness, declared once. `effect_atoms` emits the Lean
-- function, the row (`Atoms.rows`), the flow embedding's table
-- (`Atoms.table`), the wire dispatcher (`Atoms.eval`) and the generated
-- `atoms.ts` (`Atoms.source`), so no atom exists in one face only
-- (`E4-TARGET-CE-025`). A `match` body is parenthesised: its alternatives
-- would otherwise swallow the next atom.
effect_atoms Atoms importing handles [JobQueue] from "./job-queue.ts" where
  | succ (n : Nat) : Nat ⟪ "n + 1" ⟫ := n + 1
  | orZero (e : Except String Nat) : Nat ⟪ "Result.isSuccess(e) ? e.success : 0" ⟫ :=
      (match e with | .ok n => n | .error _ => 0)
  | firstOr (r : Option (Except String Nat)) : Nat
      ⟪ "Option.isSome(r) ? (Result.isSuccess(r.value) ? r.value.success : 0) : 0" ⟫ :=
      (match r with | Option.some (.ok n) => n | _ => 0)
  -- The job runner's counter atom: naturals truncate at zero on the Lean side,
  -- and the flow never calls it at zero.
  | dec (n : Nat) : Nat ⟪ "n - 1" ⟫ := n - 1
  -- The job runner's ticket projection. `Jobs.next` answers a job ticket --
  -- the connection it came from and the job id -- because a flow cannot build
  -- a pair from two block slots (`E4-FLOW-CE-028`); this takes it apart again
  -- for the one-parameter `attempt`.
  | snd (ticket : Handle "JobQueue" × Nat) : Nat ⟪ "ticket[1]" ⟫ := ticket.2
  -- Flow v3 value branches: the drain tests *values*, not tape answers. A
  -- ticket whose job id is 0 means the queue was empty; a positive attempt
  -- budget means the job may be retried.
  | nonEmpty (ticket : Handle "JobQueue" × Nat) : Bool ⟪ "ticket[1] !== 0" ⟫ := ticket.2 != 0
  | positive (n : Nat) : Bool ⟪ "n !== 0" ⟫ := n != 0

effect_program incr (n : Nat) over Cell : Nat :=
  let x ← Cell.get()
  let _ ← Cell.put(succ x)
  let y ← Cell.get()
  return y

-- A second program: two writes, then a read. Exercises the discard rule
-- twice and returns the last write.
effect_program twice (n : Nat) over Cell : Nat :=
  let _ ← Cell.put(n)
  let _ ← Cell.put(succ n)
  let y ← Cell.get()
  return y

-- The data reading of errors: an answer that is an `Except`, spelled
-- `Result.Result<number, string>` on the host (rc.112 has no `Either`). The
-- program recovers from it through a pure atom and continues.
effect_signature ECell where
  | tryGet : Except String Nat ⟪ "try to read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫

effect_program recover (n : Nat) over ECell : Nat :=
  let r ← ECell.tryGet()
  let _ ← ECell.put(n)
  return orZero r

/-- A reader that always fails with a returned error; the write still happens. -/
def ecellLive : ECell.Service (StateT Nat Id) := fun name =>
  match name with
  | .tryGet => fun _ => pure (.error "boom")
  | .put => fun n => set n

example : ((interpret ecellLive.toHandler (recover 5)).run 41 : Nat × Nat) = (0, 5) := rfl

-- The aborting reading of errors: `get` may fail with a `String`; the
-- handler kind is `ExceptT String M`, the host method is `Effect.Effect<number, string>`.
effect_signature FCell where
  | get : Nat !! String ⟪ "read the cell, may fail" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫

effect_program fallible (n : Nat) over FCell : Nat :=
  let _ ← FCell.put(n)
  let x ← FCell.get()
  return x

/-- A reader that aborts; the preceding write still happens and is traced. -/
def fcellLive : FCell.Service (ExceptT String (StateT Nat Id)) := fun name =>
  match name with
  | .get => fun _ => throw "boom"
  | .put => fun n => set n

example : ((interpret fcellLive.toHandler (fallible 5)).run.run 41 : Except String Nat × Nat) =
    (.error "boom", 5) := rfl

-- Depth three at the answer face: a lookup that may be missing (`Option`) and,
-- when present, may be malformed (`Except`). rc.112 has no `Either`, so the
-- answer spells `Option.Option<Result.Result<number, string>>`. This is the
-- shape the M3 note called out as unavailable while Stratum V capped spellings
-- at depth two.
effect_signature Tri where
  | lookup (k : Nat) : Option (Except String Nat) ⟪ "look a key up", "may be missing" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell", "store" ⟫

effect_program probe (n : Nat) over Tri : Nat :=
  let r ← Tri.lookup(n)
  let _ ← Tri.put(n)
  return firstOr r

/-- A store whose lookup misses at key zero and otherwise answers the cell
offset by the key; the write still happens. -/
def triLive : Tri.Service (StateT Nat Id) := fun name =>
  match name with
  | .lookup => fun k => do
      let s ← get
      pure (if k == 0 then Option.none else Option.some (Except.ok (s + k)))
  | .put => fun n => set n

example : ((interpret triLive.toHandler (probe 3)).run 41 : Nat × Nat) = (44, 3) := rfl
example : ((interpret triLive.toHandler (probe 0)).run 41 : Nat × Nat) = (0, 0) := rfl

/-- The Lean handler `tail.ts` mirrors with a `Ref`. -/
def cellLive : Cell.Service (StateT Nat Id) := fun name =>
  match name with
  | .get => fun _ => get
  | .put => fun n => set n

example : ((interpret cellLive.toHandler (incr 0)).run 41 : Nat × Nat) = (42, 42) := rfl
example : ((interpret cellLive.toHandler (twice 7)).run 41 : Nat × Nat) = (8, 8) := rfl

/-- The traced run from the initial cell, with the outcome appended. -/
def goldenLog (program : Program Cell.Sig Nat) (initial : Nat) : Effect4.Trace.Log :=
  let result : (Nat × Effect4.Trace.Log) × Nat :=
    ((interpret (Cell.traced cellLive).toHandler program).run []).run initial
  result.1.2 ++ [.done (.success (.nat result.1.1))]

def egoldenLog (program : Program ECell.Sig Nat) (initial : Nat) : Effect4.Trace.Log :=
  let result : (Nat × Effect4.Trace.Log) × Nat :=
    ((interpret (ECell.traced ecellLive).toHandler program).run []).run initial
  result.1.2 ++ [.done (.success (.nat result.1.1))]

/-- The traced fallible run: the log survives the failure; the outcome is the error. -/
def fgoldenLog (program : Program FCell.Sig Nat) (initial : Nat) : Effect4.Trace.Log :=
  let result : (Except String Nat × Effect4.Trace.Log) × Nat :=
    ((interpret (FCell.tracedExcept fcellLive).toHandler program).run.run []).run initial
  result.1.2 ++ [.done (match result.1.1 with
    | .ok n => .success (.nat n)
    | .error e => .failure (.str e))]

/-- The traced depth-three run: the answer of `lookup` is one wire value,
`{"some":[true, 44]}`, on both faces. -/
def tgoldenLog (program : Program Tri.Sig Nat) (initial : Nat) : Effect4.Trace.Log :=
  let result : (Nat × Effect4.Trace.Log) × Nat :=
    ((interpret (Tri.traced triLive).toHandler program).run []).run initial
  result.1.2 ++ [.done (.success (.nat result.1.1))]

/-- One harness program: its family's rows, its script, and its golden log.
`flowInput` is the parameter value of the Flow-runner golden (the internal
oracle); programs without one have no flow golden. -/
structure Entry where
  name : String
  rows : ServiceRow
  script : Script
  log : Effect4.Trace.Log
  flowInput : Option Effects.Trace.Val := none
  initial : Nat := 41

/-- The programs the harness knows. -/
def programs : List Entry :=
  [ { name := "incr", rows := Cell.rows, script := incr.script, log := goldenLog (incr 0) 41,
      flowInput := some (.nat 0) }
  , { name := "twice", rows := Cell.rows, script := twice.script, log := goldenLog (twice 7) 41,
      flowInput := some (.nat 7) }
  , { name := "recover", rows := ECell.rows, script := recover.script, log := egoldenLog (recover 5) 41 }
  , { name := "fallible", rows := FCell.rows, script := fallible.script, log := fgoldenLog (fallible 5) 41 }
  , { name := "probe", rows := Tri.rows, script := probe.script, log := tgoldenLog (probe 3) 41 } ]

/-! ## The families that moved into the library

`Scopes` (`Effect4/Runtime/ScopeFamily.lean`) and `Deferreds`
(`Effect4/Stateful/DeferredFamily.lean`) used to be declared here. A script is
not a library, so nothing under `Effect4/` could state a theorem about either,
and `Deferreds` was written out a second time in
`Effect4Test/Flow/DeferredsContract.lean` where the two copies could drift.
Both are declared once now, in the library, and this module imports them
(lowering lane L3, plan section 5 decision 3). -/
/-! ## The Flow face: the runner (internal oracle) and the dispatch lowering -/

/-- The atoms the scripts call, with their TypeScript types: the `effect_atoms`
rows, read as the flow embedding reads them. -/
def cellAtoms : AtomTable := Atoms.table

/-- The Cell family by name, over the same state the traced service uses. -/
def cellFamily : String → Effects.Trace.Val → StateT Nat Id Effects.Trace.Val
  | "get", _ => do let n ← get; pure (.nat n)
  | "put", .nat n => do set n; pure .unit
  | _, _ => pure .unit

/-- The same atoms on the wire, from the same rows. -/
def cellAtom : String → Effects.Trace.Val → Effects.Trace.Val := Atoms.eval

/-- One flow program of the harness: its admitted graph, the tapes it is run
with (golden name suffix, tape), its input, and the traced-service log it must
agree with under `m2` when it was embedded from a script. -/
structure FlowEntry where
  program : FlowProgram
  rows : ServiceRow := Cell.rows
  tapes : List (String × Flow.Tape)
  input : Effects.Trace.Val
  initial : Nat := 41
  oracle : Option Effect4.Trace.Log := none
  /-- The script the graph was embedded from, when it was embedded from one.
  Its own denotation (`denoteScript`, packet D5) is the third face of the
  oracle; `Script.toFlow_denote` is why the two Lean faces cannot drift. -/
  script : Option Script := none
  /-- Resource-boundary tapes. A tape named here is run with the given fuel
  instead of `fuelFor`, so the Lean face stops at a `frontier` with tape left
  over, and its golden carries the op budgets whose host `frontier` lands at the
  same row. One budget per yield setting: the budget counts primitives and the
  yield wrapper is itself primitives. -/
  boundaries : List (String × Nat × List (String × Nat)) := []

/-- Embed and admit a script's flow. -/
def embed? (entry : Entry) : Option FlowProgram := do
  let (table, raw) ← Script.toFlow entry.rows cellAtoms entry.script
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow =>
      some { name := entry.name, param := entry.script.param, result := entry.script.result,
             table := table, flow := flow }
  | .error _ => none

/-- Admit a hand-built graph over a table. -/
def admit? (name : String) (table : List OpSpec) (raw : RawFlow String) : Option FlowProgram :=
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .ok flow => some { name := name, param := ("n", raw.inputTy), result := raw.resultTy,
                       table := table, flow := flow }
  | .error _ => none

/-- `choose` at site 7 between two returns of the input. -/
def chooserRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨7⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .ret ⟨0⟩ }
      , { id := ⟨2⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

/-- A literal 1 beside the input, then a chosen self-loop that swaps the two
parameters on every left decision and returns the first on the right. -/
def swapTable : List OpSpec :=
  [{ name := "lit", kind := .lit (.nat 1), requestTy := "number", answerTy := "number" }]

def swapRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .perform ⟨0⟩ ⟨0⟩ ⟨1⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number", "number"], term := .choose ⟨1⟩ ⟨1⟩ ⟨2⟩ [⟨1⟩, ⟨0⟩] }
      , { id := ⟨2⟩, params := ["number", "number"], term := .ret ⟨0⟩ } ] }

def decision (site : Nat) (branch : Bool) : Flow.Decision := ⟨⟨site⟩, branch⟩

/-- A cycle entered at two blocks: every cycle passes a `choose`, so it is
admitted, but the graph is not reducible and keeps the dispatch form. -/
def irreducibleRaw : RawFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    blocks :=
      [ { id := ⟨0⟩, params := ["number"], term := .choose ⟨0⟩ ⟨1⟩ ⟨2⟩ [⟨0⟩] }
      , { id := ⟨1⟩, params := ["number"], term := .choose ⟨1⟩ ⟨2⟩ ⟨3⟩ [⟨0⟩] }
      , { id := ⟨2⟩, params := ["number"], term := .choose ⟨2⟩ ⟨1⟩ ⟨3⟩ [⟨0⟩] }
      , { id := ⟨3⟩, params := ["number"], term := .ret ⟨0⟩ } ] }

/-- The flow programs of the harness. -/
def flowEntries : List FlowEntry :=
  (programs.filterMap fun entry =>
    match entry.flowInput, embed? entry with
    | some input, some program =>
        some { program := program, rows := entry.rows, tapes := [("empty", [])], input := input,
               initial := entry.initial, oracle := some entry.log, script := some entry.script }
    | _, _ => none) ++
  ((admit? "chooser" [] chooserRaw).toList.map fun program =>
    { program := program, tapes := [("left", [decision 7 true]), ("right", [decision 7 false])],
      input := .nat 5 }) ++
  ((admit? "swap" swapTable swapRaw).toList.map fun program =>
    { program := program,
      tapes := [("once", [decision 1 true, decision 1 false]),
                ("twice", [decision 1 true, decision 1 true, decision 1 false]),
                -- The budget tape: thirteen answers, of which the run reaches
                -- four before its resource runs out on either face.
                ("budget", (List.replicate 12 (decision 1 true)) ++ [decision 1 false])],
      -- Fuel 5: one block-0 visit plus four `choose` visits, then the frontier.
      -- The host budgets were measured against rc.112 on the pinned install and
      -- are exact: 19 primitives at the default yield setting, 79 at the rc.112
      -- floor of 3, both giving the same four `decide` rows and one `frontier`.
      boundaries := [("budget", 5, [("default", 19), ("yield3", 79)])],
      input := .nat 5 }) ++
  ((admit? "irreducible" [] irreducibleRaw).toList.map fun program =>
    { program := program,
      tapes := [("left", [decision 0 true, decision 1 true, decision 2 false]),
                ("right", [decision 0 false, decision 2 true, decision 1 false])],
      input := .nat 5 })

/-- Run a flow entry on one tape; the log the runner wrote. With no fuel given
the run is expected to finish; with fuel given it is expected to stop at a fuel
frontier, which is one `frontier` row and no outcome. -/
def flowLogWith (entry : FlowEntry) (tape : Flow.Tape) (fuel? : Option Nat) :
    Except String Effect4.Trace.Log :=
  let table := entry.program.table
  let fuel := fuel?.getD (Flow.fuelFor entry.program.flow.erase tape)
  let result : (Flow.RunResult × Effect4.Trace.Log) × Nat :=
    ((Flow.run fuel entry.program.flow (tableService ⟨0⟩ table cellFamily cellAtom)
      (tableNameOf ⟨0⟩ table) tape entry.input).run []).run entry.initial
  match fuel?, result.1.1 with
  | none, .done _ => pure result.1.2
  | some _, .frontier (.fuel _) => pure result.1.2
  | _, other => throw s!"the flow run of {entry.program.name} did not finish: {repr other}"

def flowLog (entry : FlowEntry) (tape : Flow.Tape) : Except String Effect4.Trace.Log :=
  flowLogWith entry tape none

/-- The third face of the internal oracle: the script's own denotation
(`Effect4/Target/TypeScript/ScriptDenotation.lean`, packet D5), interpreted
under the same table service that the runner uses. `Script.toFlow_denote` makes
its agreement with the flow-runner face a theorem rather than an observation;
the arm prints it anyway, so a change to either face shows up here. -/
def denotationLog (entry : FlowEntry) (script : Script) : Except String Effect4.Trace.Log :=
  let table := entry.program.table
  match denoteScript ⟨0⟩ entry.rows cellAtoms table script entry.input with
  | none => throw s!"the script of {entry.program.name} has no denotation"
  | some program =>
    let traced := Flow.tracedFlowService (tableService ⟨0⟩ table cellFamily cellAtom)
      (tableNameOf ⟨0⟩ table)
    let result : (Effects.Trace.Val × Effect4.Trace.Log) × Nat :=
      ((interpret (Effects.Family.Service.toHandler traced) program).run []).run entry.initial
    pure (result.1.2 ++ [.done (.success result.1.1)])

/-! ## Regions (P-T7): a family with resources and failures -/

effect_signature RCell where
  | get : Nat ⟪ "read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫
  | acquire (n : Nat) : Nat ⟪ "acquire a resource named by a number" ⟫
  | release (n : Nat) : Unit ⟪ "release a resource" ⟫
  | boom (n : Nat) : Nat !! String ⟪ "fail with a string" ⟫
  | releaseBoom (n : Nat) : Unit !! String ⟪ "a release that fails" ⟫

/-- `RCell` by name: resources are their numbers, `boom` and `releaseBoom` fail. -/
def rcellFamily : String → Effects.Trace.Val → StateT Nat Id (Except Effects.Trace.Val Effects.Trace.Val)
  | "get", _ => do let n ← get; pure (.ok (.nat n))
  | "put", .nat n => do set n; pure (.ok .unit)
  | "acquire", v => pure (.ok v)
  | "release", _ => pure (.ok .unit)
  | "boom", _ => pure (.error (.str "boom"))
  | "releaseBoom", _ => pure (.error (.str "boom"))
  | _, _ => pure (.ok .unit)

def rcellTable : List OpSpec := familyTable RCell.rows

/-- Operation positions in `rcellTable`. -/
def opAcquire : OperationId := ⟨2⟩
def opRelease : OperationId := ⟨3⟩
def opBoom : OperationId := ⟨4⟩
def opReleaseBoom : OperationId := ⟨5⟩

def rblock (id : Nat) (region : Option Nat) (params : List String) (term : RegionTerm) : RegionBlock String :=
  { id := ⟨id⟩, region := region.map RegionId.mk, params := params, term := term }

def rregion (id : Nat) (parent : Option Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := parent.map RegionId.mk, continue_ := ⟨continue_⟩, resultTy := "number" }

def regionFlow (regions : List (RegionRow String)) (blocks : List (RegionBlock String)) : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := regions, blocks := blocks }

def vars (n : Nat) : List Var := (List.range n).map Var.mk

/-- Two nested regions, each acquiring a resource, the inner body failing:
both close with the failure, innermost first. -/
def regionNested : RegionFlow String := regionFlow [rregion 1 none 7, rregion 2 (some 1) 6]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.enter ⟨2⟩ ⟨3⟩ (vars 2))
  , rblock 3 (some 2) ["number", "number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨4⟩ (vars 2))
  , rblock 4 (some 2) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨5⟩ (vars 3)))
  , rblock 5 (some 2) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 6 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 7 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- Two resources in one region, then a failing body: releases run latest
first with the failure. -/
def regionTwoFail : RegionFlow String := regionFlow [rregion 1 none 5]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.acquire opAcquire ⟨1⟩ opRelease ⟨3⟩ (vars 2))
  , rblock 3 (some 1) ["number", "number", "number"] (.plain (.perform opBoom ⟨0⟩ ⟨4⟩ (vars 3)))
  , rblock 4 (some 1) ["number", "number", "number", "number"] (.leave ⟨3⟩)
  , rblock 5 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- Two resources whose second release fails. The runner models it
(`Effect4Test/Flow/RegionRunnerContract.lean`), but `Effect.acquireRelease`
types a release `Effect<unknown, never, R>`, so the lowering refuses it and
it has no host golden (E4-TARGET-CE-012). -/
def regionReleaseFails : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.acquire opAcquire ⟨1⟩ opReleaseBoom ⟨3⟩ (vars 2))
  , rblock 3 (some 1) ["number", "number", "number"] (.leave ⟨2⟩)
  , rblock 4 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- One resource, a clean leave: the release sees success and the run succeeds. -/
def regionBothSucceed : RegionFlow String := regionFlow [rregion 1 none 3]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.leave ⟨1⟩)
  , rblock 3 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-! ## Interruption as decisions (M2)

Three region flows whose lowering declares interrupt points. The tape in each
golden's `tape` header is the *interrupt* tape (`Effect4.Flow.interruptRead`),
not a choice tape: none of these flows chooses, and the interrupt site space is
disjoint from every `choose` site (`Effect4.Flow.Point.site_ne_choose`). -/

/-- Position of `put` in `rcellTable`: a `number` request answering `void`. -/
def opPut : OperationId := ⟨1⟩

/-- Unmasked delivery: one region, a `perform` inside it, the interrupt
delivered at that point. The region closes with `interrupted` and the run ends
`done interrupted`; there is no resource, so no finalizer runs. -/
def interruptUnmasked : RegionFlow String := regionFlow [rregion 1 none 3]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.plain (.perform opPut ⟨0⟩ ⟨2⟩ (vars 1)))
  , rblock 2 (some 1) ["number", "void"] (.leave ⟨0⟩)
  , rblock 3 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- Masked deferral, then delivery at the first unmasked point. Region 1 is
uninterruptible: the tape delivers at the `perform` inside it, the runner keeps
the interrupt pending across that point and across the region's own `leave`
(both masked), the region closes cleanly with `success`, and the `perform` after
it — outside every region — delivers. -/
def interruptMasked : RegionFlow String := regionFlow [rregion 1 none 4]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.plain (.perform opPut ⟨0⟩ ⟨3⟩ (vars 2)))
  , rblock 3 (some 1) ["number", "number", "void"] (.leave ⟨1⟩)
  , rblock 4 none ["number"] (.plain (.perform opPut ⟨0⟩ ⟨5⟩ (vars 1)))
  , rblock 5 none ["number", "void"] (.plain (.ret ⟨0⟩)) ]

/-- A finalizer observing `interrupted`: two nested regions, each holding a
resource, the interrupt delivered at a `perform` in the inner body. Both
regions close innermost-first with `interrupted`, and each release runs with
that closing exit — the `finalizer r {"interrupted":true}` rows. -/
def interruptFinalizer : RegionFlow String := regionFlow [rregion 1 none 7, rregion 2 (some 1) 6]
  [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
  , rblock 1 (some 1) ["number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨2⟩ (vars 1))
  , rblock 2 (some 1) ["number", "number"] (.enter ⟨2⟩ ⟨3⟩ (vars 2))
  , rblock 3 (some 2) ["number", "number"] (.acquire opAcquire ⟨0⟩ opRelease ⟨4⟩ (vars 2))
  , rblock 4 (some 2) ["number", "number", "number"] (.plain (.perform opPut ⟨0⟩ ⟨5⟩ (vars 3)))
  , rblock 5 (some 2) ["number", "number", "number", "void"] (.leave ⟨1⟩)
  , rblock 6 (some 1) ["number"] (.leave ⟨0⟩)
  , rblock 7 none ["number"] (.plain (.ret ⟨0⟩)) ]

/-- One interrupt tape entry, at the point before the `perform` of a block. -/
def deliverAtPerform (block : Nat) : Flow.Decision :=
  ⟨(Effect4.Flow.Point.perform ⟨block⟩).site, true⟩

structure RegionEntry where
  program : RegionProgram
  input : Effects.Trace.Val := .nat 5
  initial : Nat := 41

def admitRegion? (name : String) (raw : RegionFlow String) : Option RegionProgram :=
  match admitRegions (tableAlphabet ⟨0⟩ rcellTable) raw with
  | .ok flow => some { name := name, param := ("n", "number"), result := "number",
                       table := rcellTable, flow := flow }
  | .error _ => none

def regionEntries : List RegionEntry :=
  [ ("regionNested", regionNested), ("regionTwoFail", regionTwoFail),
    ("regionBothSucceed", regionBothSucceed) ].filterMap
    fun (name, raw) => (admitRegion? name raw).map fun program => { program := program }

/-- The runner's log of a region program; `failed` is a finished run too. -/
def regionLog (entry : RegionEntry) : Except String Effect4.Trace.Log :=
  let table := entry.program.table
  let result : ((Flow.RunResult × Flow.Tape) × Effect4.Trace.Log) × Nat :=
    ((Flow.runRegionsDefault entry.program.flow (Flow.tableRegionService ⟨0⟩ table rcellFamily cellAtom)
      (tableNameOf ⟨0⟩ table) [] entry.input).run []).run entry.initial
  match result.1.1.1 with
  | .done _ => pure result.1.2
  | .failed _ => pure result.1.2
  | other => throw s!"the region run of {entry.program.name} did not finish: {repr other}"

/-- The Lean-face run of a region program at one fuel: the result and the log. -/
def regionRunAt (entry : RegionEntry) (fuel : Nat) : Flow.RunResult × Effect4.Trace.Log :=
  let table := entry.program.table
  let result : ((Flow.RunResult × Flow.Tape) × Effect4.Trace.Log) × Nat :=
    ((Flow.runRegions fuel entry.program.flow
      (Flow.tableRegionService ⟨0⟩ table rcellFamily cellAtom)
      (tableNameOf ⟨0⟩ table) [] entry.input).run []).run entry.initial
  (result.1.1.1, result.1.2)

/-- The DB-04 frontier golden of a region program: the run at one fuel below
the least fuel that finishes. Its log is the region rows already written,
punctuated by the `frontier` marker -- and nothing else: fuel exhaustion is a
live frontier, never a failure and never a refusal, and it leaves the merged
failure list untouched (`Effect4/Semantics/Approximation.lean`,
`regionLoop_frontier_live`). The region counterpart of the `swap.budget`
golden. `regionFuelFor` bounds the search, and
`Effect4.Flow.runRegions_fuelFor_finishes` is why that bound is enough. -/
def regionFrontierLog (entry : RegionEntry) : Except String Effect4.Trace.Log :=
  let bound := Flow.regionFuelFor entry.program.flow.flow []
  match (List.range (bound + 1)).find? fun fuel => !(regionRunAt entry fuel).1.exhausted with
  | none => throw s!"the region run of {entry.program.name} does not finish below fuel {bound}"
  | some 0 => throw s!"the region run of {entry.program.name} finishes at zero fuel"
  | some (settles + 1) =>
      let out := regionRunAt entry settles
      if out.1.exhausted then pure out.2
      else throw s!"the region run of {entry.program.name} did not stop at a fuel frontier"
/-- One interrupt program of the harness: its admitted graph (with interrupt
points declared and its masked regions named) and the interrupt tape it runs
with. -/
structure InterruptEntry where
  program : RegionProgram
  itape : Flow.Tape
  input : Effects.Trace.Val := .nat 5
  initial : Nat := 41

def admitInterrupt? (name : String) (raw : RegionFlow String) (masked : List RegionId) :
    Option RegionProgram :=
  match admitRegions (tableAlphabet ⟨0⟩ rcellTable) raw with
  | .ok flow => some { name := name, param := ("n", "number"), result := "number",
                       table := rcellTable, flow := flow, interrupts := true, masked := masked }
  | .error _ => none

def interruptEntries : List InterruptEntry :=
  [ ("interruptUnmasked", interruptUnmasked, ([] : List RegionId), [deliverAtPerform 1])
  , ("interruptMasked", interruptMasked, [⟨1⟩], [deliverAtPerform 2])
  , ("interruptFinalizer", interruptFinalizer, ([] : List RegionId), [deliverAtPerform 4])
  ].filterMap fun (name, raw, masked, itape) =>
    (admitInterrupt? name raw masked).map fun program =>
      { program := program, itape := itape }

/-- The runner's log of an interrupt program; an interrupted run is finished. -/
def interruptLog (entry : InterruptEntry) : Except String Effect4.Trace.Log :=
  let table := entry.program.table
  let result : ((Flow.InterruptResult × Flow.Tape) × Effect4.Trace.Log) × Nat :=
    ((Flow.runInterruptsDefault entry.program.flow entry.program.masked
      (Flow.tableRegionService ⟨0⟩ table rcellFamily cellAtom)
      (tableNameOf ⟨0⟩ table) [] entry.itape entry.input).run []).run entry.initial
  match result.1.1.1 with
  | .done _ => pure result.1.2
  | .failed _ => pure result.1.2
  | .interrupted => pure result.1.2
  | other => throw s!"the interrupt run of {entry.program.name} did not finish: {repr other}"

/-! ## `Jobs` (packet: the first real program): a resource-managed job runner

The first harness program written the way an Effect user would write one: open
a connection to a job queue inside a region, drain the queue, and let the
region's release close the connection on *every* exit — the clean one, the
failing one and the interrupted one.

Refusals and workarounds this family and its flow record, each with a register
row (`docs/research/2026-09-03-job-runner.md` carries the full account):

- **A flow cannot build a pair.** `plan` hands a service exactly one `Val`, so
  a request is one block slot and no term of the flow language pairs two of
  them. A two-parameter operation is therefore performed from a slot that
  already holds the tuple, which means the tuple has to *arrive* as an answer:
  `next` answers a job ticket, the connection and the job id, and `run`, `ack`
  and `requeue` take that ticket as their two-parameter request. The `snd`
  atom takes it apart for the one-parameter `attempt`.
  counterexample: E4-FLOW-CE-028
- **A flow has no failure handler.** An aborting operation ends the run
  (`Effect4.Flow.regionLoop`'s `fail`), so "on failure, retry or requeue" is
  not expressible over `run`. `attempt` is the same job in the *data* reading
  of its error (`Except String Nat`, rc.112 `Result`), which the run survives;
  `run` is kept and exercised by `jobPoison`, whose whole point is that the
  abort closes the region and the release still runs.
  counterexample: E4-FLOW-CE-026
- **A flow does not branch on data.** `choose` reads the decision tape, so the
  queue-empty test and the retry/requeue decision are tape questions, not
  tests of `next`'s answer or of the carried attempt budget. The budget is a
  real block parameter, decremented by the `dec` atom on every retry, and the
  flow cannot compare it with zero. counterexample: E4-FLOW-CE-027
- **The interrupt tape addresses occurrences, not jobs.** The packet's third
  predicted gap is half refuted: `Effect4.Flow.interruptRead` consumes the head
  only when it names the site, so entries at one site are read in the order the
  run reaches that site and a non-delivering entry moves delivery to the next
  occurrence -- which is how `jobRunner.interrupt` interrupts the *second* job.
  What stays true is that a tape names a control point, never the job the run
  is holding there. No register row: nothing refuses what it claims to do.
-/

effect_signature Jobs where
  | connect : Handle "JobQueue" ⟪ "open a connection to the job queue", "the connection" ⟫
  | next (conn : Handle "JobQueue") : Handle "JobQueue" × Nat
      ⟪ "dequeue the next job", "a ticket: the connection and the job id, 0 when empty" ⟫
  | run (conn : Handle "JobQueue") (job : Nat) : Nat !! String
      ⟪ "run a job on its connection", "aborts with the job's error" ⟫
  | attempt (job : Nat) : Except String Nat
      ⟪ "run a job, reporting its error as data", "the flow has no failure handler" ⟫
  | ack (conn : Handle "JobQueue") (job : Nat) : Unit
      ⟪ "acknowledge a finished job on its connection" ⟫
  | requeue (conn : Handle "JobQueue") (job : Nat) : Unit
      ⟪ "put a job back at the end of its connection's queue" ⟫
  | disconnect (conn : Handle "JobQueue") : Unit ⟪ "close the connection" ⟫

/-- The queue state the Lean handler keeps: the jobs still to run, the jobs
acknowledged in acknowledgement order, the jobs put back, and how many more
times each job is scheduled to fail. The host keeps the same four fields in a
JSON file (`harness/trace/job-queue.ts`); the golden is the join. -/
structure Queue where
  pending : List Nat
  acked : List Nat
  requeued : List Nat
  /-- job id, remaining scheduled failures -/
  failures : List (Nat × Nat)
deriving Repr, Inhabited

namespace Queue

def failuresLeft (queue : Queue) (job : Nat) : Nat :=
  match queue.failures.find? (·.1 == job) with
  | some entry => entry.2
  | none => 0

def consumeFailure (queue : Queue) (job : Nat) : Queue :=
  { queue with failures := queue.failures.map fun entry =>
      if entry.1 == job then (entry.1, entry.2 - 1) else entry }

def seed (pending : List Nat) (failures : List (Nat × Nat) := []) : Queue :=
  { pending := pending, acked := [], requeued := [], failures := failures }

end Queue

/-- The message a failed job reports. Both faces build it the same way. -/
def jobError (job : Nat) : String := "job " ++ toString job ++ " failed"

/-- `Jobs` by name over the queue state. `run` aborts; `attempt` is the same
job with its error in the answer. `connect` answers handle 0 — one connection
per run, and the host's first-seen handle index is the same 0. `next` answers
the ticket `(conn, job)`, and the three two-parameter operations receive that
ticket as one `Val.pair`: exactly what `wireArgs` builds from a two-argument
host call. -/
def jobsFamily : String → Effects.Trace.Val →
    StateT Queue Id (Except Effects.Trace.Val Effects.Trace.Val)
  | "connect", _ => pure (.ok (.nat 0))
  | "next", conn => do
      let queue ← get
      match queue.pending with
      | [] => pure (.ok (.pair conn (.nat 0)))
      | job :: rest => do
          set { queue with pending := rest }
          pure (.ok (.pair conn (.nat job)))
  | "run", .pair _ (.nat job) => do
      let queue ← get
      if queue.failuresLeft job == 0 then pure (.ok (.nat job))
      else do
        set (queue.consumeFailure job)
        pure (.error (.str (jobError job)))
  | "attempt", .nat job => do
      let queue ← get
      if queue.failuresLeft job == 0 then
        pure (.ok (.pair (.bool true) (.nat job)))
      else do
        set (queue.consumeFailure job)
        pure (.ok (.pair (.bool false) (.str (jobError job))))
  | "ack", .pair _ (.nat job) => do
      modify fun queue => { queue with acked := queue.acked ++ [job] }
      pure (.ok .unit)
  | "requeue", .pair _ (.nat job) => do
      modify fun queue =>
        { queue with pending := queue.pending ++ [job], requeued := queue.requeued ++ [job] }
      pure (.ok .unit)
  | "disconnect", _ => pure (.ok .unit)
  | _, _ => pure (.ok .unit)

/-- The pure atoms the job flow calls; their host bodies are in `atoms.ts`,
from the same `effect_atoms Atoms` rows (`E4-TARGET-CE-025`). -/
def jobAtom : String → Effects.Trace.Val → Effects.Trace.Val
  | "succ", .nat n => .nat (n + 1)
  | "dec", .nat n => .nat (n - 1)
  | "snd", .pair _ (.nat job) => .nat job
  | "nonEmpty", .pair _ (.nat job) => .bool (job != 0)
  | "positive", .nat n => .bool (n != 0)
  | _, _ => .unit

/-- The TypeScript spelling of a connection handle, as `Handle "JobQueue"`
answers it. -/
def jobHandleTy : String := "JobQueue"

/-- The TypeScript spelling of a job ticket: what `next` answers and what the
three two-parameter operations take as their request. Both readings are the
same right-nested product, which is why one slot serves both. -/
def jobTicketTy : String := "readonly [" ++ jobHandleTy ++ ", number]"

/-- The job alphabet: the family's seven operations, then the pure rows the
graph needs — a unit literal (the nullary `connect` still takes a request slot
of its own type), a zero literal (the initial acknowledged count), the two
counter atoms and the ticket projection. -/
def jobsTable : List OpSpec := familyTable Jobs.rows ++
  [ { name := "unit", kind := .lit .unit, requestTy := "number", answerTy := "void" }
  , { name := "zero", kind := .lit (.nat 0), requestTy := "number", answerTy := "number" }
  , { name := "succ", kind := .atom, requestTy := "number", answerTy := "number" }
  , { name := "dec", kind := .atom, requestTy := "number", answerTy := "number" }
  , { name := "snd", kind := .atom, requestTy := jobTicketTy, answerTy := "number" }
  , { name := "nonEmpty", kind := .atom, requestTy := jobTicketTy, answerTy := "boolean" }
  , { name := "positive", kind := .atom, requestTy := "number", answerTy := "boolean" } ]

def opConnect : OperationId := ⟨0⟩
def opNext : OperationId := ⟨1⟩
def opRun : OperationId := ⟨2⟩
def opAttempt : OperationId := ⟨3⟩
def opAck : OperationId := ⟨4⟩
def opRequeue : OperationId := ⟨5⟩
def opDisconnect : OperationId := ⟨6⟩
def opUnit : OperationId := ⟨7⟩
def opZero : OperationId := ⟨8⟩
def opSucc : OperationId := ⟨9⟩
def opDec : OperationId := ⟨10⟩
def opSnd : OperationId := ⟨11⟩
def opNonEmpty : OperationId := ⟨12⟩
def opPositive : OperationId := ⟨13⟩

/-- The TypeScript spelling of `attempt`'s answer. -/
def jobResultTy : String := "Result.Result<number, string>"

def jregion (id : Nat) (parent : Option Nat) (continue_ : Nat) : RegionRow String :=
  { id := ⟨id⟩, parent := parent.map RegionId.mk, continue_ := ⟨continue_⟩, resultTy := "number" }

/-- The job runner, as a Flow v3 region flow.

```
b0   enter region 1
b1     a void request slot for the nullary connect
b2     acquire connect, release disconnect
b3     acked := 0
b4   loop: ticket := next(conn)                    <- (conn, job)
b5     more := nonEmpty(ticket)
b6     branch 1 on more:
b7       false -> leave region 1 with acked
b8       true  -> run(ticket) caught:
b10               ok    -> ack(ticket[0], ticket[1])
b11                        acked := acked + 1, back to b4
b12               error -> left := positive(attempts)
b9                         branch 3 on left:
b13                          true  -> attempts := attempts - 1
b15                                   back to b8, same ticket
b14                          false -> requeue(ticket[0], ticket[1])
b16                                   back to b4
b17  return acked
```

Flow v3 (`test/contracts/flow-v3.contract.md`) is what makes this the program
the packet wanted: `run` aborts, and the drain catches it on the failure edge
of `performCatch` (`E4-FLOW-CE-026`, repaired); the queue-empty test and the
retry bound are `branch`es on values the atoms compute (`E4-FLOW-CE-027`,
repaired). Both branches are still decision *sites*: the tape answers them and
the runner refuses a run where the tape and the value disagree, which is what
keeps every cycle tape-bounded and the denotation fuel-free.

The ticket is the multi-argument packet's two-parameter request: `next` hands
it out, and `run`, `ack` and `requeue` destructure it at the call
(`E4-FLOW-CE-028`, `Lowering.tupleArgs`).

The interrupt point before every `perform` (a caught one included) and at the
region's `leave` is declared by the lowering (`RegionProgram.interrupts`), not
by the graph: an interrupt delivered anywhere in the drain closes region 1, and
the release — `disconnect` — runs on that path too. -/
def jobRunnerFlow : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := [jregion 1 none 17],
    blocks :=
      [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
      , rblock 1 (some 1) ["number"] (.plain (.perform opUnit ⟨0⟩ ⟨2⟩ (vars 1)))
      , rblock 2 (some 1) ["number", "void"] (.acquire opConnect ⟨1⟩ opDisconnect ⟨3⟩ (vars 1))
      , rblock 3 (some 1) ["number", jobHandleTy] (.plain (.perform opZero ⟨0⟩ ⟨4⟩ [⟨1⟩, ⟨0⟩]))
      , rblock 4 (some 1) [jobHandleTy, "number", "number"]
          (.plain (.perform opNext ⟨0⟩ ⟨5⟩ (vars 3)))
      , rblock 5 (some 1) [jobHandleTy, "number", "number", jobTicketTy]
          (.plain (.perform opNonEmpty ⟨3⟩ ⟨6⟩ (vars 4)))
      , rblock 6 (some 1) [jobHandleTy, "number", "number", jobTicketTy, "boolean"]
          (.plain (.branch ⟨4⟩ ⟨1⟩ ⟨8⟩ ⟨7⟩ (vars 4)))
      , rblock 7 (some 1) [jobHandleTy, "number", "number", jobTicketTy] (.leave ⟨2⟩)
      , rblock 8 (some 1) [jobHandleTy, "number", "number", jobTicketTy]
          (.plain (.performCatch opRun ⟨3⟩ ⟨10⟩ (vars 4) ⟨12⟩ (vars 4)))
      , rblock 9 (some 1) [jobHandleTy, "number", "number", jobTicketTy, "boolean"]
          (.plain (.branch ⟨4⟩ ⟨3⟩ ⟨13⟩ ⟨14⟩ (vars 4)))
      , rblock 10 (some 1) [jobHandleTy, "number", "number", jobTicketTy, "number"]
          (.plain (.perform opAck ⟨3⟩ ⟨11⟩ (vars 3)))
      , rblock 11 (some 1) [jobHandleTy, "number", "number", "void"]
          (.plain (.perform opSucc ⟨2⟩ ⟨4⟩ (vars 2)))
      , rblock 12 (some 1) [jobHandleTy, "number", "number", jobTicketTy, "string"]
          (.plain (.perform opPositive ⟨1⟩ ⟨9⟩ (vars 4)))
      , rblock 13 (some 1) [jobHandleTy, "number", "number", jobTicketTy]
          (.plain (.perform opDec ⟨1⟩ ⟨15⟩ [⟨0⟩, ⟨2⟩, ⟨3⟩]))
      , rblock 14 (some 1) [jobHandleTy, "number", "number", jobTicketTy]
          (.plain (.perform opRequeue ⟨3⟩ ⟨16⟩ (vars 3)))
      , rblock 15 (some 1) [jobHandleTy, "number", jobTicketTy, "number"]
          (.plain (.jump ⟨8⟩ [⟨0⟩, ⟨3⟩, ⟨1⟩, ⟨2⟩]))
      , rblock 16 (some 1) [jobHandleTy, "number", "number", "void"]
          (.plain (.jump ⟨4⟩ (vars 3)))
      , rblock 17 none ["number"] (.plain (.ret ⟨0⟩)) ] }

/-- The packet's aborting `run`, which the drain cannot use: one job, taken
from the queue and run *on its connection*; its abort closes region 1 with the
failure, the release still runs, and the run ends `failed`. This is the
shortest program over the packet's two-parameter `run`: `next` answers the
ticket and `run` is performed with it, whole. -/
def jobPoisonFlow : RegionFlow String :=
  { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
    regions := [jregion 1 none 6],
    blocks :=
      [ rblock 0 none ["number"] (.enter ⟨1⟩ ⟨1⟩ (vars 1))
      , rblock 1 (some 1) ["number"] (.plain (.perform opUnit ⟨0⟩ ⟨2⟩ (vars 1)))
      , rblock 2 (some 1) ["number", "void"] (.acquire opConnect ⟨1⟩ opDisconnect ⟨3⟩ (vars 1))
      , rblock 3 (some 1) ["number", jobHandleTy] (.plain (.perform opNext ⟨1⟩ ⟨4⟩ []))
      , rblock 4 (some 1) [jobTicketTy] (.plain (.perform opRun ⟨0⟩ ⟨5⟩ []))
      , rblock 5 (some 1) ["number"] (.leave ⟨0⟩)
      , rblock 6 none ["number"] (.plain (.ret ⟨0⟩)) ] }

def admitJob? (name : String) (raw : RegionFlow String) (interrupts : Bool)
    (masked : List RegionId) : Option RegionProgram :=
  match admitRegions (tableAlphabet ⟨0⟩ jobsTable) raw with
  | .ok flow => some { name := name, param := ("n", "number"), result := "number",
                       table := jobsTable, flow := flow, interrupts := interrupts,
                       masked := masked }
  | .error _ => none

/-- The three lowered job programs: the drain, the drain whose whole region is
a masked critical section, and the poison job. -/
def jobPrograms : List RegionProgram :=
  ([ ("jobRunner", jobRunnerFlow, true, ([] : List RegionId))
   , ("jobRunnerMasked", jobRunnerFlow, true, [⟨1⟩])
   , ("jobPoison", jobPoisonFlow, false, ([] : List RegionId))
   ] : List (String × RegionFlow String × Bool × List RegionId)).filterMap
    fun entry => admitJob? entry.1 entry.2.1 entry.2.2.1 entry.2.2.2

/-- One job golden: the program it runs, the two tapes it runs with (the
choice tape answers `choose`, the interrupt tape answers the interrupt points;
the site spaces are disjoint by `Effect4.Flow.sitesSeparated`), the queue it
starts from and the attempt budget it is called with. -/
structure JobEntry where
  program : RegionProgram
  golden : String
  tape : Flow.Tape := []
  itape : Flow.Tape := []
  queue : Queue
  input : Effects.Trace.Val := .nat 2

def jobProgram? (name : String) : Option RegionProgram := jobPrograms.find? (·.name == name)

/-- Decide `site` this way. -/
def choice (site : Nat) (branch : Bool) : Flow.Decision := ⟨⟨site⟩, branch⟩

/-- The interrupt point before the `perform` of a block. -/
def jobPerformPoint (block : Nat) : Nat := (Effect4.Flow.Point.perform ⟨block⟩).site.value

/-- The interrupt point at a region's `leave`. -/
def jobLeavePoint (region : Nat) : Nat := (Effect4.Flow.Point.leave ⟨region⟩).site.value

/-- Sites 1 and 3 are the two value branches of the drain: another job? and
may it be retried? Their tape entries must agree with the values the atoms
compute, or the runner refuses the run. Whether a job succeeded is no longer a
question: the caught `run` takes its value or its failure edge. -/
def more (b : Bool) : Flow.Decision := choice 1 b

def retried (b : Bool) : Flow.Decision := choice 3 b

/-- The five goldens of the packet, plus the poison job that exercises the
packet's aborting `run`. The queue seeds are the ones `harness/trace/job-tail.ts`
writes into its JSON file; the golden is the join of the two faces. -/
def jobEntries : List JobEntry :=
  (jobProgram? "jobRunner").toList.flatMap (fun program =>
    [ -- Three jobs, each acked; then the queue is empty and the region closes.
      { program := program, golden := "clean",
        tape := [more true, more true, more true, more false],
        queue := Queue.seed [1, 2, 3] : JobEntry }
      -- Job 2 fails once: `run`'s failure edge asks whether a retry is left
      -- (the budget is 2), the retry succeeds, and the budget dropped to 1.
    , { program := program, golden := "retry",
        tape := [more true, more true, retried true, more false],
        queue := Queue.seed [1, 2] [(2, 1)] }
      -- Job 2 fails three times against a budget of 2: two retries, then the
      -- exhausted budget puts the job back on the queue; the drain takes it
      -- again, it succeeds, and the region closes with one job acked.
    , { program := program, golden := "requeue",
        tape := [more true, retried true, retried true, retried false, more true, more false],
        queue := Queue.seed [2] [(2, 3)] }
      -- Interrupted mid-queue: job 1 is acked, and the interrupt is delivered
      -- at the point before the *second* job's `attempt`. The tape reaches that
      -- occurrence by spending a non-delivering entry at the same site on the
      -- first visit: `interruptRead` consumes the head only when it names the
      -- site, so entries at one site are read in occurrence order. This is the
      -- packet's predicted gap "the interrupt tape is per program not per job",
      -- refuted for occurrences and confirmed for data: a tape addresses
      -- control points, never the job id at that point.
    , { program := program, golden := "interrupt",
        tape := [more true, more true],
        itape := [⟨⟨jobPerformPoint 8⟩, false⟩, ⟨⟨jobPerformPoint 8⟩, true⟩],
        queue := Queue.seed [1, 2, 3] }
    ]) ++
  (jobProgram? "jobRunnerMasked").toList.map (fun program =>
    -- The whole drain is a masked critical section. The interrupt requested at
    -- the second job's `attempt` point defers; the region's own `leave` point
    -- is masked too, so the region closes cleanly with the jobs acked so far,
    -- `disconnect` runs with that success exit, and the pending interrupt is
    -- delivered at the restoration (the M2 repair).
    { program := program, golden := "masked",
      tape := [more true, more true, more false],
      itape := [⟨⟨jobPerformPoint 8⟩, false⟩, ⟨⟨jobPerformPoint 8⟩, true⟩],
      queue := Queue.seed [1, 2] : JobEntry }) ++
  (jobProgram? "jobPoison").toList.map (fun program =>
    { program := program, golden := "poison", queue := Queue.seed [7] [(7, 1)] : JobEntry })

/-- The runner's log of one job golden. A program that declares interrupt
points runs through `runInterrupts`; the poison job, which declares none, runs
through `runRegions`, so each Lean face writes exactly the rows its lowering
asks the host for. -/
def jobLog (entry : JobEntry) : Except String Effect4.Trace.Log :=
  let table := entry.program.table
  let service := Flow.tableRegionService ⟨0⟩ table jobsFamily jobAtom
  let named := tableNameOf ⟨0⟩ table
  if entry.program.interrupts then
    let result : ((Flow.InterruptResult × Flow.Tape) × Effect4.Trace.Log) × Queue :=
      ((Flow.runInterruptsDefault entry.program.flow entry.program.masked service named
        entry.tape entry.itape entry.input).run []).run entry.queue
    match result.1.1.1 with
    | .done _ => pure result.1.2
    | .failed _ => pure result.1.2
    | .interrupted => pure result.1.2
    | other =>
        throw s!"the job run of {entry.program.name}.{entry.golden} did not finish: {repr other}"
  else
    let result : ((Flow.RunResult × Flow.Tape) × Effect4.Trace.Log) × Queue :=
      ((Flow.runRegionsDefault entry.program.flow service named entry.tape entry.input).run
        []).run entry.queue
    match result.1.1.1 with
    | .done _ => pure result.1.2
    | .failed _ => pure result.1.2
    | other =>
        throw s!"the job run of {entry.program.name}.{entry.golden} did not finish: {repr other}"

/-- The queue the Lean face ends with; the design note quotes it beside the
JSON the host tail leaves behind. -/
def jobQueueAfter (entry : JobEntry) : Queue :=
  let table := entry.program.table
  let service := Flow.tableRegionService ⟨0⟩ table jobsFamily jobAtom
  let named := tableNameOf ⟨0⟩ table
  if entry.program.interrupts then
    (((Flow.runInterruptsDefault entry.program.flow entry.program.masked service named
      entry.tape entry.itape entry.input).run []).run entry.queue).2
  else
    (((Flow.runRegionsDefault entry.program.flow service named entry.tape entry.input).run
      []).run entry.queue).2

/-- The flow families of the dispatch-form module. -/
def flowFamilies : List (ServiceRow × List FlowProgram × List RegionProgram) :=
  [ (Cell.rows, flowEntries.map (·.program), []),
    (RCell.rows, [], regionEntries.map (·.program) ++ interruptEntries.map (·.program)) ]

/-- The families the module declares, each with its scripts. -/
def families : List (ServiceRow × List Script) :=
  [ (Cell.rows, [incr.script, twice.script]), (ECell.rows, [recover.script]), (FCell.rows, [fallible.script])
  , (Tri.rows, [probe.script]) ]

/-! ## The projections, by name

Each family answers one function from a projection's *name* to its text, and one
list of the names that family projects. The `<family>-golden` commands and the
`all` command below both read exactly these, so the two paths cannot name
different files or render one differently: the shell that once spelled a loop
per family now spells none (survey finding H11).

The provenance prologue is not Lean's to compute -- it digests the shell
generator itself and reads `lake-manifest.json` -- so `all` takes it as a file
and prepends the same bytes to every projection, exactly as the shell's
`{ provenance; run … }` group did. -/

/-- The straight-line projections: one `<program>.empty.tsv` per script. -/
def goldenText (name : String) : IO String :=
  match programs.find? (·.name == name) with
  | some entry =>
      admitted name entry.log
        (Effect4.Target.TypeScript.Trace.golden (name ++ ".empty") []
          ((entry.script.ruleSet entry.rows).map Rule.id) entry.log)
  | none => throw (IO.userError s!"unknown program {name}")

/-- The Flow-runner projections, as `<program>` and `<tape>` name pairs: the
flow entries with each of their tapes, then the region entries, whose one
tape is empty. -/
def flowProjections : List (String × String) :=
  (flowEntries.flatMap fun entry => entry.tapes.map fun (tapeName, _) => (entry.program.name, tapeName)) ++
  regionEntries.map fun entry => (entry.program.name, "empty")

def flowGoldenText (name tapeName : String) : IO String :=
  match flowEntries.find? (·.program.name == name) with
  | some entry =>
      match entry.tapes.find? (·.1 == tapeName) with
      | some (_, tape) =>
          let boundary := entry.boundaries.find? (·.1 == tapeName)
          match flowLogWith entry tape (boundary.map (·.2.1)) with
          | .ok log =>
              admitted (name ++ "." ++ tapeName) log
                (Effect4.Target.TypeScript.Trace.golden (name ++ "." ++ tapeName) tape.wire
                  ((Flow.structuredRuleSet entry.rows entry.program).map Rule.id) log (face := "lean-flow")
                  (budgets := (boundary.map (·.2.2)).getD []))
          | .error message => throw (IO.userError message)
      | none => throw (IO.userError s!"no tape {tapeName} for {name}")
  | none =>
      match regionEntries.find? (·.program.name == name) with
      | some entry =>
          match regionLog entry with
          | .ok log =>
              pure (Effect4.Target.TypeScript.Trace.golden (name ++ ".empty") []
                ((Region.ruleSet RCell.rows entry.program).map Rule.id) log (face := "lean-flow"))
          | .error message => throw (IO.userError message)
      | none => throw (IO.userError s!"no flow program {name}")

/-- Interruption as decisions (M2): their own subdirectory under `flow/`. -/
def interruptGoldenText (name : String) : IO String :=
  match interruptEntries.find? (·.program.name == name) with
  | some entry =>
      match interruptLog entry with
      | .ok log =>
          admitted name log
            (Effect4.Target.TypeScript.Trace.golden name entry.itape.wire
              ((Region.ruleSet RCell.rows entry.program).map Rule.id) log (face := "lean-flow"))
      | .error message => throw (IO.userError message)
  | none => throw (IO.userError s!"no interrupt program {name}")

def scopeGoldenText (name : String) : IO String :=
  match scopePrograms.find? (·.name == name) with
  | some entry =>
      admitted name entry.log
        (Effect4.Target.TypeScript.Trace.golden ("scope." ++ name) []
          ((entry.script.ruleSet Scopes.rows).map Rule.id) entry.log)
  | none => throw (IO.userError s!"unknown scope program {name}")

def layerGoldenText (name : String) : IO String :=
  match layerPrograms.find? (·.name == name) with
  | some entry =>
      admitted name entry.log
        (Effect4.Target.TypeScript.Trace.golden ("layer." ++ name) []
          ((entry.script.ruleSet Layers.rows).map Rule.id) entry.log)
  | none => throw (IO.userError s!"unknown layer program {name}")

def fiberGoldenText (name : String) : IO String :=
  match fiberPrograms.find? (·.name == name) with
  | some entry =>
      -- A program the sequential projection refused something in has no
      -- Lean face to compare, and its golden is not written at all.
      -- counterexample: E4-SEM-CE-010
      if entry.stuck then
        throw (IO.userError
          s!"refusing to emit golden fiber.{name}: the sequential projection has no answer for one of its operations")
      else
        admitted name entry.log
          (Effect4.Target.TypeScript.Trace.golden ("fiber." ++ name) entry.tape
            ((entry.script.ruleSet Fibers.rows).map Rule.id) entry.log)
  | none => throw (IO.userError s!"unknown fiber program {name}")

/-- The job projections, as `<program>` and `<golden>` name pairs: four goldens
share the `jobRunner` body and differ in their queue seed and their tapes. -/
def jobProjections : List (String × String) :=
  jobEntries.map fun entry => (entry.program.name, entry.golden)

def jobGoldenText (name goldenName : String) : IO String :=
  match jobEntries.find? fun entry =>
      entry.program.name == name && entry.golden == goldenName with
  | some entry =>
      match jobLog entry with
      | .ok log =>
          -- One `tape` header carries both tapes: the choice sites the flow
          -- author wrote are below `interruptBase` and every interrupt site
          -- is at or above it (`Effect4.Flow.Point.site_ne_choose`), so the
          -- tail splits the one list into its two readers by site.
          admitted (name ++ "." ++ goldenName) log
            (Effect4.Target.TypeScript.Trace.golden (name ++ "." ++ goldenName)
              (entry.tape.wire ++ entry.itape.wire)
              ((Region.ruleSet Jobs.rows entry.program).map Rule.id) log (face := "lean-flow"))
      | .error message => throw (IO.userError message)
  | none => throw (IO.userError s!"no job golden {name}.{goldenName}")

def deferredGoldenText (name : String) : IO String :=
  match deferredEntries.find? (·.name == name) with
  | some entry =>
      admitted name entry.log
        (Effect4.Target.TypeScript.Trace.golden ("deferred." ++ name) []
          ((entry.script.ruleSet Deferreds.rows).map Rule.id) entry.log)
  | none => throw (IO.userError s!"unknown deferred program {name}")

/-- The `Contexts` family (lowering lane L3). It has no host tail yet, so its
goldens are not written by `writeAll`; this arm exists so the host lane can
generate them the moment `context-tail.ts` lands. -/
def contextGoldenText (name : String) : IO String :=
  match contextPrograms.find? (·.name == name) with
  | some entry =>
      admitted name entry.log
        (Effect4.Target.TypeScript.Trace.golden ("context." ++ name) []
          ((entry.script.ruleSet Contexts.rows).map Rule.id) entry.log)
  | none => throw (IO.userError s!"unknown context program {name}")

def refGoldenText (name : String) : IO String :=
  match Effect4.RefFamily.refPrograms.find? (·.name == name) with
  | some entry =>
      admitted name entry.log
        (Effect4.Target.TypeScript.Trace.golden ("ref." ++ name) []
          ((entry.script.ruleSet entry.rows).map Rule.id) entry.log)
  | none => throw (IO.userError s!"unknown ref program {name}")

/-- Write every projection of every family under `dir`, each prefixed by
`prologue`. One process writes the whole corpus; the shell no longer spawns a
Lean elaboration per golden (survey finding H11). The subdirectories are the
ones the host gate's globs depend on: a family with its own tail must not be
visible to another family's glob, and each comment in
`scripts/generate-trace-goldens.sh` that said so now says it here. -/
def writeAll (dir prologue : String) : IO Unit := do
  let write (path : String) (body : String) : IO Unit :=
    IO.FS.writeFile (dir ++ "/" ++ path) (prologue ++ body)
  IO.FS.createDirAll dir
  write "masks.tsv" Effect4.Target.TypeScript.Trace.maskTable
  for entry in programs do
    write (entry.name ++ ".empty.tsv") (← goldenText entry.name)
  -- The Flow-runner face of the same programs (the internal oracle), kept in a
  -- subdirectory so the host gate's program glob never sees them.
  IO.FS.createDirAll (dir ++ "/flow")
  for (program, tapeName) in flowProjections do
    write ("flow/" ++ program ++ "." ++ tapeName ++ ".tsv") (← flowGoldenText program tapeName)
  -- Interruption as decisions (M2), in their own subdirectory under `flow/`, so
  -- the flow host loop's `flow/*.tsv` glob never sees them: they need the
  -- Interrupts service and `interrupt-tail.ts`, not `flow-tail.ts`. The `tape`
  -- header of each is the *interrupt* tape; none of these flows chooses.
  IO.FS.createDirAll (dir ++ "/flow/interrupt")
  for entry in interruptEntries do
    write ("flow/interrupt/" ++ entry.program.name ++ ".tsv") (← interruptGoldenText entry.program.name)
  -- The `Scopes` family, likewise in a subdirectory of its own: it has its own
  -- generated module and its own tail (`scope-tail.ts`), so the straight-line
  -- host loop's `*.empty.tsv` glob must not see it.
  IO.FS.createDirAll (dir ++ "/scope")
  for entry in scopePrograms do
    write ("scope/" ++ entry.name ++ ".tsv") (← scopeGoldenText entry.name)
  -- The `Layers` family (packet M4): its own generated module and its own tail
  -- (`layer-tail.ts`). Its handles are rc.112 `Ref` and `Scope` objects,
  -- indexed by the tracer.
  IO.FS.createDirAll (dir ++ "/layer")
  for entry in layerPrograms do
    write ("layer/" ++ entry.name ++ ".tsv") (← layerGoldenText entry.name)
  -- The `Fibers` family (packet M3): its own generated module and its own tail
  -- (`fiber-tail.ts`). Each golden carries the tape its forks are answered
  -- from, in the `tape` header row.
  IO.FS.createDirAll (dir ++ "/fiber")
  for entry in fiberPrograms do
    write ("fiber/" ++ entry.name ++ ".tsv") (← fiberGoldenText entry.name)
  -- The job runner (the first real program): its own generated module
  -- (`job-fixture.ts`) and its own tail (`job-tail.ts`) over a real file-backed
  -- queue. A golden is named `<program>.<golden>`.
  IO.FS.createDirAll (dir ++ "/job")
  for (program, goldenName) in jobProjections do
    write ("job/" ++ program ++ "." ++ goldenName ++ ".tsv") (← jobGoldenText program goldenName)
  -- The `Deferreds` family, kept in a subdirectory for the same reason as the
  -- flow goldens: they run through `deferred-tail.ts`, not `tail.ts`.
  IO.FS.createDirAll (dir ++ "/deferred")
  for entry in deferredEntries do
    write ("deferred/" ++ entry.name ++ ".tsv") (← deferredGoldenText entry.name)
  -- The `Refs` family: its own generated module and its own tail
  -- (`ref-tail.ts`).
  IO.FS.createDirAll (dir ++ "/ref")
  for entry in Effect4.RefFamily.refPrograms do
    write ("ref/" ++ entry.name ++ ".tsv") (← refGoldenText entry.name)

def main (args : List String) : IO Unit := do
  match args with
  | ["fixture"] =>
      -- The straight-line module imports the atoms its scripts call; every atom
      -- still exists on both faces (`Atoms.rows` ↔ `atoms.ts`).
      match modules? families [.named ["succ", "orZero", "firstOr"] "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a script")
  | ["atoms"] =>
      -- One `atoms.ts` for every family, concatenated from the `effect_atoms`
      -- rows each family declares beside its own programs: the Lean body and
      -- the host body of an atom come from one declaration wherever the atom
      -- lives (`E4-TARGET-CE-025`).
      IO.print (atomsModule
        (Atoms.rows ++ Effect4.DeferredFamily.DeferredAtoms.rows ++
          Effect4.ScopeFamily.ScopeAtoms.rows ++ Effect4.LayerFamily.LayerAtoms.rows ++
          Effect4.RefFamily.RefFns.rows)
        [TypeScript.Import.types ["JobQueue"] "./job-queue.ts",
         TypeScript.Import.types ["RefFn"] "./ref-fns.ts",
         TypeScript.Import.types ["Layer", "Ref"] "effect"])
  | ["masks"] => IO.print Effect4.Target.TypeScript.Trace.maskTable
  | ["golden", name] => IO.print (← goldenText name)
  | ["all", dir] => writeAll dir ""
  | ["all", dir, provenanceFile] => writeAll dir (← IO.FS.readFile provenanceFile)
  | ["programs"] => IO.println (String.intercalate "\n" (programs.map (·.name)))
  | ["types"] =>
      for entry in programs do
        IO.println (entry.name ++ "\t" ++ Script.declarationLine entry.rows entry.script)
  | ["flow-programs"] =>
      for (program, tapeName) in flowProjections do
        IO.println (program ++ "\t" ++ tapeName)
  | ["flow-golden", name, tapeName] => IO.print (← flowGoldenText name tapeName)
  | ["oracle"] =>
      for entry in flowEntries do
        match entry.oracle, entry.tapes with
        | some expected, (_, tape) :: _ =>
            match flowLog entry tape with
            | .ok log =>
                unless Effect4.Trace.agree Effects.Trace.Mask.m2 log expected do
                  throw (IO.userError s!"FAIL flow oracle {entry.program.name}: the runner and the traced service differ under m2")
                match entry.script with
                | none =>
                    IO.println s!"PASS flow oracle {entry.program.name}: the runner agrees with the traced service under m2 ({log.length} rows); no script face"
                | some script =>
                    match denotationLog entry script with
                    | .error message =>
                        throw (IO.userError s!"FAIL flow oracle {entry.program.name}: {message}")
                    | .ok denoted =>
                        unless Effect4.Trace.agree Effects.Trace.Mask.m2 denoted expected do
                          throw (IO.userError s!"FAIL flow oracle {entry.program.name}: the script denotation and the traced service differ under m2")
                        unless Effect4.Trace.agree Effects.Trace.Mask.m2 denoted log do
                          throw (IO.userError s!"FAIL flow oracle {entry.program.name}: the script denotation and the runner differ under m2")
                        IO.println s!"PASS flow oracle {entry.program.name}: the traced service, the Flow runner and the script denotation agree under m2 ({log.length} rows)"
            | .error message => throw (IO.userError s!"FAIL flow oracle {entry.program.name}: {message}")
        | _, _ => pure ()
  | ["flow-fixture"] =>
      match regionModules? flowFamilies [.named ["succ"] "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "dispatch lowering refused a flow")
  | ["structured-fixture"] =>
      match structuredModules? flowFamilies [.named ["succ"] "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "structured lowering refused a flow")
  | ["flow-types"] =>
      for entry in flowEntries do
        for (tapeName, _) in entry.tapes do
          IO.println (entry.program.name ++ "\t" ++ tapeName ++ "\t" ++
            Flow.declarationLine entry.rows entry.program)
      for entry in regionEntries do
        IO.println (entry.program.name ++ "\tempty\t" ++ Region.declarationLine RCell.rows entry.program)
  | ["interrupt-programs"] =>
      IO.println (String.intercalate "\n" (interruptEntries.map (·.program.name)))
  | ["interrupt-golden", name] => IO.print (← interruptGoldenText name)
  | ["layer-fixture"] =>
      -- `Layer`, `Ref`, `Scope` and `Context` are imported as types only: the
      -- generated module names `Layer.Layer<number>`, `Layer.MemoMap`,
      -- `Ref.Ref<number>`, `Scope.Closeable` and `Context.Context<never>` in
      -- the service shape and never calls into any of them.
      match modules? [(Layers.rows, layerPrograms.map (·.script))]
          [.types ["Layer", "Ref", "Scope"] "effect",
           .named layerAtomNames "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a layer script")
  | ["layer-programs"] => IO.println (String.intercalate "\n" (layerPrograms.map (·.name)))
  | ["layer-golden", name] => IO.print (← layerGoldenText name)
  | ["layer-types"] =>
      for entry in layerPrograms do
        IO.println (entry.name ++ "\t" ++ Script.declarationLine Layers.rows entry.script)
  | ["scope-fixture"] =>
      -- `Scope` is imported as a type only: the generated module names
      -- `Scope.Closeable` in the service shape and never calls into it.
      -- `Result` is the `closeExit` argument's spelling.
      match modules? [(Scopes.rows, scopePrograms.map (·.script))]
          [.types ["Scope"] "effect", .named scopeAtomNames "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a scope script")
  | ["scope-programs"] => IO.println (String.intercalate "\n" (scopePrograms.map (·.name)))
  | ["scope-golden", name] => IO.print (← scopeGoldenText name)
  | ["admission-probe"] =>
      -- The planted value of `scripts/test-trace-goldens-gate.sh`: no program of
      -- the corpus produces a natural the host cannot carry, so the admission
      -- clause is only reachable by planting one here.
      let log : Effect4.Trace.Log :=
        [.answer "probe" (.nat (hostSafeInteger + 1)), .done (.success .unit)]
      IO.print (← admitted "admission-probe" log
        (Effect4.Target.TypeScript.Trace.golden "admission.probe" [] [] log))
  | ["scope-types"] =>
      for entry in scopePrograms do
        IO.println (entry.name ++ "\t" ++ Script.declarationLine Scopes.rows entry.script)
  | ["region-frontier"] =>
      for entry in regionEntries do
        match regionFrontierLog entry with
        | .ok log =>
            IO.print (Effect4.Target.TypeScript.Trace.golden (entry.program.name ++ ".frontier") []
              ((Region.ruleSet RCell.rows entry.program).map Rule.id) log (face := "lean-flow"))
        | .error message => throw (IO.userError message)
  | ["frame-trace"] =>
      -- Packet D4, the finalizer half. For each region program, the frame
      -- machine's projected trace (`FrameEvent.traceOf` of the run of
      -- `compileRegion`) beside the runner's log under the mask that keeps
      -- `finalizer` and `done`. The two are equal by
      -- `Effect4Test/Semantics/RegionSimulationContract.lean`; this arm exists
      -- so the coordinator can pin the pair as a golden later. The oracle is
      -- the stateless face of `rcellFamily` at the entry's initial state: the
      -- three region programs never perform `get` or `put`.
      for entry in regionEntries do
        let fuel := Flow.fuelFor entry.program.flow.flow.erase []
        let answerOf : (tableAlphabet ⟨0⟩ entry.program.table).Op → Effects.Trace.Val →
            Except Effects.Trace.Val Effects.Trace.Val := fun op request =>
          match (OpSpec.at entry.program.table op).kind with
          | .lit value => .ok value
          | .atom => .ok (cellAtom (OpSpec.at entry.program.table op).name request)
          | .family =>
            ((rcellFamily (OpSpec.at entry.program.table op).name request).run entry.initial).1
        let machine := Effect4.RegionSimulation.traceOfRun
          (Effect4.FrameFiber.run
            (Effect4.RegionSimulation.regionInterp (tableAlphabet ⟨0⟩ entry.program.table)
              entry.program.flow.flow
              (Effect4.RegionSimulation.statelessOracle (tableAlphabet ⟨0⟩ entry.program.table)
                entry.program.flow.flow answerOf))
            (Effect4.RegionSimulation.regionBound fuel)
            (Effect4.FrameFiber.start
              (Effect4.RegionSimulation.compileAt (tableAlphabet ⟨0⟩ entry.program.table)
                entry.program.flow.flow
                ⟨fuel, entry.program.flow.flow.entry, [entry.input], []⟩))).2
        match regionLog entry with
        | .ok log =>
            let runner := Effects.Trace.project
              Effect4.RegionSimulation.finalizerAndOutcomeMask log
            IO.println ("program\t" ++ entry.program.name)
            for event in machine do
              IO.println ("machine\t" ++ Effect4.Target.TypeScript.Trace.row event)
            for event in runner do
              IO.println ("runner\t" ++ Effect4.Target.TypeScript.Trace.row event)
            IO.println (if machine == runner then "agree\ttrue" else "agree\tfalse")
        | .error message => throw (IO.userError message)
  | ["region-oracle"] =>
      -- The region half of the internal oracle. The runner of
      -- `Effect4/Flow/Region.lean` and `interpret` of the region denotation
      -- (`Effect4/Semantics/RegionDenotation.lean`, packet D2) are two Lean
      -- emitters of the same alphabet; `runRegions_eq_interpret` says they
      -- agree, and this arm computes that agreement per region program.
      for entry in regionEntries do
        let table := entry.program.table
        let flow := entry.program.flow
        let fuel := Flow.fuelFor flow.flow.erase []
        let service := Flow.tableRegionService ⟨0⟩ table rcellFamily cellAtom
        let named := tableNameOf ⟨0⟩ table
        let runner : ((Flow.RunResult × Flow.Tape) × Effect4.Trace.Log) × Nat :=
          ((Flow.runRegions fuel flow service named [] entry.input).run []).run entry.initial
        let denoted : ((Flow.RunResult × Flow.Tape) × Effect4.Trace.Log) × Nat :=
          (((fun outcome => outcome.1) <$> Flow.interpretRegions service named
            (Flow.denoteRegions fuel flow [] entry.input)).run []).run entry.initial
        if runner.1.2 = denoted.1.2 then
          IO.println s!"PASS region oracle {entry.program.name}: the runner and interpret of the denotation write the same log ({runner.1.2.length} rows)"
        else
          throw (IO.userError s!"FAIL region oracle {entry.program.name}: the runner and interpret of the denotation differ")
  | ["fiber-fixture"] =>
      -- `Fiber` and `Option` are imported as types only: the generated module
      -- names `Fiber.Fiber<number, number>` and `Option.Option<number>` in the
      -- service shape and never calls into either.
      match modules? [(Fibers.rows, fiberPrograms.map (·.script))] [.types ["Fiber", "Option"] "effect"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a fiber script")
  | ["fiber-programs"] => IO.println (String.intercalate "\n" (fiberPrograms.map (·.name)))
  | ["fiber-golden", name] => IO.print (← fiberGoldenText name)
  | ["fiber-types"] =>
      for entry in fiberPrograms do
        IO.println (entry.name ++ "\t" ++ Script.declarationLine Fibers.rows entry.script)
  | ["job-fixture"] =>
      -- `JobQueue` is imported as a type only: the generated module names it in
      -- the `Jobs` service shape and never calls into it. `succ` and `dec` are
      -- the drain's counters and `snd` is its ticket projection.
      match regionModules? [(Jobs.rows, [], jobPrograms)]
        [.named ["succ", "dec", "snd", "nonEmpty", "positive"] "./atoms.ts",
         .types ["JobQueue"] "./job-queue.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "dispatch lowering refused a job flow")
  | ["job-programs"] =>
      for (program, goldenName) in jobProjections do
        IO.println (program ++ "\t" ++ goldenName)
  | ["job-golden", name, goldenName] => IO.print (← jobGoldenText name goldenName)
  | ["job-types"] =>
      for program in jobPrograms do
        IO.println (program.name ++ "\t" ++ Region.declarationLine Jobs.rows program)
  | ["job-queues"] =>
      for entry in jobEntries do
        IO.println (entry.program.name ++ "." ++ entry.golden ++ "\t" ++
          toString (repr (jobQueueAfter entry)))
  | ["deferred-fixture"] =>
      -- `Deferred`, `Option` and `Result` are imported as types only: the
      -- generated module names `Deferred.Deferred<number, number>` and
      -- `Option.Option<Result.Result<number, number>>` in the service shape and
      -- never calls into any of them.
      match modules? [(Deferreds.rows, deferredEntries.map (·.script))]
          [.types ["Deferred", "Option", "Result"] "effect",
           .named deferredAtomNames "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a deferred script")
  | ["deferred-programs"] => IO.println (String.intercalate "\n" (deferredEntries.map (·.name)))
  | ["deferred-golden", name] => IO.print (← deferredGoldenText name)
  | ["deferred-types"] =>
      for entry in deferredEntries do
        IO.println (entry.name ++ "\t" ++ Script.declarationLine Deferreds.rows entry.script)
  | ["ref-fixture"] =>
      -- `Ref` is imported as a type only: the generated module names
      -- `Ref.Ref<number>` in the service shape and never calls into it.
      -- `Effect4.RefFamily` is not opened: it carries its own `succ` atom, and
      -- this module already has one for the `Cell` scripts.
      -- `RefFn` is the named-function table `ref-fns.ts` exports; the atoms
      -- that mint one live in `Effect4.RefFamily.RefFns` and reach `atoms.ts`
      -- through the `atoms` arm above.
      match modules? Effect4.RefFamily.refFamilies
          [.types ["Ref"] "effect", .types ["RefFn"] "./ref-fns.ts",
           .named (["succ"] ++ Effect4.RefFamily.RefFns.rows.map (·.name)) "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a ref script")
  | ["context-fixture"] =>
      -- `Context`, `Layer`, `Scope` and `Option` are imported as types only.
      match modules? [(Contexts.rows, contextPrograms.map (·.script))]
          [.types ["Layer", "Scope"] "effect"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a context script")
  | ["context-programs"] =>
      IO.println (String.intercalate "\n" (contextPrograms.map (·.name)))
  | ["context-golden", name] => IO.print (← contextGoldenText name)
  | ["context-types"] =>
      for entry in contextPrograms do
        IO.println (entry.name ++ "\t" ++ Script.declarationLine Contexts.rows entry.script)
  | ["ref-programs"] =>
      IO.println (String.intercalate "\n" (Effect4.RefFamily.refPrograms.map (·.name)))
  | ["ref-golden", name] => IO.print (← refGoldenText name)
  | ["ref-types"] =>
      for entry in Effect4.RefFamily.refPrograms do
        IO.println (entry.name ++ "\t" ++ Script.declarationLine entry.rows entry.script)
  | _ => throw (IO.userError "usage: Generate.lean all <dir> [<provenance-file>] | fixture | masks | golden <program> | programs | types | flow-programs | flow-golden <program> <tape> | oracle | flow-fixture | structured-fixture | flow-types | scope-fixture | scope-programs | scope-golden <program> | scope-types | region-frontier | admission-probe | frame-trace | interrupt-programs | interrupt-golden <program> | region-oracle | fiber-fixture | fiber-programs | fiber-golden <program> | fiber-types | job-fixture | job-programs | job-golden <program> <golden> | job-types | job-queues | deferred-fixture | deferred-programs | deferred-golden <program> | deferred-types | ref-fixture | ref-programs | ref-golden <program> | ref-types | context-fixture | context-programs | context-golden <program> | context-types | atoms | layer-fixture | layer-programs | layer-golden <program> | layer-types")
