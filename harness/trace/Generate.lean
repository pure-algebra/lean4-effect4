import Effect4.Meta.Derive
import Effect4.Target.TypeScript.Trace
import Effect4.Target.TypeScript.Lower
import Effect4.Target.TypeScript.ScriptFlow
import Effect4.Target.TypeScript.FlowLower
import Effect4.Target.TypeScript.RegionLower
import Effect4.Flow.Region

/-!
The trace harness family. `main fixture` prints the generated Effect v4 module,
`main golden <program>` prints the Lean-expected trace of one program under
the empty tape, and `main masks` prints the registered mask table. Every
golden is the traced service's log plus the outcome, rendered by
`Effect4.Target.TypeScript.Trace`; `check.sh` byte-compares the outputs with
`fixture.ts` and `generated/traces/` and then runs the host.
-/

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

effect_signature Cell where
  | get : Nat ⟪ "read the cell", "current value" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell", "store" ⟫

/-- A pure atom; `atoms.ts` carries its host body. -/
def succ (n : Nat) : Nat := n + 1

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
-- `Either.Either<number, string>` on the host. The program recovers from it
-- through a pure atom and continues.
effect_signature ECell where
  | tryGet : Except String Nat ⟪ "try to read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫

/-- Recover a value from a failed read; `atoms.ts` carries its host body. -/
def orZero (e : Except String Nat) : Nat :=
  match e with
  | .ok n => n
  | .error _ => 0

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
  , { name := "fallible", rows := FCell.rows, script := fallible.script, log := fgoldenLog (fallible 5) 41 } ]

/-! ## The Flow face: the runner (internal oracle) and the dispatch lowering -/

/-- The atoms the Cell scripts call, with their TypeScript types. -/
def cellAtoms : AtomTable := [("succ", "number", "number")]

/-- The Cell family by name, over the same state the traced service uses. -/
def cellFamily : String → Effects.Trace.Val → StateT Nat Id Effects.Trace.Val
  | "get", _ => do let n ← get; pure (.nat n)
  | "put", .nat n => do set n; pure .unit
  | _, _ => pure .unit

def cellAtom : String → Effects.Trace.Val → Effects.Trace.Val
  | "succ", .nat n => .nat (n + 1)
  | _, _ => .unit

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

/-- The flow programs of the harness. -/
def flowEntries : List FlowEntry :=
  (programs.filterMap fun entry =>
    match entry.flowInput, embed? entry with
    | some input, some program =>
        some { program := program, rows := entry.rows, tapes := [("empty", [])], input := input,
               initial := entry.initial, oracle := some entry.log }
    | _, _ => none) ++
  ((admit? "chooser" [] chooserRaw).toList.map fun program =>
    { program := program, tapes := [("left", [decision 7 true]), ("right", [decision 7 false])],
      input := .nat 5 }) ++
  ((admit? "swap" swapTable swapRaw).toList.map fun program =>
    { program := program,
      tapes := [("once", [decision 1 true, decision 1 false]),
                ("twice", [decision 1 true, decision 1 true, decision 1 false])],
      input := .nat 5 })

/-- Run a flow entry on one tape; the log the runner wrote. -/
def flowLog (entry : FlowEntry) (tape : Flow.Tape) : Except String Effect4.Trace.Log :=
  let table := entry.program.table
  let result : (Flow.RunResult × Effect4.Trace.Log) × Nat :=
    ((Flow.runDefault entry.program.flow (tableService ⟨0⟩ table cellFamily cellAtom)
      (tableNameOf ⟨0⟩ table) tape entry.input).run []).run entry.initial
  match result.1.1 with
  | .done _ => pure result.1.2
  | other => throw s!"the flow run of {entry.program.name} did not finish: {repr other}"

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

/-- The flow families of the dispatch-form module. -/
def flowFamilies : List (ServiceRow × List FlowProgram × List RegionProgram) :=
  [ (Cell.rows, flowEntries.map (·.program), []), (RCell.rows, [], regionEntries.map (·.program)) ]

/-- The families the module declares, each with its scripts. -/
def families : List (ServiceRow × List Script) :=
  [ (Cell.rows, [incr.script, twice.script]), (ECell.rows, [recover.script]), (FCell.rows, [fallible.script]) ]

def main (args : List String) : IO Unit := do
  match args with
  | ["fixture"] =>
      match modules? families [.named ["succ", "orZero"] "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a script")
  | ["masks"] => IO.print Effect4.Target.TypeScript.Trace.maskTable
  | ["golden", name] =>
      match programs.find? (·.name == name) with
      | some entry =>
          IO.print (Effect4.Target.TypeScript.Trace.golden (name ++ ".empty") []
            ((entry.script.ruleSet entry.rows).map Rule.id) entry.log)
      | none => throw (IO.userError s!"unknown program {name}")
  | ["programs"] => IO.println (String.intercalate "\n" (programs.map (·.name)))
  | ["flow-programs"] =>
      for entry in flowEntries do
        for (tapeName, _) in entry.tapes do
          IO.println (entry.program.name ++ "\t" ++ tapeName)
      for entry in regionEntries do
        IO.println (entry.program.name ++ "\tempty")
  | ["flow-golden", name, tapeName] =>
      match flowEntries.find? (·.program.name == name) with
      | some entry =>
          match entry.tapes.find? (·.1 == tapeName) with
          | some (_, tape) =>
              match flowLog entry tape with
              | .ok log =>
                  IO.print (Effect4.Target.TypeScript.Trace.golden (name ++ "." ++ tapeName) tape.wire
                    ((Flow.ruleSet entry.rows entry.program).map Rule.id) log (face := "lean-flow"))
              | .error message => throw (IO.userError message)
          | none => throw (IO.userError s!"no tape {tapeName} for {name}")
      | none =>
          match regionEntries.find? (·.program.name == name) with
          | some entry =>
              match regionLog entry with
              | .ok log =>
                  IO.print (Effect4.Target.TypeScript.Trace.golden (name ++ ".empty") [] 
                    ((Region.ruleSet RCell.rows entry.program).map Rule.id) log (face := "lean-flow"))
              | .error message => throw (IO.userError message)
          | none => throw (IO.userError s!"no flow program {name}")
  | ["oracle"] =>
      for entry in flowEntries do
        match entry.oracle, entry.tapes with
        | some expected, (_, tape) :: _ =>
            match flowLog entry tape with
            | .ok log =>
                if Effect4.Trace.agree Effects.Trace.Mask.m2 log expected then
                  IO.println s!"PASS flow oracle {entry.program.name}: the runner agrees with the traced service under m2 ({log.length} rows)"
                else
                  throw (IO.userError s!"FAIL flow oracle {entry.program.name}: the runner and the traced service differ under m2")
            | .error message => throw (IO.userError s!"FAIL flow oracle {entry.program.name}: {message}")
        | _, _ => pure ()
  | ["flow-fixture"] =>
      match regionModules? flowFamilies [.named ["succ"] "./atoms.ts"] with
      | some source => IO.print source
      | none => throw (IO.userError "dispatch lowering refused a flow")
  | ["flow-types"] =>
      for entry in flowEntries do
        for (tapeName, _) in entry.tapes do
          IO.println (entry.program.name ++ "\t" ++ tapeName ++ "\t" ++
            Flow.declarationLine entry.rows entry.program)
      for entry in regionEntries do
        IO.println (entry.program.name ++ "\tempty\t" ++ Region.declarationLine RCell.rows entry.program)
  | _ => throw (IO.userError "usage: Generate.lean fixture | masks | golden <program> | programs | flow-programs | flow-golden <program> <tape> | oracle | flow-fixture | flow-types")
