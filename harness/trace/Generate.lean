import Effect4.Meta.Derive
import Effect4.Target.TypeScript.Trace
import Effect4.Target.TypeScript.Lower
import Effect4.Target.TypeScript.ScriptFlow

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

/-! ## The Flow-runner face (internal oracle) -/

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

/-- Embed, admit, and run a script's flow; the log the runner wrote. -/
def flowLog (entry : Entry) (input : Effects.Trace.Val) : Except String Effect4.Trace.Log := do
  let some (table, raw) := Script.toFlow entry.rows cellAtoms entry.script
    | throw s!"embedding refused {entry.name}"
  match admit (tableAlphabet ⟨0⟩ table) raw with
  | .error diagnostic => throw s!"admission refused the embedded {entry.name}: {repr diagnostic}"
  | .ok flow =>
    let result : (Flow.RunResult × Effect4.Trace.Log) × Nat :=
      ((Flow.runDefault flow (tableService ⟨0⟩ table cellFamily cellAtom) (tableNameOf ⟨0⟩ table)
        [] input).run []).run entry.initial
    match result.1.1 with
    | .done _ => pure result.1.2
    | other => throw s!"the flow run of {entry.name} did not finish: {repr other}"

/-- The programs with a flow golden. -/
def flowPrograms : List (Entry × Effects.Trace.Val) :=
  programs.filterMap fun entry => entry.flowInput.map fun input => (entry, input)

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
  | ["flow-programs"] => IO.println (String.intercalate "\n" (flowPrograms.map (·.1.name)))
  | ["flow-golden", name] =>
      match flowPrograms.find? (·.1.name == name) with
      | some (entry, input) =>
          match flowLog entry input with
          | .ok log =>
              IO.print (Effect4.Target.TypeScript.Trace.golden (name ++ ".empty") [] ["flow-runner"] log
                (face := "lean-flow"))
          | .error message => throw (IO.userError message)
      | none => throw (IO.userError s!"no flow golden for {name}")
  | ["oracle"] =>
      for (entry, input) in flowPrograms do
        match flowLog entry input with
        | .ok log =>
            if Effect4.Trace.agree Effects.Trace.Mask.m2 log entry.log then
              IO.println s!"PASS flow oracle {entry.name}: the runner agrees with the traced service under m2 ({log.length} rows)"
            else
              throw (IO.userError s!"FAIL flow oracle {entry.name}: the runner and the traced service differ under m2")
        | .error message => throw (IO.userError s!"FAIL flow oracle {entry.name}: {message}")
  | ["types"] =>
      for entry in programs do
        IO.println (entry.name ++ "\t" ++ entry.script.declarationLine entry.rows)
  | _ => throw (IO.userError "usage: Generate.lean fixture | masks | golden <program> | programs | flow-programs | flow-golden <program> | oracle")
