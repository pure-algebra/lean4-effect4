import Effect4.Meta.Derive
import Effect4.Runtime.Scope
import Effect4.Target.TypeScript.Trace
import Effect4.Target.TypeScript.Lower
import Effect4.Target.TypeScript.ScriptFlow
import Effect4.Target.TypeScript.FlowLower
import Effect4.Target.TypeScript.RegionLower
import Effect4.Target.TypeScript.StructuredLower
import Effect4.Flow.Region
import Effect4.Semantics.Approximation
import Effect4.Semantics.RegionSimulation

/-!
The trace harness family. `main fixture` prints the generated Effect v4 module,
`main golden <program>` prints the Lean-expected trace of one program under
the empty tape, and `main masks` prints the registered mask table. Every
golden is the traced service's log plus the outcome, rendered by
`Effect4.Target.TypeScript.Trace`; `check.sh` byte-compares the outputs with
`fixture.ts` and `generated/traces/` and then runs the host.
-/

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4

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

/-! ## `Scopes`: a traced family over the reified rc.112 `Scope`

The first family whose operations take and return an opaque host handle. The
handle is `Handle "Scope.Closeable"` (`Effect4/Meta/Derive.lean`): the Lean
carrier is an index, the wire value is that index, and the target prints
rc.112's own opaque `Scope.Closeable`. The Lean face names scopes in creation
order and the host tracer indexes the objects it is handed in first-seen order,
which is the same order because a handle only ever leaves the host as the
answer of the `make` that produced it.

`close` answers the *keys the close ran, in order*. That is what makes LIFO,
removal and close idempotence observable at the service level without a
finalizer having to be an operation of its own: the model's answer is
`Scope.closeOrder` and the host's answer is the order rc.112 actually ran them
in. `addFinalizer` answers whether it registered (`true`) or ran the finalizer
immediately because the scope had closed (`false`), which is rc.112
`scopeAddFinalizerExit`'s two arms and the model's `Scope.addExit`.

Refusals, recorded here and in `docs/TRACE-DAG.md`:

- The finalizer strategy is not an operation. `make` is nullary and takes
  rc.112's `"sequential"` default; the parallel strategy needs a fiber machine
  (`Effect4Test/Audit/RuntimeCoverage.lean` `scope.close-parallel`), and this
  lane cannot observe it.
- `remove` has no rc.112 entry point. `effect`'s package exports map
  `"./internal/*"` to `null`, so `scopeRemoveFinalizerUnsafe` is unreachable;
  the host service performs the same two-arm removal over the *public* mutable
  `Scope.state` (`Scope.ts` `State.Open`), locating the entry by the identity
  of the finalizer it registered. The `remove` golden therefore pins the public
  state shape and the model, not an rc.112 call. -/

effect_signature Scopes where
  | make : Handle "Scope.Closeable" ⟪ "open a new scope", "acquire a lifetime" ⟫
  | addFinalizer (scope : Handle "Scope.Closeable") (key : Nat) : Bool
      ⟪ "register a finalizer under a key", "true when it was registered, false when the scope had closed and it ran now" ⟫
  | remove (scope : Handle "Scope.Closeable") (key : Nat) : Unit
      ⟪ "unregister the finalizer under a key" ⟫
  | close (scope : Handle "Scope.Closeable") : List Nat
      ⟪ "close the scope", "the keys the close ran, in order" ⟫

/-- The scope the model handler keeps: keys and finalizers are both `Nat`, so a
finalizer *is* its key and `Scope.closeOrder` is exactly the answer `close`
gives. `φ` is nominal by DB-02; what a finalizer does is the `run` argument. -/
abbrev ScopeCarrier := Scope Nat Nat Unit Unit Unit Unit Unit

/-- Every live scope, in creation order; a `Handle` indexes into it. -/
abbrev ScopeStore := List ScopeCarrier

/-- The nominal finalizer's effect. Nothing in this family observes a
finalizer's own exit, so it is the void exit; a fallible release is the packet
that settles the cause-merge divergence, and is refused here. -/
def scopeRun : Nat → Exit Unit Unit Unit Unit Unit → Exit Unit Unit Unit Unit Unit :=
  fun _ _ => Exit.void

/-- The Lean handler: a thin wrapper over `Effect4/Runtime/Scope.lean`.
`make` is `Scope.make`, `addFinalizer` is `Scope.addExit`, `remove` is
`Scope.removeUnsafe`, `close` is `Scope.close` with `Scope.closeOrder` as its
answer. It adds no scope semantics of its own. -/
def scopesLive : Scopes.Service (StateT ScopeStore Id) := fun name =>
  match name with
  | .make => fun _ => do
      let store ← get
      set (store ++ [Scope.make FinalizerStrategy.sequential])
      pure ⟨store.length⟩
  | .addFinalizer => fun (handle, key) => do
      let store ← get
      match store[handle.index]? with
      | none => pure false
      | some scope =>
          set (store.set handle.index (Scope.addExit scopeRun scope key key).1)
          pure (!scope.isClosed)
  | .remove => fun (handle, key) => do
      let store ← get
      match store[handle.index]? with
      | none => pure ()
      | some scope => set (store.set handle.index (scope.removeUnsafe key))
  | .close => fun handle => do
      let store ← get
      match store[handle.index]? with
      | none => pure []
      | some scope =>
          set (store.set handle.index (Scope.close scopeRun scope Exit.void).1)
          pure scope.closeOrder

-- Three finalizers, closed once: the keys come back last registered first.
effect_program scopeLifo (n : Nat) over Scopes : List Nat :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizer(s, 1)
  let _ ← Scopes.addFinalizer(s, 2)
  let _ ← Scopes.addFinalizer(s, 3)
  let r ← Scopes.close(s)
  return r

-- Registering on a closed scope runs the finalizer now and answers `false`.
effect_program scopeAddAfterClosed (n : Nat) over Scopes : Bool :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizer(s, 1)
  let _ ← Scopes.close(s)
  let a ← Scopes.addFinalizer(s, 2)
  return a

-- A removed key does not run.
effect_program scopeRemove (n : Nat) over Scopes : List Nat :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizer(s, 1)
  let _ ← Scopes.addFinalizer(s, 2)
  let _ ← Scopes.remove(s, 1)
  let r ← Scopes.close(s)
  return r

-- The second close runs nothing and answers the empty order.
effect_program scopeCloseTwice (n : Nat) over Scopes : List Nat :=
  let s ← Scopes.make()
  let _ ← Scopes.addFinalizer(s, 1)
  let _ ← Scopes.addFinalizer(s, 2)
  let _ ← Scopes.close(s)
  let r ← Scopes.close(s)
  return r

example : ((interpret scopesLive.toHandler (scopeLifo 0)).run [] : List Nat × ScopeStore).1
    = [3, 2, 1] := rfl
example : ((interpret scopesLive.toHandler (scopeAddAfterClosed 0)).run [] : Bool × ScopeStore).1
    = false := rfl
example : ((interpret scopesLive.toHandler (scopeRemove 0)).run [] : List Nat × ScopeStore).1
    = [2] := rfl
example : ((interpret scopesLive.toHandler (scopeCloseTwice 0)).run [] : List Nat × ScopeStore).1
    = [] := rfl

/-- The traced run of a scope program, with its outcome appended. -/
def scopeGoldenLog {α : Type} [Effects.Trace.ToVal α] (program : Program Scopes.Sig α) :
    Effect4.Trace.Log :=
  let result : (α × Effect4.Trace.Log) × ScopeStore :=
    ((interpret (Scopes.traced scopesLive).toHandler program).run []).run []
  result.1.2 ++ [.done (.success (Effects.Trace.ToVal.toVal result.1.1))]

/-- One scope program: its script and its golden log. -/
structure ScopeEntry where
  name : String
  script : Script
  log : Effect4.Trace.Log

def scopePrograms : List ScopeEntry :=
  [ { name := "lifo", script := scopeLifo.script, log := scopeGoldenLog (scopeLifo 0) }
  , { name := "addAfterClosed", script := scopeAddAfterClosed.script,
      log := scopeGoldenLog (scopeAddAfterClosed 0) }
  , { name := "remove", script := scopeRemove.script, log := scopeGoldenLog (scopeRemove 0) }
  , { name := "closeTwice", script := scopeCloseTwice.script,
      log := scopeGoldenLog (scopeCloseTwice 0) } ]

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
               initial := entry.initial, oracle := some entry.log }
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
          IO.print (← admitted name entry.log
            (Effect4.Target.TypeScript.Trace.golden (name ++ ".empty") []
              ((entry.script.ruleSet entry.rows).map Rule.id) entry.log))
      | none => throw (IO.userError s!"unknown program {name}")
  | ["programs"] => IO.println (String.intercalate "\n" (programs.map (·.name)))
  | ["types"] =>
      for entry in programs do
        IO.println (entry.name ++ "\t" ++ Script.declarationLine entry.rows entry.script)
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
              let boundary := entry.boundaries.find? (·.1 == tapeName)
              match flowLogWith entry tape (boundary.map (·.2.1)) with
              | .ok log =>
                  IO.print (← admitted (name ++ "." ++ tapeName) log
                    (Effect4.Target.TypeScript.Trace.golden (name ++ "." ++ tapeName) tape.wire
                      ((Flow.structuredRuleSet entry.rows entry.program).map Rule.id) log (face := "lean-flow")
                      (budgets := (boundary.map (·.2.2)).getD [])))
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
  | ["scope-fixture"] =>
      -- `Scope` is imported as a type only: the generated module names
      -- `Scope.Closeable` in the service shape and never calls into it.
      match modules? [(Scopes.rows, scopePrograms.map (·.script))] [.types ["Scope"] "effect"] with
      | some source => IO.print source
      | none => throw (IO.userError "lowering refused a scope script")
  | ["scope-programs"] => IO.println (String.intercalate "\n" (scopePrograms.map (·.name)))
  | ["scope-golden", name] =>
      match scopePrograms.find? (·.name == name) with
      | some entry =>
          IO.print (← admitted name entry.log
            (Effect4.Target.TypeScript.Trace.golden ("scope." ++ name) []
              ((entry.script.ruleSet Scopes.rows).map Rule.id) entry.log))
      | none => throw (IO.userError s!"unknown scope program {name}")
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
  | _ => throw (IO.userError "usage: Generate.lean fixture | masks | golden <program> | programs | types | flow-programs | flow-golden <program> <tape> | oracle | flow-fixture | structured-fixture | flow-types | scope-fixture | scope-programs | scope-golden <program> | scope-types | region-frontier | admission-probe")
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
  | _ => throw (IO.userError "usage: Generate.lean fixture | masks | golden <program> | programs | types | flow-programs | flow-golden <program> <tape> | oracle | flow-fixture | structured-fixture | flow-types | scope-fixture | scope-programs | scope-golden <program> | scope-types | admission-probe | frame-trace")
