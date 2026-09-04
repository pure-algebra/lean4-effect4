import Effect4.Program.Compile
import Effect4.Program.Wire
import Effect4.Codegen.Print
import Effect4.Codegen.Schema

/-!
# Effect4.Api — the application face

One module, the whole pipeline, small interface:

```
 Effect TS text  ⇄  Program (Eff)  →  NCode (rc.112 frames)  →  Deep machine
   print/read        compile                                     replay / runSync
```

* `Program` is the Eff AST over the native operation alphabet (`Effect4/Syntax/Eff.lean`,
  `Native.lean`): first-order, decidable, no Lean function inside.
* `typeOf` / `wellTyped` type a program against the native signature.
* `print` / `printDecl` answer TypeScript **syntax** (`TypeScript.Expr`, `ConstDecl`),
  never text. Rendering to bytes is one call to the pinned package — `TypeScript.Render.expr
  house0 0 e` — kept outside this module on purpose: Lean's `String` folds reach
  `Classical.choice`, and this module stays at the library's axiom ceiling.
* `bytesOf` / `ofBytes` are the canonical bytes of a program and the exact decoder: what
  the store addresses and what an OCaml or TypeScript host is sent and sends back.
* `compile` is the defunctionalising compile to the frame alphabet; `interpOf` gives the
  names their meaning.
* `replay` runs a program against an explicit host decision tape (the meaning is the
  relation over tapes; a run is its fuel-bounded simulator); `run` is the tape every
  ordinary program takes (evaluate the root, flush its dispatcher); `runSync` is
  `Effect.runSyncExit`.
* The Schema half: a persisted document or representation as its `Schema.Struct({…})`
  syntax (`schemaDocument`, `schemaRepresentation`) and the JSON payload beside it
  (`jsonExpr`). Text generation with its module assembler is
  `Effect4.Codegen.Schema.generate?`, admitted by exact name in the axiom gate.

Everything else in the library is implementation behind this seam. Callers and tests cross
it the same way; `Test/Api/ApiContract.lean` is the receipt.
-/

namespace Effect4.Api

open Effect4 Effect4.Machine Effect4.Program

/-- A program: the Eff AST over the native operation alphabet. -/
abbrev Program := NativeEff

/-! ## Typing and printing -/

/-- The type of a program against the native signature; `none` when ill-typed. -/
def typeOf (program : Program) : Option EffTy := Program.typeOf nativeSignature program

/-- Whether the program is well-typed. -/
def wellTyped (program : Program) : Bool := (typeOf program).isSome

/-- The program as one TypeScript expression, at the empty environment. -/
def print (program : Program) : Except PrintRefusal TypeScript.Expr :=
  Program.print nativeSignature 0 program

/-! ## Bytes: how a program crosses a boundary -/

/-- The canonical bytes of a program: what the store addresses and what a host is sent
(`Effect4.Program.Wire`). -/
def bytesOf (program : Program) : Store.Bytes := Wire.encodeProgram program

/-- A program from its canonical bytes, exactly: `none` unless the bytes are one
well-formed program and nothing else. Type it with `wellTyped` before running it. -/
def ofBytes (bytes : Store.Bytes) : Option Program := Wire.decodeProgram bytes

/-- The program as an exported constant with its `Effect.Effect<A, E>` type; `none` when it
is ill-typed or the printer refuses it. -/
def printDecl (name : String) (program : Program) : Option TypeScript.ConstDecl :=
  match typeOf program, print program with
  | some ty, Except.ok body => some (Program.printDecl name ty body)
  | _, _ => none

/-! ## Compiling and running -/

/-- The compiled root: the program as a primitive of the frame alphabet, at `fuel` with the
`choose` decisions on `choices`. -/
def compile (program : Program) (fuel : Nat) (choices : List Bool := []) : NCode :=
  Program.compile program fuel choices

/-- The machine and the host decisions at the compile's alphabet. -/
abbrev Machine := RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev Decision := RunDecision EffName EffThunk Val Err Defect FiberId Ann

/-- The root fiber of a loaded program. -/
def root : FiberId := ⟨0⟩

/-- A fresh machine over the empty stores and the empty context, holding the compiled
program as its root fiber, not yet evaluated. -/
def load (program : Program) (fuel : Nat) (choices : List Bool := []) : Machine :=
  { (RunMachine.empty Stores.empty : Machine) with
    fibers := [RunFiber.make root (compile program fuel choices) true
      (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }

/-- How a replay ended: every fiber exited; the tape or the fuel ran out first (a live
frontier, never a failure); or the machine reached a state rc.112 cannot. -/
inductive Outcome
  | finished
  | frontier
  | stuck (why : Stuck)
deriving DecidableEq, Repr

/-- A run: how it ended and the machine it ended in. -/
structure Run where
  outcome : Outcome
  machine : Machine

/-- Replay a host decision tape against the program. -/
def replay (program : Program) (fuel : Nat) (tape : List Decision) (choices : List Bool := []) :
    Run :=
  match replayEval (interpOf program) fuel tape (load program fuel choices) with
  | ReplayResult.finished m => ⟨Outcome.finished, m⟩
  | ReplayResult.frontier m => ⟨Outcome.frontier, m⟩
  | ReplayResult.stuck why m => ⟨Outcome.stuck why, m⟩

/-- The decision that starts every run: the root evaluated synchronously. -/
def evaluate : Decision := RunDecision.evaluate root

/-- The decision that drains every armed dispatcher, round after round. -/
def flush : Decision := RunDecision.flush

/-- The ordinary run: evaluate the root, then flush. -/
def run (program : Program) (fuel : Nat) (choices : List Bool := []) : Run :=
  replay program fuel [evaluate, flush] choices

/-- `Effect.runSyncExit`: the root evaluated on the caller's stack, its dispatcher flushed,
and the `AsyncFiberError` defect when it has not exited. -/
def runSync (program : Program) (fuel : Nat) (choices : List Bool := []) : Machine × ExitV :=
  runSyncExit (interpOf program) fuel (RunMachine.empty Stores.empty)
    (compile program fuel choices) emptyCtx

/-- The root's exit; `none` while it is still live. -/
def Run.exit (r : Run) : Option ExitV := (r.machine.fiber? root).bind RunFiber.exit

/-- Every event the machine recorded, in order. -/
def Run.trace (r : Run) : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx) :=
  r.machine.trace

/-- The stores the run left behind. -/
def Run.stores (r : Run) : Stores := r.machine.state

/-- How many fibers the run created, the root included. -/
def Run.fiberCount (r : Run) : Nat := r.machine.fibers.length

/-! ## Schema, as syntax -/

/-- A persisted Schema document as its `Schema.Struct({…})` Program. -/
def schemaDocument (document : Effect4.Document) : TypeScript.Expr :=
  Effect4.Codegen.Schema.documentExpr document

/-- A persisted representation as its Schema Program. -/
def schemaRepresentation (representation : Effect4.Representation) : TypeScript.Expr :=
  Effect4.Codegen.Schema.representation representation

/-- A JSON payload as a TypeScript literal. -/
def jsonExpr (value : Effect4.Json) : TypeScript.Expr :=
  Effect4.Codegen.Schema.json value

end Effect4.Api
