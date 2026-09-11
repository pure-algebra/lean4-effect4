import Effect4.Program.Admit
import Effect4.Program.Packages
import Effect4.Program.Wire
import Effect4.Codegen.Print
import Effect4.Codegen.Read
import Effect4.Codegen.Schema
import Effect4.Codegen.Target
import Effect4.Store.Cascade
import Effect4.Schema.Bridge
import Effect4.Schema.Endpoint
import Effect4.Schema.Codec
import Effect4.Schema.Image
import Effect4.Schema.Transform

/-!
# Effect4.Api — the application face

One module, the whole pipeline, small interface:

```
 Effect TS text  ⇄  Program (Eff)  →  NCode (rc.112 frames)  →  Machine
   print/read        compile                                     replay / runSync
```

* `Program` is the Eff AST over the native operation alphabet (`src/Effect4/Program/Eff.lean`,
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
* The codegen crossing: `Target` and `Artefact` represent emitted syntax, and `render`
  is the one crossing from an artefact to bytes — admitted by exact name in the gate as
  `Effect4.Codegen.Artefact.render`, and the reason the rest of this face never returns text.

Applications import `Effect4.Api` for programs and data schemas. Batteries test modules
at their own boundaries; `Test/Api/ApiContract.lean` exercises the application seam.
-/

namespace Effect4.Api

open Effect4 Effect4.Machine Effect4.Program

export Effect4.Machine (Val Err Defect Ann Ctx Stores ExitV Stuck RunEvent RunDecision)
export Effect4 (FiberId)
export Effect4.Program (EffName EffThunk)

/-! The value spellings at the application seam: `Val` is the shared carrier
(`Effect4.Store.Val`, U1), so its frames and the runtime's spellings over it
(`Machine/Stores.lean`) are re-exported here, where `Val.nat 42` and `Val.cell ⟨0⟩` read as
before. -/
namespace Val
export Effect4.Store.Val (unit nat bool str bytes list pair ctor ref handle)
export Effect4.Machine.Val (fiber cell promise scopeHandle exitOk exitNil fibers context exitErr
  resultFailure resultSuccess snapshot? context? cause?)
end Val

/-- A program: the Eff AST over the native operation alphabet. -/
abbrev Program := NativeEff

/-! ## Typing and printing -/

/-- The type of a program against the native signature; `none` when ill-typed. Layer
references are resolved first (`Program.typeOfProgram`: well-formed, then expanded to their
targets), so a program with a diamond types as its inlined twin does. -/
def typeOf (program : Program) (table : RowTable := []) : Option EffTy := Program.typeOfProgram (nativeSignature table) program

/-- Whether the program is well-typed. -/
def wellTyped (program : Program) (table : RowTable := []) : Bool := (typeOf program table).isSome

/-- A program's boundary schema document (Decision 12 / S-4): computes the Document for
any well-typed program, refusing when the program is ill-typed. -/
def schemaOf (program : Program) (table : RowTable := []) : Option Effect4.Document :=
  (typeOf program table).map Effect4.Program.EffTy.document

/-- The program as one TypeScript expression, at the empty environment. -/
def print (program : Program) (table : RowTable := []) : Except PrintRefusal TypeScript.Expr :=
  Program.print (nativeSignature table) 0 program

/-- A program back from one TypeScript expression, at the empty environment: the inverse of
`print` on the trees `print` produces (`src/Effect4/Codegen/Read.lean`, `read_print` and
`read_exact`), a `ReadRefusal` on every other tree. -/
def read (expression : TypeScript.Expr) (table : RowTable := []) : Except ReadRefusal Program :=
  Program.readEff (nativeSignature table) (nativeSpell table) 0 expression

/-- Whether the printer keeps the program whole, so that `read` of its printing is the program
itself; what it loses is documented on `Effect4.Program.readable`. -/
def readable (program : Program) (table : RowTable := []) : Bool :=
  Program.readable (nativeSignature table) (nativeSpell table) 0 program

/-- `read` after `print`: the program itself when it is `readable` and the printer accepts
it (`Effect4.Program.roundTrip_eq`), and otherwise the program the printer kept, which prints
the same (`read_exact`). -/
def roundTrip (program : Program) (table : RowTable := []) : Except ReadRefusal Program :=
  Program.roundTrip (nativeSignature table) (nativeSpell table) 0 program

/-! ## Bytes: how a program crosses a boundary -/

/-- The canonical bytes of a program: what the store addresses and what a host is sent
(`Effect4.Program.Wire`). -/
def bytesOf (program : Program) : Store.Bytes := Wire.encodeProgram program

/-- A program from its canonical bytes, exactly: `none` unless the bytes are one
well-formed program and nothing else. Type it with `wellTyped` before running it. -/
def ofBytes (bytes : Store.Bytes) : Option Program := Wire.decodeProgram bytes

/-- The program as an exported constant with its `Effect.Effect<A, E>` type; `none` when it
is ill-typed or the printer refuses it. -/
def printDecl (name : String) (program : Program) (table : RowTable := []) : Option TypeScript.ConstDecl :=
  match typeOf program table, print program table with
  | some ty, Except.ok body => some (Program.printDecl name ty body)
  | _, _ => none

/-- The program as a declaration block: one `const L_<path> = …` per referenced layer target
(the host rows slice, `Program.printModule`), then the exported main constant; `none` when it
is ill-typed or the printer refuses it. The block is what a host must run for a program with
a layer reference: rc.112 keys its memo map on the layer object (`Layer.ts:411`), and the one
`const` is the one object. -/
def printModule (name : String) (program : Program) (table : RowTable := []) : Option TypeScript.Module :=
  match typeOf program table with
  | some ty =>
    match Program.printModule (nativeSignature table) name ty program with
    | Except.ok decls => some { header := [], imports := [], decls := decls.map .const }
    | Except.error _ => none
  | none => none

/-- A program back from a declaration block: the inverse of `printModule` on the blocks it
prints (`Program.readModule`), a `ReadRefusal` on every other. -/
def readModule (module : TypeScript.Module) (table : RowTable := []) : Except ReadRefusal Program :=
  Program.readModule (nativeSignature table) (nativeSpell table) module.decls

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
def load (program : Program) (fuel : Nat) (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Machine :=
  { (RunMachine.empty { Stores.empty with externals := ExternalStore.ofAnswers answers } : Machine) with
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

/-- Replay a host decision tape against the program. **Raw**: this entry point checks
nothing. It does not type the program, does not check the supplied table's names
(`LawfulTable`) and does not check that the runner can register the table's rows
(`checkTable`). The checked entry point is `replayAdmitted`, whose certificate
`admitProgram` builds; `replayChecked` is a different check again — it admits the incoming
*decisions*, not the program. Kept and named for fixtures, negative tests and the truth
driver. -/
def replay (program : Program) (fuel : Nat) (tape : List Decision) (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := []) :
    Run :=
  letI := evaluatorFor program table
  match replayEval (interpOf program table) fuel tape (load program fuel choices answers) with
  | ReplayResult.finished m => ⟨Outcome.finished, m⟩
  | ReplayResult.frontier m => ⟨Outcome.frontier, m⟩
  | ReplayResult.stuck why m => ⟨Outcome.stuck why, m⟩

/-- The decision that starts every run: the root evaluated synchronously. -/
def evaluate : Decision := RunDecision.evaluate root

/-- The decision that drains every armed dispatcher, round after round. -/
def flush : Decision := RunDecision.flush

/-- The ordinary run: evaluate the root, then flush. **Raw**, exactly as `replay` is: no
typing, no table check. `runAdmitted` is the checked one. It also takes no decision tape, so a
program that parks on a clock cannot finish through it — a timed `sleep` needs
`replay … [evaluate, .advance 1, flush]`. -/
def run (program : Program) (fuel : Nat) (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := []) : Run :=
  replay program fuel [evaluate, flush] choices answers table

/-- `Effect.runSyncExit`: the root evaluated on the caller's stack, its dispatcher flushed,
and the `AsyncFiberError` defect when it has not exited. **Raw**, as `run` and `replay` are:
it checks neither the program nor the table. There is no `runSyncAdmitted`; a caller that
wants the certificate builds it with `admitProgram` and keeps it. -/
def runSync (program : Program) (fuel : Nat) (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := []) : Machine × ExitV :=
  letI := evaluatorFor program table
  runSyncExit (interpOf program table) fuel
    (RunMachine.empty { Stores.empty with externals := ExternalStore.ofAnswers answers })
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

/-- The external row and evaluated request at a matching guard token. -/
def requestOf (m : Machine) (fiber : FiberId) (token : Nat) : Option (NativeOp × Val) :=
  Program.requestOf m fiber token

abbrev Refusal := Program.Refusal

/-- Replay with admission. A refusal contains the decision position and the
machine at the refusal; it is separate from the program's exit. -/
def replayChecked (program : Program) (fuel : Nat) (tape : List Decision)
    (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := [])
    (table : RowTable := []) : Run ⊕ (Nat × Decision × Refusal × Machine) :=
  match Program.replayCheckedFrom program fuel answers table 0 tape
      (load program fuel choices answers) with
  | .inr refusal => .inr refusal
  | .inl (.finished m) => .inl ⟨.finished, m⟩
  | .inl (.frontier m) => .inl ⟨.frontier, m⟩
  | .inl (.stuck why m) => .inl ⟨.stuck why, m⟩

/-- The external frontiers after each decision, with their row and request. -/
def replaySteps (program : Program) (fuel : Nat) (tape : List Decision)
    (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := [])
    (table : RowTable := []) : List (Nat × Decision × List Program.Await) :=
  Program.replayStepsFrom program fuel table 0 tape (load program fuel choices answers)

/-! ## Admission: the three checks a run is entitled to (v2 DI-61 (b), (c), (d))

Five different questions are answered by five different checks
(`docs/research/2026-09-09-foundation-admission-boundary.md` §1), and this face keeps them
apart rather than bundling them into one word:

* **typed** — `typeOf` computes an `EffTy`. Since DI-54 that includes operation-domain
  membership, so an external index outside the supplied table no longer types.
* **lawful** — `LawfulTable`: the supplied rows' *names* are unique, do not collide with a
  built-in, drop no trailing name and capture no printed binder.
* **runnable** — `checkTable`: this runner can register every supplied row, i.e. each is
  `(registration := .external, kind := .async)`. Naming lawfulness does not imply it.

`readable` is **not** among them. It means "printing this program and reading it back gives
this program", which is a property of the *print image*, not of execution: the historical wire
program `Wire.Corpus.pAwait` is typed and runs, and is not readable (it spells `perform` on an
async row, which the reader canonicalises to `callback`). Bundling it would have refused the
compatibility case the invocation unification exists for, so it is a separate optional
certificate, `imageCertificate`.

None of this is a completion claim: an admitted program may park at a live frontier, and a
frontier is never a refusal (`AGENTS.md`, representation rules). -/

export Effect4.Program (TableRefusal checkTable)

/-- What `admitProgram` refuses, in the order it checks. -/
inductive AdmitRefusal
  /-- `typeOf` answered `none` against this table. -/
  | illTyped
  /-- `LawfulTable` refused the supplied rows' names. -/
  | unlawfulTable
  /-- This runner cannot register a supplied row, with its position. -/
  | table (why : TableRefusal)
deriving DecidableEq, Repr

/-- A program admitted to run against a table: its type, and the three facts a caller is
entitled to assume. The fields are proofs, so an `AdmittedProgram` cannot be forged by
building the structure with the wrong table — the table and the program are its indices. -/
structure AdmittedProgram (program : Program) (table : RowTable) where
  ty : EffTy
  typed : typeOf program table = some ty
  lawful : LawfulTable table = true
  runnable : checkTable table = none

/-- The decidable admission: the type, the table's names, the table's registrations. No
classical reasoning and no `sorry` — every field is discharged by the evaluation that decided
it. -/
def admitProgram (program : Program) (table : RowTable := []) :
    Except AdmitRefusal (AdmittedProgram program table) :=
  match htyped : typeOf program table with
  | none => .error .illTyped
  | some ty =>
    if hlawful : LawfulTable table = true then
      match hrunnable : checkTable table with
      | some why => .error (.table why)
      | none => .ok ⟨ty, htyped, hlawful, hrunnable⟩
    else .error .unlawfulTable

/-- The print-image certificate, separate from admission on purpose: the proof that this
program survives `print` and `read` unchanged. A program without it still runs.

`PLift` only because `Option` is a `Type` and the certificate is a `Prop`; the proposition
carried is exactly `readable program table = true`, reached as `.down`. -/
def imageCertificate (program : Program) (table : RowTable := []) :
    Option (PLift (readable program table = true)) :=
  if h : readable program table = true then some ⟨h⟩ else none

/-- The checked ordinary run: `run`, with the certificate consumed. -/
def runAdmitted {program : Program} {table : RowTable}
    (admitted : AdmittedProgram program table) (fuel : Nat) (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Run :=
  let _ := admitted.ty
  run program fuel choices answers table

/-- The checked replay: `replay`, with the certificate consumed. The tape is the caller's,
as in `replay`; admission says nothing about which decisions are legal (that is
`replayChecked`) and nothing about finishing. -/
def replayAdmitted {program : Program} {table : RowTable}
    (admitted : AdmittedProgram program table) (fuel : Nat) (tape : List Decision)
    (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Run :=
  let _ := admitted.ty
  replay program fuel tape choices answers table

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

/-! ## Codegen: the targets, artefacts, and rendering to bytes -/

export Effect4.Codegen (Target Artefact)
export Effect4.Codegen.Artefact (render)

/-! ## Multi-Tier Cascading CAS Store -/

export Effect4.Store (CascadingStore)

/-! ## Higher-Order Schema APIs and Functions -/

export Effect4.Schema (Endpoint ApiSpec SchemaFn SchemaTransform
  titleKey descriptionKey documentationKey httpMethodKey httpPathKey deprecatedKey)
export Effect4.Schema (ProgramImage Transform PureMap)

end Effect4.Api
