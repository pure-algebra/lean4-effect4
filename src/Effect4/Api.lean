import Effect4.Program.Admit
import Effect4.Program.Admission
import Effect4.Program.Table
import Effect4.Program.Typing.Blame
import Effect4.Program.Authoring
import Effect4.Api.Derived
import Effect4.Program.Packages
import Effect4.Program.Wire
import Effect4.Codegen.Print
import Effect4.Codegen.Checked
import Effect4.Codegen.SourceBindings
import Effect4.Codegen.Read
import Effect4.Codegen.Admit
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
* `typeOf` / `wellTyped` type a program against the native signature; `explain` / `blame`
  locate and name a refusal (DI-86).
* Certificate first (DI-85): `check` answers the typing certificate or the located, named
  refusal, `Typed` carries a program with its certificate into `Typed.run`, `Typed.replay`,
  `Typed.runSync` and `Typed.emit` under a `Budget` with defaults, and `author` takes a named
  source (`Program.Authoring.Src`) to a `Typed` in one call.
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
  `Effect.runSyncExit`. These three are the raw, host-free runs.
* Host replies reach a program through one route: the keyed session
  `Effect4.Api.HostSession` (`start`, `bindCall`, `submit`, `advance`, `inspect`), which
  binds a reply to the call it answers before the reply becomes a decision (DI-23, DI-58).
  The `answers` list `load`, `replay`, `run` and `runSync` still accept is the legacy route
  the session replaces; it stays only until the truth corpus runs on keyed tapes (DI-23's
  amendment), and nothing new should use it.
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

/-- Compute the shared typing certificate without the runner's registration checks.
The result refers to this exact program and table; declarations use the same evidence. -/
def checkTyping (program : Program) (table : RowTable := []) :
    Option (Effect4.Program.TypedProgram (nativeSignature table) program) :=
  Effect4.Program.checkTypedProgram (nativeSignature table) program

/-- Whether the program is well-typed. -/
def wellTyped (program : Program) (table : RowTable := []) : Bool := (typeOf program table).isSome

/-- Where and why a program fails to type (DI-86): the checker's refusal, with the program's
layer references resolved as `typeOf` resolves them (an ill-formed reference is refused at the
root, a reference that survives expansion at its site). `none` exactly when the program is
`wellTyped` (`Api.explain_none_iff`, below). -/
def explain (program : Program) (table : RowTable := []) : Option Effect4.Program.TypeRefusal :=
  if program.layerRefsWF then
    match program.expandRefs.refSites [] with
    | (site, target) :: _ => some ⟨site, .layerReference target⟩
    | [] => Effect4.Program.explain (nativeSignature table) [] program.expandRefs
  else some ⟨[], .referencesIllFormed⟩

/-- The path of the refusal alone: the deepest node whose own rule refuses. -/
def blame (program : Program) (table : RowTable := []) : Option (List Nat) :=
  (explain program table).map (·.path)

/-- The facade's refusal is the checker's (DI-86): `explain` answers `none` exactly when the
program is `wellTyped`, the layer references resolved the same way on both sides. -/
theorem explain_none_iff (program : Program) (table : RowTable) :
    explain program table = none ↔ wellTyped program table = true := by
  unfold explain wellTyped typeOf Program.typeOfProgram Program.typeOf
  split
  · split <;> simp_all [Program.explain_none_iff]
  · simp_all

theorem blame_none_iff (program : Program) (table : RowTable) :
    blame program table = none ↔ wellTyped program table = true := by
  simp [blame, ← explain_none_iff]

/-- A program's boundary schema document (Decision 12 / S-4): computes the Document for
any well-typed program, refusing when the program is ill-typed. -/
def schemaOf (program : Program) (table : RowTable := []) : Option Effect4.Document :=
  (typeOf program table).map Effect4.Program.EffTy.document

/-- The program as one TypeScript expression, at the empty environment. -/
def print (program : Program) (table : RowTable := []) : Except PrintRefusal TypeScript.Expr :=
  Program.print (nativeSignature table) 0 program

/-- A program back from one TypeScript expression, at the empty environment: read through the
table the printer prints from (`src/Effect4/Codegen/Read.lean`, `readT`), a `ReadRefusal` on a
tree no row matches. A row is accepted only when the printer would choose it for what was
read, so what is read prints back to the tree read (guarded on the corpus; the theorem over the
table is owed, R5.2). -/
def read (expression : TypeScript.Expr) (table : RowTable := []) : Except ReadRefusal Program :=
  Program.readEff (nativeSignature table) (nativeSpell table) 0 expression

/-- `read`, with where a refusal happened: the path of constructors and argument indices down to
the node that refused, and, when a reserved head matched no row, what the nearest row's skeleton
has where the tree parts from it (`Effect4.Program.ReadFailure`; `.render` for a person). -/
def readAt (expression : TypeScript.Expr) (table : RowTable := []) :
    Except Program.ReadFailure Program :=
  Program.readEffAt (nativeSignature table) (nativeSpell table) 0 expression

/-- Whether `read` of the program's printing is the program itself: the round trip, decided by
running it. What the printer loses is listed in `Codegen/Read.lean`'s module note (a variable
out of scope, a dropped `unit` request, the `daemon` flag of a scoped fork, a loop's cursor
annotation, the internal fiber actions). -/
def readable (program : Program) (table : RowTable := []) : Bool :=
  Program.readable (nativeSignature table) (nativeSpell table) 0 program

/-- `read` after `print`: the program itself exactly when it is `readable`
(`Effect4.Program.roundTrip_eq`), and otherwise the program the printer kept. -/
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
  match checkTyping program table, print program table with
  | some typing, Except.ok body => (Program.printDecl name typing.ty body).toOption
  | _, _ => none

/-- The program as a declaration block: one `const L_<path> = …` per referenced layer target
(the host rows slice, `Program.printModule`), then the exported main constant; `none` when it
is ill-typed or the printer refuses it. The block is what a host must run for a program with
a layer reference: rc.112 keys its memo map on the layer object (`Layer.ts:411`), and the one
`const` is the one object. -/
def printModule (name : String) (program : Program) (table : RowTable := []) : Option TypeScript.Module :=
  ((Effect4.Codegen.emitModule name program table).toOption).map (·.module)

/-- The module together with its core typing and exact production receipt. Consumers
that need the proof connection retain this result; `printModule` projects its syntax.
This does not validate source imports or establish target typing/execution. -/
def emitModule (name : String) (program : Program) (table : RowTable := []) :
    Except Effect4.Codegen.EmissionRefusal (Effect4.Codegen.ModuleEmission program table name) :=
  Effect4.Codegen.emitModule name program table

/-- Raw reconstruction from a declaration block. This recovers programs in the
printer's readable image, but ignores imports, outer annotations and export names.
Use `checkTyping` on the recovered program for core typing; that check alone does
not validate the original source envelope. -/
def readModule (module : TypeScript.Module) (table : RowTable := []) : Except ReadRefusal Program :=
  Program.readModule (nativeSignature table) (nativeSpell table) module.decls

/-- Check imports and lexical bindings on the original module, retaining its exact
syntax in the certificate's index. The caller supplies permitted import origins.
This is a prerequisite of typed source admission: it does not check annotation
agreement, resolve package exports or validate the origin expected by a core head. -/
def checkSourceBindings (module : TypeScript.Module)
    (allowed : List Effect4.Codegen.Bindings.Origin) :
    Option (Effect4.Codegen.SourceBindings.Checked allowed module) :=
  Effect4.Codegen.SourceBindings.validate allowed module

/-- Checked reading of a declaration block, the boundary `readModule` is the raw half of.
It checks four things and keeps all four: the original module's imports and lexical bindings
against the permitted origins (with a host's `ambient` prelude prepended), the raw
reconstruction of the program, the one whole-program type checker, and the declaration
envelope — a safe export name, the last declaration exported under that name and annotated
exactly as `printDecl` annotates the checked type, and every earlier declaration a plain
exported layer constant.

What it does **not** check. It does not widen a declared type: the comparison is equality
with the printer's own annotation, because the core has no subsumption at a program's top
type. It admits no binder, return or local annotation; the raw reader still refuses those.
It gives the `effect` package no meaning: a resolved `Effect` is a lexical fact, not
evidence that the host's namespace is the pinned one. It is neither target type checking
nor execution. -/
def admitModule (name : String) (module : TypeScript.Module) (table : RowTable := [])
    (allowed : List Effect4.Codegen.Bindings.Origin := Effect4.Codegen.effectOrigins)
    (ambient : List TypeScript.Import := []) :
    Except Effect4.Codegen.SurfaceRefusal
      (Effect4.Codegen.ModuleReading table name allowed ambient) :=
  Effect4.Codegen.admitModule name module table allowed ambient

/-! ## Compiling and running -/

/-- The compiled root: the program as a primitive of the frame alphabet, at `fuel`. -/
def compile (program : Program) (fuel : Nat) : NCode :=
  Program.compile program fuel

/-- The machine and the host decisions at the compile's alphabet. -/
abbrev Machine := RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev Decision := RunDecision EffName EffThunk Val Err Defect FiberId Ann

/-- The root fiber of a loaded program. -/
def root : FiberId := ⟨0⟩

/-- A fresh machine over the empty stores and the empty context, holding the compiled
program as its root fiber, not yet evaluated. -/
def load (program : Program) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Machine :=
  { (RunMachine.empty { Stores.empty with externals := ExternalStore.ofAnswers answers } : Machine) with
    fibers := [RunFiber.make root (compile program compileFuel) true
      (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }

/-- How a replay ended: every fiber exited; the tape or the fuel ran out first (a live
frontier, never a failure); or the machine reached a state rc.112 cannot. -/
inductive Outcome
  | finished
  | frontier
  | stuck (why : Stuck)
deriving DecidableEq, Repr

/-- What a replay is read as: its outcome, final machine and live frontier reasons. (`Run`,
`src/Effect4/Run.lean`, is the value a caller holds while a built program runs; this is the
reading `Run.inspect` takes of it.) -/
structure Inspection where
  outcome : Outcome
  machine : Machine
  reasons : List FrontierReason

/-- Replay a host decision tape against the program. **Raw**: this entry point checks
nothing. It does not type the program, does not check the supplied table's names
(`LawfulTable`) and does not check that the runner can register the table's rows
(`checkTable`). The checked entry point is `replayAdmitted`, whose certificate
`admitProgram` builds; `replayChecked` is a different check again — it admits the incoming
*decisions*, not the program. Kept and named for fixtures, negative tests and the truth
driver. -/
def replay (program : Program) (fuel : Nat) (tape : List Decision)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := [])
    (compileFuel : Nat := fuel) :
    Inspection :=
  letI := evaluatorFor program table
  match replayEval (interpOf program table) fuel tape (load program compileFuel answers) with
  | ReplayResult.finished m => ⟨Outcome.finished, m, []⟩
  | ReplayResult.frontier why m => ⟨Outcome.frontier, m, frontierReasons why m⟩
  | ReplayResult.stuck why m => ⟨Outcome.stuck why, m, []⟩

/-- Completeness of this tape observation at explicit command and compile budgets.
It excludes outstanding host replies and a missing runnable decision; timers and
exhaustion remain observable and this predicate does not assert termination. -/
def Tape.Complete (program : Program) (table : RowTable) (tape : List Decision)
    (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := [])
    (compileFuel : Nat := fuel) : Prop :=
  let reasons := (replay program fuel tape answers table compileFuel).reasons
  (∀ key, FrontierReason.awaitHost key ∉ reasons) ∧ FrontierReason.awaitDecision ∉ reasons

/-- The decision that starts every run: the root evaluated synchronously. -/
def evaluate : Decision := RunDecision.evaluate root

/-- The decision that drains every armed dispatcher, round after round. -/
def flush : Decision := RunDecision.flush

/-- The ordinary run: evaluate the root, then flush. **Raw**, exactly as `replay` is: no
typing, no table check. `runAdmitted` is the checked one. It also takes no decision tape, so a
program that parks on a clock cannot finish through it — a timed `sleep` needs
`replay … [evaluate, .advance 1, flush]`. -/
def run (program : Program) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := [])
    (compileFuel : Nat := fuel) : Inspection :=
  replay program fuel [evaluate, flush] answers table compileFuel

/-- `Effect.runSyncExit`: the root evaluated on the caller's stack, its dispatcher flushed,
and the `AsyncFiberError` defect when it has not exited. **Raw**, as `run` and `replay` are:
it checks neither the program nor the table. There is no `runSyncAdmitted`; a caller that
wants the certificate builds it with `admitProgram` and keeps it. -/
def runSync (program : Program) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (table : RowTable := [])
    (compileFuel : Nat := fuel) : Machine × ExitV :=
  letI := evaluatorFor program table
  runSyncExit (interpOf program table) fuel
    (RunMachine.empty { Stores.empty with externals := ExternalStore.ofAnswers answers })
    (compile program compileFuel) emptyCtx

/-- The root's exit; `none` while it is still live. -/
def Inspection.exit (r : Inspection) : Option ExitV := (r.machine.fiber? root).bind RunFiber.exit

/-- Every event the machine recorded, in order. -/
def Inspection.trace (r : Inspection) :
    List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx) :=
  r.machine.trace

/-- The stores the run left behind. -/
def Inspection.stores (r : Inspection) : Stores := r.machine.state

/-- How many fibers the run created, the root included. -/
def Inspection.fiberCount (r : Inspection) : Nat := r.machine.fibers.length

/-- The external row and evaluated request at a matching guard token. -/
def requestOf (m : Machine) (fiber : FiberId) (token : Nat) : Option (NativeOp × Val) :=
  Program.requestOf m fiber token

abbrev Refusal := Program.Refusal

/-- Replay with admission. A refusal contains the decision position and the
machine at the refusal; it is separate from the program's exit. -/
def replayChecked (program : Program) (fuel : Nat) (tape : List Decision)

    (answers : List (Completion Val Err Defect FiberId Ann) := [])
    (table : RowTable := []) : Inspection ⊕ (Nat × Decision × Refusal × Machine) :=
  match Program.replayCheckedFrom program fuel answers table 0 tape
      (load program fuel answers) with
  | .inr refusal => .inr refusal
  | .inl (.finished m) => .inl ⟨.finished, m, []⟩
  | .inl (.frontier why m) => .inl ⟨.frontier, m, frontierReasons why m⟩
  | .inl (.stuck why m) => .inl ⟨.stuck why, m, []⟩

/-- The external frontiers after each decision, with their row and request. -/
def replaySteps (program : Program) (fuel : Nat) (tape : List Decision)

    (answers : List (Completion Val Err Defect FiberId Ann) := [])
    (table : RowTable := []) : List (Nat × Decision × List Program.Await) :=
  Program.replayStepsFrom program fuel table 0 tape (load program fuel answers)

/-! ## Admission: execution checks and reserved integer refusal

Five different questions are answered by five different checks
(`docs/research/2026-09-09-foundation-admission-boundary.md` §1), and this face keeps them
apart. The execution certificate retains the following three checks:

* **typed** — `typeOf` computes an `EffTy`. Since DI-54 that includes operation-domain
  membership, so an external index outside the supplied table no longer types.
* **lawful** — `LawfulTable`: the supplied rows' *names* are unique, do not collide with a
  built-in, drop no trailing name and capture no printed binder.
* **runnable** — `checkTable`: this runner can register every supplied row, i.e. each is
  `(registration := .external, kind := .async)`. Naming lawfulness does not imply it.

P2a additionally scans every raw table type and both inferred program columns for
`int`. Successful admission records both negative scan results in its certificate;
a refusal identifies the exact constructor path.

`readable` is **not** among them. It means "printing this program and reading it back gives
this program", which is a property of the *print image*, not of execution: a program can be
typed and run and still not be one the printer keeps whole (a loop whose cursor is annotated:
no reader of types exists). Admission certifies execution and `readable` certifies reconstruction, so it is a
separate optional certificate, `imageCertificate`. (The example this paragraph once gave,
`Wire.Corpus.pAwait`, became readable when `callback` retired into `perform`.)

None of this is a completion claim: an admitted program may park at a live frontier, and a
frontier is never a refusal (`AGENTS.md`, representation rules). -/

export Effect4.Program (TableRefusal checkTable rowKey AdmittedProgram AdmitRefusal admitProgram
  admitProgram_table_int admitProgram_program_int admitProgram_type_int Path findInt findIntInTable
  findIntInProgram findIntInEffTy
  AdmittedStraightProgram StraightAdmitRefusal admitStraightProgram)

namespace Table
export Effect4.Program.Table (lawful checkLawful LawfulRefusal)
end Table

/-- The print-image certificate, separate from admission on purpose: the proof that this
program survives `print` and `read` unchanged. A program without it still runs.

`PLift` only because `Option` is a `Type` and the certificate is a `Prop`; the proposition
carried is exactly `readable program table = true`, reached as `.down`. -/
def imageCertificate (program : Program) (table : RowTable := []) :
    Option (PLift (readable program table = true)) :=
  if h : readable program table = true then some ⟨h⟩ else none

/-- The checked ordinary run: `run`, with the certificate consumed. -/
def runAdmitted {program : Program} {table : RowTable}
    (admitted : AdmittedProgram program table) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := [])
    (compileFuel : Nat := fuel) : Inspection :=
  let _ := admitted.ty
  run program fuel answers table compileFuel

/-- The checked replay: `replay`, with the certificate consumed. The tape is the caller's,
as in `replay`; admission says nothing about which decisions are legal (that is
`replayChecked`) and nothing about finishing. -/
def replayAdmitted {program : Program} {table : RowTable}
    (admitted : AdmittedProgram program table) (fuel : Nat) (tape : List Decision)

    (answers : List (Completion Val Err Defect FiberId Ann) := [])
    (compileFuel : Nat := fuel) : Inspection :=
  let _ := admitted.ty
  replay program fuel tape answers table compileFuel

/-! ## Certificate first (DI-85)

A program is checked once; what runs, prints or emits afterwards takes the certificate, not the
raw program. `check` is total by `explain_none_iff`: no program is refused without a located
reason. `author` is the agent's one call from a named source. -/

/-- A program with its typing certificate against a table. -/
structure Typed (table : RowTable) where
  program : Program
  certificate : Effect4.Program.TypedProgram (nativeSignature table) program

/-- Certificate first: the checker's evidence, or its located and named refusal (DI-86). -/
def check (program : Program) (table : RowTable := []) :
    Except Effect4.Program.TypeRefusal (Typed table) :=
  match h : explain program table with
  | some refusal => .error refusal
  | none =>
    match h2 : Program.typeOfProgram (nativeSignature table) program with
    | some ty => .ok ⟨program, ⟨ty, h2⟩⟩
    | none => absurd ((explain_none_iff program table).mp h) (by simp [wellTyped, typeOf, h2])

/-- The command and compile budgets of a run; the defaults are the truth corpus's. -/
structure Budget where
  fuel : Nat := 1000
  compileFuel : Nat := 1000
deriving DecidableEq, Repr

namespace Typed

variable {table : RowTable}

/-- The certified type. -/
def ty (t : Typed table) : EffTy := t.certificate.ty

/-- `replay` on the certified program. -/
def replay (t : Typed table) (tape : List Decision) (budget : Budget := {}) : Inspection :=
  Api.replay t.program budget.fuel tape [] table budget.compileFuel

/-- `run` on the certified program: evaluate the root, flush. -/
def run (t : Typed table) (budget : Budget := {}) : Inspection :=
  Api.run t.program budget.fuel [] table budget.compileFuel

/-- `Effect.runSyncExit` on the certified program: the exit alone. -/
def runSync (t : Typed table) (budget : Budget := {}) : ExitV :=
  (Api.runSync t.program budget.fuel [] table budget.compileFuel).2

/-- The printed syntax of the certified program. -/
def print (t : Typed table) : Except PrintRefusal TypeScript.Expr := Api.print t.program table

/-- The certified module emission under a declaration name. -/
def emit (t : Typed table) (name : String) :
    Except Effect4.Codegen.EmissionRefusal (Effect4.Codegen.ModuleEmission t.program table name) :=
  Api.emitModule name t.program table

/-- The canonical bytes: the program's identity for a store and a host. -/
def bytes (t : Typed table) : Store.Bytes := bytesOf t.program

end Typed

/-- Why an authored source is refused: at a name (the scope reader's refusal at its path) or
at a type (the checker's located refusal). -/
inductive AuthorRefusal
  | scope (refusal : Effect4.Program.Authoring.Refusal)
  | typing (refusal : Effect4.Program.TypeRefusal)
deriving DecidableEq

/-- The agent's one call: a named source elaborated at the empty scope, then checked. -/
def author (src : Effect4.Program.Authoring.Src NativeOp) (table : RowTable := []) :
    Except AuthorRefusal (Typed table) :=
  match Effect4.Program.Authoring.elaborate src with
  | .error refusal => .error (.scope refusal)
  | .ok program => (check program table).mapError .typing

/-- `author` for a module with shared layers by name. -/
def authorModule (m : Effect4.Program.Authoring.Module NativeOp) (table : RowTable := []) :
    Except AuthorRefusal (Typed table) :=
  match Effect4.Program.Authoring.elaborateModule m with
  | .error refusal => .error (.scope refusal)
  | .ok program => (check program table).mapError .typing

/-! ## The environment as data

What a program needs of its surroundings, and what a layer gives one, are both computed by
the type system (`EffTy.requires`, `LayerTy`) and were reachable from neither this face nor
an author. They are projections of a certificate, so they cost one line each, and they are
what lets an agent read a composition before running anything. -/

namespace Typed

variable {table : RowTable}

/-- The full keys this program performs against, in the canonical key order. -/
def requires (t : Typed table) : List ServiceKey := t.ty.requires.elems

/-- Whether the program needs nothing of its surroundings: `Effect<A, E, never>`. -/
def closed (t : Typed table) : Bool := t.ty.requires == Effect4.Machine.Env.Requirement.empty

end Typed

/-- A layer with its signature: what it provides, its error column, what it still needs
(`LayerTy`, `Layer<ROut, E, RIn>`). A layer could be written before this and neither checked
nor printed on its own: `Authoring.elaborate` took a program, and the first error in a layer
a library shipped surfaced when some program provided it. -/
structure TypedLayer (sig : Signature NativeOp) where
  layer : LayerTerm NativeOp
  ty : LayerTy
  ok : Effect4.Program.layerTy sig layer = some ty

/-- The agent's one call for a layer, as `author` is for a program: elaborated at the empty
scope, then typed, with the checker's located refusal when it does not type. Total, by
`explainLayer_none_iff`: no layer is refused without a reason at a path. -/
def checkLayer (l : Effect4.Program.Authoring.LayerSrc NativeOp) (table : RowTable := [])
    (sig : Signature NativeOp := nativeSignature table) :
    Except AuthorRefusal (TypedLayer sig) :=
  match Effect4.Program.Authoring.elaborateLayer l with
  | .error refusal => .error (.scope refusal)
  | .ok layer =>
    match h : Effect4.Program.layerTy sig layer with
    | some ty => .ok ⟨layer, ty, h⟩
    | none =>
      match h2 : Effect4.Program.explainLayer sig [] layer with
      | some refusal => .error (.typing refusal)
      | none =>
        absurd ((Effect4.Program.explainLayer_none_iff sig layer []).mp h2) (by simp [h])

namespace TypedLayer

variable {sig : Signature NativeOp}

/-- The keys the layer provides, in the canonical key order. -/
def provides (l : TypedLayer sig) : List ServiceKey := l.ty.out.elems

/-- The keys the layer still needs before it can be built. -/
def requires (l : TypedLayer sig) : List ServiceKey := l.ty.requires.elems

/-- Whether the layer needs nothing of its surroundings: a deployment that is complete
(`LayerTy.Closed`). A merge of two siblings where one meant to feed the other is exactly the
layer whose `requires` is not empty, which is why this is worth reading before a program
exists. -/
def closed (l : TypedLayer sig) : Bool :=
  l.ty.requires == Effect4.Machine.Env.Requirement.empty

/-- The printed layer (`Codegen.Templates.printLayerT`, the printer's own fold). -/
def print (l : TypedLayer sig) : Except PrintRefusal TypeScript.Expr :=
  Effect4.Codegen.Templates.printLayerT sig l.layer

end TypedLayer

/-- The printed layer, as `print` is for a program. -/
def printLayer {sig : Signature NativeOp} (l : TypedLayer sig) :
    Except PrintRefusal TypeScript.Expr := l.print

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
