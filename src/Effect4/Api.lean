import Effect4.Program.Admit
import Effect4.Program.Admission
import Effect4.Program.Table
import Effect4.Program.Typing.Blame
import Effect4.Program.Typing.Agreement
import Effect4.Program.Authoring
import Effect4.Program.Authoring.Lifts
import Effect4.Program.Authoring.Records
import Effect4.Program.Authoring.Maps
import Effect4.Program.Authoring.Tuples
import Effect4.Program.Authoring.Folds
import Effect4.Api.Derived
import Effect4.Program.Packages
import Effect4.Store.Domain.ProgramWire
import Effect4.Store.Domain.Cascade
import Effect4.Schema.Bridge
import Effect4.Schema.OfShape
import Effect4.Schema.Codec

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
  refusal, `Typed` carries a program with its certificate into `Typed.run` and `Typed.runSync`
  under a `Budget` with defaults, and `author` takes a named source
  (`Program.Authoring.Src`) to a `Typed` in one call. `Typed.replay` replays a session's journal
  through the checked session, so it stands beside the session's face
  (`src/Effect4/Run/Live.lean`, decisions row 373 (8)).
* The codegen face is its own module, `Effect4.Api.Codegen` (`src/Effect4/Api/Codegen.lean`),
  in this namespace: `print` and `read`, the round trip and its certificate, `printDecl`, the
  module's emission and its checked reading, the printed `Typed`, `TypedLayer` and `Built`, and the
  Schema syntax. It answers syntax, never text. This module imports none of the codegen, so an
  edit of the printer, the reader, the module writer or their refusal alphabets
  (`src/Effect4/Codegen/Refusal.lean`) rebuilds none of this face's importers. The generated
  `Api/RefusalsDerived.lean` reads those alphabets through the codegen face (decisions row 395
  (5)).
* `bytesOf` / `ofBytes` are the canonical bytes of a program and the exact decoder: what
  the store addresses and what an OCaml or TypeScript host is sent and sends back.
* `compile` is the defunctionalising compile to the frame alphabet; `interpOf` gives the
  names their meaning.
* `replay` runs a program against an explicit host decision tape (the meaning is the
  relation over tapes; a run is its fuel-bounded simulator); `run` is the tape every
  ordinary program takes (evaluate the root, flush its dispatcher); `runSync` is
  `Effect.runSyncExit`. These three are the raw, host-free runs, and `replay` is a named test
  entry (decisions row 373 (8)).
* Host replies reach a program through one route: the keyed session
  `Effect4.Api.HostSession` (`start`, `bindCall`, `submit`, `advance`, `inspect`), which
  binds a reply to the call it answers before the reply becomes a decision (DI-23, DI-58).
  A raw tape answers a parked call by the decision `answerAsync` alone; no run entry takes a
  list of answers, and a host call always parks (DI-23).

Applications import the root `Effect4`, which imports this face and its codegen face. Batteries
test modules at their own boundaries; `Test/Api/ApiContract.lean` exercises the application seam.
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
layer references resolved as `typeOf` resolves them. The facade refuses an ill-formed reference
at its site, the first in program order, with the condition it breaks (`Eff.firstRefFault`,
decisions row 341). Where the references are well formed, it answers the whole module's refusal
of the expansion (`Checker.checkModule`, decisions row 328): the structural checker's refusal
for a program with no block (`Program.explain`). The expansion has no reference site
(`expanded_refs_nil_of_wf`, `Laws/Program/ReferenceExpansion.lean`), so no arm answers for one
(decisions row 273). `none` exactly when the program is `wellTyped` (`Api.explain_none_iff`,
below). -/
def explain (program : Program) (table : RowTable := []) : Option Effect4.Program.TypeRefusal :=
  match program.firstRefFault with
  | some (site, target, why) => some ⟨site, .referenceIllFormed target why⟩
  | none =>
    Effect4.Program.Checker.refusal
      (Effect4.Program.Checker.checkModule (nativeSignature table) program.expandRefs)

/-- The path of the refusal alone: the deepest node whose own rule refuses. -/
def blame (program : Program) (table : RowTable := []) : Option (List Nat) :=
  (explain program table).map (·.path)

/-- The facade's refusal is the checker's (DI-86): `explain` answers `none` exactly when the
program is `wellTyped`, the layer references resolved the same way on both sides. Both sides
test the references' formation (`Eff.firstRefFault_eq_none`). Where it holds, both sides read
the one module check of the expansion, its refusal and its success. Where it fails, the facade
refuses at the reference and the program is not `wellTyped`. The proof uses no law of the proof
graph. -/
theorem explain_none_iff (program : Program) (table : RowTable) :
    explain program table = none ↔ wellTyped program table = true := by
  unfold explain wellTyped typeOf Program.typeOfProgram
  cases h : program.firstRefFault with
  | none =>
    rw [if_pos ((Program.Eff.firstRefFault_eq_none program).mp h)]
    show Program.Checker.refusal _ = none ↔ Option.isSome (Except.toOption _) = true
    cases Program.Checker.checkModule (nativeSignature table) program.expandRefs with
    | ok _ => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | error _ => exact ⟨nofun, nofun⟩
  | some f =>
    obtain ⟨site, target, why⟩ := f
    have hwf : program.layerRefsWF = false := by
      cases hw : program.layerRefsWF with
      | false => rfl
      | true =>
        rw [(Program.Eff.firstRefFault_eq_none program).mpr hw] at h
        cases h
    rw [hwf]
    exact ⟨nofun, nofun⟩

theorem blame_none_iff (program : Program) (table : RowTable) :
    blame program table = none ↔ wellTyped program table = true := by
  simp [blame, ← explain_none_iff]

/-! ## Bytes: how a program crosses a boundary -/

/-- The canonical bytes of a program: what the store addresses and what a host is sent
(`Effect4.Program.Wire`). -/
def bytesOf (program : Program) : Store.Bytes := Wire.encodeProgram program

/-- A program from its canonical bytes, exactly: `none` unless the bytes are one
well-formed program and nothing else. Type it with `wellTyped` before running it. -/
def ofBytes (bytes : Store.Bytes) : Option Program := Wire.decodeProgram bytes

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
def load (program : Program) (compileFuel : Nat) : Machine :=
  { (RunMachine.empty Stores.empty : Machine) with
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
(`checkTable`). It admits no host answer: an `answerAsync` on the tape reaches the machine as
written.

**A named test entry** (decisions row 373 (8)), kept for fixtures, negative tests, the truth
driver and the laws of the machine. The checked route is `Typed.replay`
(`src/Effect4/Run/Live.lean`): it replays a session's journal, and the session admits each reply
at its call. `replayChecked` is a different check again: it admits the incoming *decisions* at
the rows' own columns, not the program. -/
def replay (program : Program) (fuel : Nat) (tape : List Decision) (table : RowTable := [])
    (compileFuel : Nat := fuel) :
    Inspection :=
  letI := evaluatorFor program table
  match replayEval (interpOf program table) fuel tape (load program compileFuel) with
  | ReplayResult.finished m => ⟨Outcome.finished, m, []⟩
  | ReplayResult.frontier why m => ⟨Outcome.frontier, m, frontierReasons why m⟩
  | ReplayResult.stuck why m => ⟨Outcome.stuck why, m, []⟩

/-- Completeness of this tape observation at explicit command and compile budgets.
It excludes outstanding host replies and a missing scheduling decision: a runnable fiber
or an armed owner (decisions row 201 (b)). Timers and exhaustion remain observable, and
this predicate does not assert termination. -/
def Tape.Complete (program : Program) (table : RowTable) (tape : List Decision)
    (fuel : Nat) (compileFuel : Nat := fuel) : Prop :=
  let reasons := (replay program fuel tape table compileFuel).reasons
  (∀ key, FrontierReason.awaitHost key ∉ reasons) ∧ FrontierReason.awaitDecision ∉ reasons

/-- The decision that starts every run: the root evaluated synchronously. -/
def evaluate : Decision := RunDecision.evaluate root

/-- The decision that drains every armed dispatcher, round after round. -/
def flush : Decision := RunDecision.flush

/-- The ordinary run: evaluate the root, then flush. **Raw**, exactly as `replay` is: no
typing, no table check. `runAdmitted` is the checked one. It also takes no decision tape, so a
program that parks on a clock cannot finish through it — a timed `sleep` needs
`replay … [evaluate, .advance 1, flush]`. -/
def run (program : Program) (fuel : Nat) (table : RowTable := [])
    (compileFuel : Nat := fuel) : Inspection :=
  replay program fuel [evaluate, flush] table compileFuel

/-- `Effect.runSyncExit`: the root evaluated on the caller's stack, its dispatcher flushed,
and the `AsyncFiberError` defect when it has not exited. **Raw**, as `run` and `replay` are:
it checks neither the program nor the table. There is no `runSyncAdmitted`; a caller that
wants the certificate builds it with `admitProgram` and keeps it. A host call parks and this
entry answers none, so a root that waits on its host ends with that defect. -/
def runSync (program : Program) (fuel : Nat) (table : RowTable := [])
    (compileFuel : Nat := fuel) : Machine × ExitV :=
  letI := evaluatorFor program table
  runSyncExit (interpOf program table) fuel (RunMachine.empty Stores.empty)
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

/-- Static malformed input has no decision position. A dynamic refusal retains
its actual decision and the machine at that point. Neither is a program exit. -/
inductive ReplayCheckRefusal where
  | formation (why : Program.Formation.Refusal)
  | decision (position : Nat) (input : Decision) (why : Refusal) (machine : Machine)

/-- Check raw formation, then replay with the existing decision admission checks. -/
def replayChecked (program : Program) (fuel : Nat) (tape : List Decision)
    (table : RowTable := []) : Inspection ⊕ ReplayCheckRefusal :=
  match Program.Formation.checkInput program table with
  | some why => .inr (.formation why)
  | none =>
    match Program.replayCheckedFrom program fuel table 0 tape (load program fuel) with
    | .inr (position, input, why, machine) => .inr (.decision position input why machine)
    | .inl (.finished m) => .inl ⟨.finished, m, []⟩
    | .inl (.frontier why m) => .inl ⟨.frontier, m, frontierReasons why m⟩
    | .inl (.stuck why m) => .inl ⟨.stuck why, m, []⟩

/-- The external frontiers after each decision, with their row and request. -/
def replaySteps (program : Program) (fuel : Nat) (tape : List Decision)
    (table : RowTable := []) : List (Nat × Decision × List Program.Await) :=
  Program.replayStepsFrom program fuel table 0 tape (load program fuel)

/-! ## Admission: execution checks and reserved integer refusal

Five different questions are answered by five different checks
(`docs/research/2026-09-09-foundation-admission-boundary.md` §1), and this face keeps them
apart. Admission is at an application's signature (`SigApp`, decisions row 21); a caller with a
row table alone admits at `⟨table, []⟩`, whose signature is `nativeSignature table`. The
execution certificate retains the following checks:

* **typed** — the checker computes an `EffTy` at `app.signature`. Since DI-54 that includes
  operation-domain membership, so an external index outside the supplied table no longer types.
* **signature** — `admitSig`: the supplied rows' keys are unique, collide with no built-in and
  drop no trailing name; this runner can register every row, i.e. each is
  `(registration := .external, kind := .async)`; every row's columns are lawful and its template
  admissible; every service declaration is lawful; and every key a row requires has a carrier.
  Naming lawfulness does not imply registration, and neither implies a carrier. `checkTable`
  answers the registration question alone, with the first position it refuses.

P2a additionally scans every raw table type and both inferred program columns for
`int`. Successful admission records both negative scan results in its certificate;
a refusal identifies the exact constructor path.

`readable` is **not** among them. It means "printing this program and reading it back gives
this program", which is a property of the *print image*, not of execution: a program can be
typed and run and still not be one the printer keeps whole (a loop whose stated cursor type is
outside the readable types, `Codegen.Classes.ReadableTy`: a cursor at a cell's type prints, and
no reading answers its spelling). Admission certifies execution and `readable` certifies
reconstruction, so it is a separate optional certificate, `imageCertificate` (`src/Effect4/Api/Codegen.lean`). (The example this paragraph once gave,
`Wire.Corpus.pAwait`, became readable when `callback` retired into `perform`.)

None of this is a completion claim: an admitted program may park at a live frontier, and a
frontier is never a refusal (`AGENTS.md`, representation rules). -/

export Effect4.Program (TableRefusal checkTable rowKey SigApp SigRefusal RowReason ServiceReason
  admitSig AdmittedProgram AdmitRefusal admitProgram admitProgram_signature Path
  AdmittedStraightProgram StraightAdmitRefusal admitStraightProgram)

namespace Table
export Effect4.Program.Table (lawful)
end Table

/-- The checked ordinary run: `run`, with the certificate consumed. The certificate is at the
table's own signature, `⟨table, []⟩`; a run at declared services is the Σ_app slice's step 3. -/
def runAdmitted {program : Program} {table : RowTable}
    (admitted : AdmittedProgram program ⟨table, []⟩) (fuel : Nat)
    (compileFuel : Nat := fuel) : Inspection :=
  let _ := admitted.ty
  run program fuel table compileFuel

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

/-- `run` on the certified program: evaluate the root, flush. -/
def run (t : Typed table) (budget : Budget := {}) : Inspection :=
  Api.run t.program budget.fuel table budget.compileFuel

/-- `Effect.runSyncExit` on the certified program: the exit alone. -/
def runSync (t : Typed table) (budget : Budget := {}) : ExitV :=
  (Api.runSync t.program budget.fuel table budget.compileFuel).2

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
scope, then checked, the type or the located refusal (`Checker.checkLayer`, an `Except`); the
certificate is the agreement `checkLayer_eq`. -/
def checkLayer (l : Effect4.Program.Authoring.LayerSrc NativeOp) (table : RowTable := [])
    (sig : Signature NativeOp := nativeSignature table) :
    Except AuthorRefusal (TypedLayer sig) :=
  match Effect4.Program.Authoring.elaborateLayer l with
  | .error refusal => .error (.scope refusal)
  | .ok layer =>
    match h : Effect4.Program.Checker.checkLayer sig [] layer with
    | .error refusal => .error (.typing refusal)
    | .ok ty => .ok ⟨layer, ty, congrArg Except.toOption h⟩

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

end TypedLayer

/-! ## Multi-Tier Cascading CAS Store -/

export Effect4.Store (CascadingStore)

end Effect4.Api
