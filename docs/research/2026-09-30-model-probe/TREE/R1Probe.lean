import Effect4.Laws.Program.Typed.Assembly
import Effect4.Api.Author

/-!
# Seat TREE, R1 probe: the typed-state source with a service table

Research probe (docs/research/2026-09-30-model-probe/TREE). Nothing here is imported by the tree.

* §A `Source`: `ProgramSource` with a service table beside the row table, typed by
  `nativeSignatureWith` (`Program/Authoring/Services.lean:49`). Connector: at the empty service
  list it is the old source (`rfl`).
* §B design B: the service table as a parameter of the value judgments (`ServicesOk` and
  everything that reads it through `HandlesFit`'s context arm). Connectors to the tree's
  judgments at `nativeServiceTy`.
* §C `PointTyped`, `BodyTyped`, and the M5 obligation restated over `Source`.
* §D admission over the source's signature, beside `admitProgram`; the seventh carrier is
  refused by the tree's admission and admitted by this one (tested).
* §E the term typer reads only atoms; that it is unchanged by the move is proved in R2Probe §A
  (not `rfl`).
-/

set_option autoImplicit false

namespace Effect4.Program.Typed.TreeProbeR1

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Program.Denote

/-! ## §A The source -/

/-- The program the typed state is about, with both tables its checker reads. -/
structure Source where
  program : NativeEff
  table : RowTable := []
  services : List (ServiceKey × Ty) := []

/-- The source's signature: rows and services threaded side by side. -/
def Source.sig (src : Source) : Signature NativeOp := nativeSignatureWith src.table src.services

/-- The tree's source is a source with no service table. -/
def Source.ofProgramSource (src : ProgramSource) : Source :=
  { program := src.program, table := src.table }

theorem Source.sig_ofProgramSource (src : ProgramSource) :
    (Source.ofProgramSource src).sig = nativeSignature src.table := rfl

/-- The row half of the signature does not see the service table. -/
theorem Source.sig_rowOf (src : Source) : src.sig.rowOf = (nativeSignature src.table).rowOf := rfl
theorem Source.sig_dom (src : Source) : src.sig.dom = (nativeSignature src.table).dom := rfl
theorem Source.sig_atomOf (src : Source) : src.sig.atomOf = (nativeSignature src.table).atomOf := rfl
theorem Source.sig_scopeKey (src : Source) :
    src.sig.scopeKey = (nativeSignature src.table).scopeKey := rfl

/-! ## §B Design B: the service table is a parameter of the value judgments -/

/-- `ServicesOk` (Typed/Admission.lean:32-34) with the static service table supplied. -/
def ServicesOkB (sty : ServiceKey → Option Ty) (w : World) (services : Env.Ctx) : Prop :=
  ∀ key sv ty, services.getV key = some sv → sty key = some ty →
    ValueOk w ty sv ∧ HandlesLive w sv

/-- `HandlesFit` (Typed/Admission.lean:39-58), its context arm reading the supplied table. -/
def HandlesFitB (sty : ServiceKey → Option Ty) (w : World) (v : Val) (ty : Ty) : Prop :=
  match ty with
  | .refOf t => ∀ key, Handle.cell key ∈ v.keys → w.Ρ key = some t
  | .deferredOf a e => ∀ key, Handle.promise key ∈ v.keys → w.«Π» key = some (a, e)
  | .fiberOf a e => ∀ id, Handle.fiber id ∈ v.keys → ∃ fty, w.Γ id = some fty ∧
      fty.answer.sub a = true ∧ fty.error.sub e = true
  | .prod a b => match v with
    | .pair v1 v2 => HandlesFitB sty w v1 a ∧ HandlesFitB sty w v2 b
    | _ => True
  | .option a => match v with
    | .some v1 => HandlesFitB sty w v1 a
    | _ => True
  | .list a => match v with
    | .list vs => ∀ x ∈ vs, HandlesFitB sty w x a
    | _ => True
  | .union a b => HandlesFitB sty w v a ∨ HandlesFitB sty w v b
  | .unknown => HandlesLive w v
  | .handle s => s = Ty.contextTarget → ∀ ctx, Val.context? v = some ctx →
      ServicesOkB sty w ctx.services
  | _ => True

def StrongValueB (sty : ServiceKey → Option Ty) (w : World) (ty : Ty) (v : Val) : Prop :=
  ValueOk w ty v ∧ HandlesFitB sty w v ty ∧ HandlesLive w v

def StrongCauseB (sty : ServiceKey → Option Ty) (w : World) (errTy : Ty) (c : CauseV) : Prop :=
  ∀ r ∈ c.reasons, match r with
  | .fail e _ => ∃ v, valOfErr e = some v ∧ StrongValueB sty w errTy v
  | .die _ _ | .interrupt _ _ => True

def StrongExitB (sty : ServiceKey → Option Ty) (w : World) (ty : EffTy) (ex : ExitV) : Prop :=
  ExitFits w ty ex ∧
  (∀ v, ex = .success v → StrongValueB sty w ty.answer v) ∧
  (∀ c, ex = .failure c → StrongCauseB sty w ty.error c)

def EnvTypedB (sty : ServiceKey → Option Ty) (w : World) (env : List Ty) (vals : List Val) : Prop :=
  env.length = vals.length ∧
  ∀ (i : Nat) (ty : Ty) (v : Val), env[i]? = some ty → vals[i]? = some v → StrongValueB sty w ty v

/-! Connectors: at the built-in table the parameterized judgments are the tree's. -/

theorem servicesOkB_native (w : World) (services : Env.Ctx) :
    ServicesOkB nativeServiceTy w services ↔ ServicesOk w services := Iff.rfl

theorem handlesFitB_native (w : World) (ty : Ty) :
    ∀ v, HandlesFitB nativeServiceTy w v ty ↔ HandlesFit w v ty := by
  induction ty with
  | prod a b iha ihb =>
    intro v
    cases v <;> simp only [HandlesFitB, HandlesFit]
    case pair v1 v2 => exact and_congr (iha v1) (ihb v2)
  | option a iha =>
    intro v
    cases v <;> simp only [HandlesFitB, HandlesFit]
    case some v1 => exact iha v1
  | list a iha =>
    intro v
    cases v <;> simp only [HandlesFitB, HandlesFit]
    case list vs => exact forall_congr' fun x => imp_congr_right fun _ => iha x
  | union a b iha ihb =>
    intro v
    exact or_congr (iha v) (ihb v)
  | _ => intro v; exact Iff.rfl

theorem strongValueB_native (w : World) (ty : Ty) (v : Val) :
    StrongValueB nativeServiceTy w ty v ↔ StrongValue w ty v :=
  and_congr Iff.rfl (and_congr (handlesFitB_native w ty v) Iff.rfl)

theorem envTypedB_native (w : World) (env : List Ty) (vals : List Val) :
    EnvTypedB nativeServiceTy w env vals ↔ EnvTyped w env vals :=
  and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun ty => forall_congr' fun v =>
    imp_congr_right fun _ => imp_congr_right fun _ => strongValueB_native w ty v)

/-! ## §C The typed-state source admission over `Source` -/

/-- `PointTyped` (Typed/Admission.lean:92-96) at the source's whole signature. -/
def PointTypedB (src : Source) (w : World) (point : Point) (ty : EffTy) : Prop :=
  ∃ (e : NativeEff) (env : List Ty),
    Node.at_ (.eff src.program) point.path = some (.eff e) ∧
    Checker.check src.sig env point.path e = .ok ty ∧
    EnvTypedB src.sig.serviceTy w env point.env

/-- `BodyTyped` (Typed/Admission.lean:99-111) over `Source`. -/
inductive BodyTypedB (src : Source) (w : World) : Body → EffTy → Prop
  | at_ (p : Point) (ty : EffTy) (h : PointTypedB src w p ty) :
      BodyTypedB src w (.at_ p) ty
  | fin (name : FinName) (ex : ExitV) (ty : EffTy) (hex : StrongExitB src.sig.serviceTy w ty ex) :
      BodyTypedB src w (.fin name ex) ty
  | raceCleanup (race : Nat) :
      BodyTypedB src w (.raceCleanup race) (EffTy.pure .unit)
  | acquireIn (p : Point) (ctx : Ctx) (ty : EffTy) (h : PointTypedB src w p ty) :
      BodyTypedB src w (.acquireIn p ctx) ty
  | release (p : Point) (prev : Ctx) (ty : EffTy) (h : PointTypedB src w p ty) :
      BodyTypedB src w (.release p prev) ty
  | layerBuild (p : Point) (m : MemoMapId) (scope : Nat) (ty : EffTy) (h : PointTypedB src w p ty) :
      BodyTypedB src w (.layerBuild p m scope) ty

/-- At the empty service list the new judgment is the tree's (`nativeSignatureWith_nil`). -/
theorem pointTypedB_ofProgramSource (src : ProgramSource) (w : World) (point : Point)
    (ty : EffTy) : PointTypedB (Source.ofProgramSource src) w point ty ↔ PointTyped src w point ty := by
  constructor
  · rintro ⟨e, env, hat, hcheck, henv⟩
    exact ⟨e, env, hat, hcheck, (envTypedB_native w env point.env).mp henv⟩
  · rintro ⟨e, env, hat, hcheck, henv⟩
    exact ⟨e, env, hat, hcheck, (envTypedB_native w env point.env).mpr henv⟩

/-- The M5 obligation (`typedState_load`, Assembly.lean:148-150) with its typing premise over the
source's signature. `Api.typeOf root.program root.table` is `typeOfProgram (nativeSignature
root.table) root.program` (Api.lean:96); over `Source` it is the source's own signature. The
conclusion still names the tree's `TypedState`, which takes a `ProgramSource`: under design B
that predicate is re-instantiated over `Source` (not done here, see the note §2). -/
theorem typedState_load_premise_shape (root : Source) (rootTy : EffTy) :
    ProofGraph.Obligation (typeOfProgram root.sig root.program = some rootTy → ClosedEff rootTy →
      True) := ⟨⟩

theorem typeOf_premise_ofProgramSource (src : ProgramSource) :
    typeOfProgram (Source.ofProgramSource src).sig src.program = Api.typeOf src.program src.table :=
  rfl

/-! ## §D Admission over the source's signature -/

/-- `AdmittedProgram` (Program/Admission.lean:89-95) with the service table as an index. -/
structure AdmittedProgramB (program : NativeEff) (table : RowTable)
    (services : List (ServiceKey × Ty))
    extends TypedProgram (nativeSignatureWith table services) program where
  lawful : Table.lawful table = true
  runnable : checkTable table = none
  intFreeTable : findIntInTable table = none
  intFreeProgram : findIntInProgram program = none
  intFreeType : findIntInEffTy ty = none

/-- `admitProgram` (Program/Admission.lean:100-123) with the one typing call moved to the
source's signature; every other check is the tree's. -/
def admitProgramB (program : NativeEff) (table : RowTable := [])
    (services : List (ServiceKey × Ty) := []) :
    Except AdmitRefusal (AdmittedProgramB program table services) :=
  match htable : findIntInTable table with
  | some pos => .error (.uninhabited pos)
  | none =>
    match hprogram : findIntInProgram program with
    | some pos => .error (.uninhabited pos)
    | none =>
    match checkTypedProgram (nativeSignatureWith table services) program with
    | none => .error .illTyped
    | some typing =>
      match htype : findIntInEffTy typing.ty with
      | some pos => .error (.uninhabited pos)
      | none =>
        if hlawful : Table.lawful table = true then
          match hrunnable : checkTable table with
          | some why => .error (.table why)
          | none => .ok ⟨typing, hlawful, hrunnable, htable, hprogram, htype⟩
        else .error (.duplicateKey ("", []))

/-- A certificate over the empty service list is a certificate of the tree's admission, and
back: the two structures carry the same fields at the same signature. -/
def AdmittedProgramB.toTree {program : NativeEff} {table : RowTable}
    (a : AdmittedProgramB program table []) : AdmittedProgram program table :=
  ⟨a.toTypedProgram, a.lawful, a.runnable, a.intFreeTable, a.intFreeProgram, a.intFreeType⟩

def AdmittedProgramB.ofTree {program : NativeEff} {table : RowTable}
    (a : AdmittedProgram program table) : AdmittedProgramB program table [] :=
  ⟨a.toTypedProgram, a.lawful, a.runnable, a.intFreeTable, a.intFreeProgram, a.intFreeType⟩

theorem AdmittedProgramB.toTree_ofTree {program : NativeEff} {table : RowTable}
    (a : AdmittedProgram program table) : (AdmittedProgramB.ofTree a).toTree = a := rfl

/-- The application's own service of the coordinator's demo (`scratchpad/demo/ServiceDemo.lean`):
a string carrier under a key the six type codes do not spell. -/
def greetKey : ServiceKey := ⟨⟨12⟩, ⟨12⟩⟩
def greetServices : List (ServiceKey × Ty) := [(greetKey, .string)]

/-- Read the service, closed by providing it: `Effect.provideService(Greeting.use, k, "hello")`. -/
def greetProgram : NativeEff :=
  .provideService greetKey (.lit (.str "hello")) (.service greetKey)

-- tested: the tree's typing and admission refuse the seventh carrier
#guard Api.typeOf greetProgram [] = none
#guard (match admitProgram greetProgram [] with
  | .error .illTyped => true
  | _ => false)
#guard (match Api.check greetProgram [] with
  | .error r => r == ⟨[], .serviceUnknown greetKey⟩
  | .ok _ => false)
-- tested: over the source's signature it types and admits, closed, answering `string`
#guard typeOfProgram (nativeSignatureWith [] greetServices) greetProgram =
  some ⟨.string, .never, Env.Requirement.empty⟩
#guard (match admitProgramB greetProgram [] greetServices with
  | .ok a => a.ty == ⟨.string, .never, Env.Requirement.empty⟩
  | .error _ => false)
-- tested: the open read alone requires its key
#guard typeOfProgram (nativeSignatureWith [] greetServices) (.service greetKey) =
  some ⟨.string, .never, Env.Requirement.single greetKey⟩

/-- The demo's service declaration: the key and its string carrier, no operations. -/
def greetDef : Effect4.Program.Authoring.ServiceDef := { key := greetKey, carrier := .string }

-- tested: building refuses the seventh carrier before typing (`disagreeingService`,
-- Api/Author.lean:46-50), naming the signature's answer `none`
#guard (match Api.Author.build
    { services := [greetDef], main := Effect4.Program.Authoring.ServiceDef.use greetDef } with
  | .error (.serviceCarrier k d sig) => k == greetKey && d == .string && sig == none
  | _ => false)
-- tested: the module already carries the table R1 needs (`Module.serviceTypes`,
-- Program/Authoring.lean:332-333)
#guard ({ services := [greetDef], main := Effect4.Program.Authoring.ServiceDef.use greetDef } :
    Effect4.Program.Authoring.Module NativeOp).serviceTypes = greetServices

/-! ## §E The term typer reads atoms only

Not `rfl`: `termTy (nativeSignatureWith t s) env x = termTy (nativeSignature t) env x` fails to
elaborate as `rfl` (tested, `R1Probe-run1.log`). It is proved by induction on terms
in `R2Probe.lean` §A (`argTy_congr`, `termTy_congr`, `causeTy_congr`). -/

end Effect4.Program.Typed.TreeProbeR1

#print axioms Effect4.Program.Typed.TreeProbeR1.Source.sig_ofProgramSource
#print axioms Effect4.Program.Typed.TreeProbeR1.Source.sig_rowOf
#print axioms Effect4.Program.Typed.TreeProbeR1.servicesOkB_native
#print axioms Effect4.Program.Typed.TreeProbeR1.handlesFitB_native
#print axioms Effect4.Program.Typed.TreeProbeR1.strongValueB_native
#print axioms Effect4.Program.Typed.TreeProbeR1.envTypedB_native
#print axioms Effect4.Program.Typed.TreeProbeR1.pointTypedB_ofProgramSource
#print axioms Effect4.Program.Typed.TreeProbeR1.typedState_load_premise_shape
#print axioms Effect4.Program.Typed.TreeProbeR1.typeOf_premise_ofProgramSource
#print axioms Effect4.Program.Typed.TreeProbeR1.AdmittedProgramB.toTree_ofTree
