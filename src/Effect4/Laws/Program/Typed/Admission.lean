import Effect4.Laws.Program.Typed.RecordOperations
import Effect4.Program.Checker
import Effect4.Laws.Program.Sched
import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.ReferenceTyping

/-!
# Laws.Program.Typed.Admission — source and control admission for typed programs

D13 source admission (checking paths and environments against the checker) before protocol
contracts, using the value membership judgments from `Typed/Membership.lean`. The shared exit
judgment also excludes `badName` and `notImplemented`; clean failures require that explicit
exclusion premise. `missingService` remains admitted in part one. Control admission (FR-09) is an
arm of the one program judgment `TypedProg` in `Typed/Residual.lean` (ruling 2026-09-23).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

/-- Part one excludes only `badName` and `notImplemented`. The type argument is retained
for the shared exit interface; `missingService` remains admitted pending part two. -/
def NoShapeDefect (_ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure cause => ∀ reason ∈ cause.reasons, match reason with
    | .die defect _ => defect ≠ .badName ∧ defect ≠ .notImplemented
    | _ => True

/-- Base membership and the part-one defect exclusion at every typed exit position. -/
def ExitOk (w : World) (ty : EffTy) (ex : ExitV) : Prop :=
  FitsExit w ty ex ∧ NoShapeDefect ty ex

/-- Part one's exclusion on a failure is `ShapeFree` on its cause, the predicate membership at an
exit type reads (decisions row 152). -/
theorem noShapeDefect_failure_iff (ty : EffTy) (c : CauseV) :
    NoShapeDefect ty (.failure c) ↔ ShapeFree c := Iff.rfl

/-- Part one: an interrupt reason carries neither excluded defect. -/
theorem noShapeDefect_of_interrupts (ty : EffTy) (cause : CauseV)
    (interrupts : ∀ reason ∈ cause.reasons, reason.tag = .interrupt) :
    NoShapeDefect ty (.failure cause) := by
  intro reason member
  have tag := interrupts reason member
  cases reason with
  | fail _ _ => trivial
  | die _ _ => cases tag
  | interrupt _ _ => trivial

/-- Removing Fail reasons does not introduce a shape defect. -/
theorem noShapeDefect_stripFail (ty : EffTy) (cause : CauseV)
    (shape : NoShapeDefect ty (.failure cause)) :
    NoShapeDefect ty (.failure cause.stripFail) := by
  intro reason member
  exact shape reason ((Cause.mem_stripFail reason cause).mp member).1

/-- Combine contains only reasons from its two inputs. -/
theorem noShapeDefect_combine (ty : EffTy) (left right : CauseV)
    (leftShape : NoShapeDefect ty (.failure left))
    (rightShape : NoShapeDefect ty (.failure right)) :
    NoShapeDefect ty (.failure (Cause.combine left right)) := by
  intro reason member
  rcases (Cause.mem_combine reason left right).mp member with fromLeft | fromRight
  · exact leftShape reason fromLeft
  · exact rightShape reason fromRight

/-- Sanitization strips Fail reasons and combines the remaining original reasons with
recorded interruption reasons; exclusion is required of both inputs. -/
theorem noShapeDefect_sanitize (ty : EffTy) (cause interrupted : CauseV)
    (shape : NoShapeDefect ty (.failure cause))
    (interruptShape : NoShapeDefect ty (.failure interrupted)) :
    NoShapeDefect ty (.failure (Cause.sanitize cause interrupted)) :=
  noShapeDefect_combine ty cause.stripFail interrupted
    (noShapeDefect_stripFail ty cause shape) interruptShape

/-- An evaluation environment typed pointwise at the corresponding static types. -/
def EnvTyped (w : World) (env : List Ty) (vals : List Val) : Prop :=
  env.length = vals.length ∧
  ∀ (i : Nat) (ty : Ty) (v : Val), env[i]? = some ty → vals[i]? = some v → Fits w v ty

/-- **Term soundness for membership (TY-07, proved)**, in the environment judgment the typed
state reads (`PointTyped`): under a signature whose atoms are the native table's (every
`nativeSignature`, every source signature), a term that types in a typed environment and
evaluates there evaluates to a value of the term's type. The proof is `evalTerm_fitsAll`
(`Typed/Membership.lean`) through `fitsAll_of_pointwise`. -/
theorem evalTerm_fits {sig : Signature NativeOp} (hatom : sig.atomOf = nativeAtomTy)
    (hconst : sig.constAtom = nativeConstAtom) {w : World} {env : List Ty} {vals : List Val}
    {t : Term} {ty : Ty} {v : Val} (henv : EnvTyped w env vals)
    (hty : termTy sig env t = some ty) (hev : evalTerm vals t = some v) : Fits w v ty :=
  evalTerm_fitsAll sig hatom hconst w t vals env ty v (fitsAll_of_pointwise henv.1 henv.2) hty hev

/-- `evalTerm_fits` at a native signature over any row table. -/
theorem evalTerm_fits_native (table : RowTable) {w : World} {env : List Ty} {vals : List Val}
    {t : Term} {ty : Ty} {v : Val} (henv : EnvTyped w env vals)
    (hty : termTy (nativeSignature table) env t = some ty) (hev : evalTerm vals t = some v) :
    Fits w v ty :=
  evalTerm_fits rfl rfl henv hty hev

/-- The program the typed state is about, with its signature (decisions row 111: the host-row
table and the service declarations, Σ_app) and the evidence that the signature is lawful
(row 114: M5 and M6 quantify over lawful sources, not over an authoring guard's callers). A
bare program coerces to a source with the empty signature, which is lawful
(`SigApp.lawful_empty`). -/
structure ProgramSource where
  program : NativeEff
  table : RowTable := []
  services : List (ServiceKey × Ty) := []
  lawful : LawfulSig ⟨table, services⟩ := by exact SigApp.lawful_empty

instance : Coe NativeEff ProgramSource := ⟨fun program => { program }⟩

/-- The source's part of the signature. -/
def ProgramSource.sig (src : ProgramSource) : SigApp := ⟨src.table, src.services⟩

/-- The checker's signature over the source's tables; with no service declarations it is
`nativeSignature src.table` (`SigApp.signature_nil`). -/
def ProgramSource.signature (src : ProgramSource) : Signature NativeOp := src.sig.signature

/-- D13 source admission at an addressed program node, under the source's signature: its row
table (`E4-SCHED-CE-014`: the empty table refused bodies that perform a host row) and its service
declarations (rows 111–114; `src.signature` is `nativeSignature src.table` for a source with no
declarations, `SigApp.signature_nil`). The node is the program's as written, the one the run
denotes; the checker reads it through the rounds of the program's expansion (`Eff.expandIn`,
decisions row 153 (b)): the checker refuses a layer reference (`Program/Checker.lean:259`) and
certifies a program with references as its expansion (`typeOfProgram`), while the run hops from a
reference to its target (`denoteLayer_ref_redirect`). For a reference-free node the expansion is
the node itself (`Eff.expandIn_eq_self`).

The point's data is its environment and its completed view, both typed at the world (decisions
row 175, `E4-TYPED-CE-021`): the values in scope fit the checker's environment (`EnvTyped`), and
each completed exit the point carries fits its fiber's declared type, the `construction` post's
clause (`Typed/Residual.lean`), which is where a point's view is built. The denotation answers a
completed exit as an `await`'s result (`Point.awaitExit`), so an untyped view denotes an untyped
program at a checked node. -/
def PointTyped (src : ProgramSource) (w : World) (point : Point) (ty : EffTy) : Prop :=
  ∃ (e : NativeEff) (env : List Ty),
    Node.at_ (.eff src.program) point.path = some (.eff e) ∧
    Checker.check src.signature env point.path (Eff.expandIn src.program e) = .ok ty ∧
    EnvTyped w env point.env ∧
    ∀ q ∈ point.completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2

/-- A capture's release is admitted: its path addresses an `acquireRelease` the checker types
under an environment its values fit, extended by the acquired value, and its context's
services are typed. The checker reads the node through the expansion's rounds, as `PointTyped`
does (decisions row 153 (b)). Here since decisions row 151 (a″): the scope registration's pre
reads it (`FinalizerAdmitted`, `Typed/Admission.lean`), as the generated bundle's `CaptureOk` does
(`preds`, `Typed/Assembly.lean`). -/
def CaptureTyped (root : ProgramSource) (w : World) (c : Capture) : Prop :=
  ∃ (acquire release : NativeEff) (env : List Ty) (t a : EffTy),
    Node.at_ (.eff root.program) c.path = some (.eff (.acquireRelease acquire release)) ∧
    Checker.check root.signature env c.path
      (Eff.expandIn root.program (.acquireRelease acquire release)) = .ok t ∧
    Checker.check root.signature env (c.path ++ [0]) (Eff.expandIn root.program acquire) = .ok a ∧
    EnvTyped w (env ++ [a.answer]) c.env ∧ ServicesFit w c.ctx.services

/-- A layer point is admitted (decisions row 186 (a)): its path addresses a layer the checker
types, read through the expansion's rounds as `PointTyped` reads a program node and as the memo
rows read the memo layer (`storePre`'s `memoGet` arm, `Typed/Residual.lean`); its lexical
environment is the empty one a layer is checked and built in (`Point.layerBuild`, decisions rows
104, 105), and its completed view is typed as `PointTyped`'s is. `PointTyped` admits only a
program node, so a layer build's point needs its own admission. -/
def LayerPointTyped (src : ProgramSource) (w : World) (point : Point) (lt : LayerTy) : Prop :=
  ∃ l : LayerTerm NativeOp,
    Node.at_ (.eff src.program) point.path = some (.layer l) ∧
    Checker.checkLayer src.signature point.path (LayerTerm.expandIn src.program l) = .ok lt ∧
    point.env = [] ∧
    ∀ q ∈ point.completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2

/-- **A finalizer the scope registration admits** (decisions row 151 (a″)): what makes its program
typed at rc.112's finalizer type `⟨unknown, never⟩` (`internal/effect.ts:3849`) at every later
world, read by name, since the pre cannot mention the program judgment it is a premise of. A
foreign finalizer's capture is typed (`CaptureTyped`: what the checker gives an
`acquireRelease`, whose release is declared `Effect<unknown, never, R2>`, `:3973`); a `release`
does not fail (a failing one answers a typed failure, which no `never` error column admits); a
finalizer that closes or detaches a scope names a present one. Every other name is typed by its
program alone. The bridge to the typing is `finalizerTyped_of_admitted` (`Typed/Assembly.lean`).
Read by the scope registration's pre (`storePre`, `Typed/Residual.lean`) and by a finalizer body's
admission (`BodyTyped.fin`). -/
def FinalizerAdmitted (root : ProgramSource) (w : World) : FinName → Prop
  | .foreign c => CaptureTyped root w c
  | .release _ fails => fails = false
  | .closeChildScope scope | .closeChildOnFailure scope => ScopeLive w scope
  | .detachFromParent parent _ => ScopeLive w parent
  -- the target's interrupt row demands it (finding F-PRE); `link` registers a fiber the machine holds
  | .interruptFiber fiber _ => (w.Γ fiber).isSome = true
  | .awaitNewChildren _ | .parkThen _ | .memoEntry _ _ => True
  -- `memoMapBuild`'s `onExit` (`Layer.ts:414-417`), never a scope's finalizer: its exit is the
  -- construction's, which `memoComplete`'s pre types at the layer's columns (decisions row 187)
  | .memoDone _ _ => False

/-- **Admitted bodies**, one arm per `Body` constructor, each what its program needs (`bodyR`,
`Laws/Program/EvaluateR.lean`; the bridge is `bodyTyped_typed`, `Typed/Body.lean`): the pre of
`mask` and `fork` (`fiberPre`, `Typed/Residual.lean`).

- A body at a point is the point's admission (`PointTyped`).
- A finalizer body is its admission by name (`FinalizerAdmitted`) at a closing exit that fits rc.112's
  release parameter type `Exit<unknown, unknown>`, and runs at the finalizer type `⟨unknown, never⟩`
  (`E4-TYPED-CE-039`: admitting it at any type its exit fits typed a program the finalizer never
  runs; no producer of `Body.fin` exists in the tree).
- `acquireRelease`'s masked half (`acquireInR`) names its node and a context whose services fit: the
  release's registration reads both (`CaptureTyped`), and the acquire runs at the node's child 0.
- A capture's release restores a context whose services fit (`setContext`'s pre).
- A layer's build runs into a present scope and a present memo map (`layerBuild_typed` reads both,
  `Typed/LayerArm.lean`; the memo map is installed into the built context, finding F-WF) at the
  build's types: the built context at the layer's checked error (`buildTy`). -/
inductive BodyTyped (src : ProgramSource) (w : World) : Body → EffTy → Prop
  | at_ (p : Point) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.at_ p) ty
  | fin (name : FinName) (ex : ExitV) (h : FinalizerAdmitted src w name)
      (hex : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex) :
      BodyTyped src w (.fin name ex) ⟨.unknown, .never, Env.Requirement.empty⟩
  | raceCleanup (race : Nat) :
      BodyTyped src w (.raceCleanup race) (EffTy.pure .unit)
  | acquireIn (p : Point) (ctx : Ctx) (ty : EffTy) (h : PointTyped src w p ty)
      (node : ∃ acquire release : NativeEff,
        Node.at_ (.eff src.program) p.path = some (.eff (.acquireRelease acquire release)))
      (services : ServicesFit w ctx.services) :
      BodyTyped src w (.acquireIn p ctx) ty
  | release (p : Point) (prev : Ctx) (ty : EffTy) (h : PointTyped src w p ty)
      (services : ServicesFit w prev.services) :
      BodyTyped src w (.release p prev) ty
  | layerBuild (p : Point) (m : MemoMapId) (scope : Nat) (lt : LayerTy)
      (h : LayerPointTyped src w p lt) (live : ScopeLive w scope) (memo : MemoLive w m) :
      BodyTyped src w (.layerBuild p m scope)
        ⟨.handle Ty.contextTarget, lt.error, Env.Requirement.empty⟩

/-- Membership at the answer column gives the successful exit; its defect exclusion is vacuous. -/
theorem strongExit_success (w : World) (ty : EffTy) (v : Val) (h : Fits w v ty.answer) :
    ExitOk w ty (.success v) := ⟨h, trivial⟩

/-- A clean failure has base membership at every effect type because the error column
constrains only `Fail` reasons. The strengthened exit judgment separately requires the
explicit defect-exclusion premise: `cleanExit` alone admits `badName` and `notImplemented`. -/
theorem strongExit_of_clean (w : World) (ty : EffTy) (c : CauseV)
    (h : cleanExit (.failure c) = true) (shape : NoShapeDefect ty (.failure c)) :
    ExitOk w ty (.failure c) := ⟨fitsExit_of_clean w ty c h shape, shape⟩

/-- At a `never` error column a fitting failure is clean: no value has type `never`. -/
theorem cleanExit_of_never (w : World) (ty : EffTy) (c : CauseV) (never : ty.error = .never)
    (h : ExitOk w ty (.failure c)) : cleanExit (.failure c) = true := cleanExit_of_never_fits w ty c never h.1

/-! ## `π` for services (C5) -/

/-- A world read at a signature's service table. -/
def restrictWorld (app : SigApp) (w : World) : World := { w with serviceTy := app.serviceTy }

/-- A context's services fit at the restriction exactly when they fit at the world, when the
two tables agree on the context's keys. -/
theorem servicesFit_restrict (app : SigApp) (w : World) (services : Env.Ctx)
    (hagree : ∀ key sv, services.getV key = some sv → w.serviceTy key = app.serviceTy key) :
    ServicesFit (restrictWorld app w) services ↔ ServicesFit w services := by
  constructor
  · intro h
    refine ⟨fun key sv sty hget hty => ?_, h.2⟩
    have hty' : app.serviceTy key = some sty := by
      rw [← hagree key sv hget]
      exact hty
    exact h.1 key sv sty hget hty'
  · intro h
    refine ⟨fun key sv sty hget hty => ?_, h.2⟩
    change app.serviceTy key = some sty at hty
    have hty' : w.serviceTy key = some sty := by
      rw [hagree key sv hget]
      exact hty
    exact h.1 key sv sty hget hty'

/-- Along an extension of the application's signature, membership survives the restriction to
the smaller table: the restriction reads no carrier the world does not. -/
theorem fits_restrict {app app' : SigApp} (hext : SigExtends app.signature app'.signature)
    (w : World) (hw : w.serviceTy = app'.serviceTy) (ty : Ty) (v : Val) (h : Fits w v ty) :
    Fits (restrictWorld app w) v ty :=
  @fits_map w (restrictWorld app w) (table_refl _) (table_refl _) (table_refl _) (fun _ _ hx => hx)
    (Stores.le_refl _)
    (fun key sty hk => by
      change app.serviceTy key = some sty at hk
      rw [hw]
      exact hext.service key sty hk) ty v h

end Effect4.Program.Typed
