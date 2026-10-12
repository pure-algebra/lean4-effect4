import Effect4.Laws.Program.Typed.Admission
import Effect4.Laws.Program.Typed.Contracts
import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typed.Residual — concrete protocols and the program judgment

Defines `Ψ_S` over all 31 `SyncOp` rows with ghost certificates, `Ψ_F` over all 40 `FiberOp`
rows with dependent carriers, the one program judgment `TypedProg`, the interpreter hook
contracts, and the two settling program cases:
1. Polymorphic ref allocation and read on a heterogeneous heap.
2. Addressed fork and mask with body admission.

`TypedProg` is the slice 5 contract ruling of 2026-09-23
(`docs/research/2026-09-23-foundations-slice5-contract-ruling.md`, `E4-SCHED-CE-010/011/012`):
one certificate per operation, shared by its precondition, its postcondition and its
continuation, with the control markers typed by their own arms.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

/-! ## The Store Protocol (31 SyncOp rows) -/

/-- **A binder term maps one type into another**, at a world and at every later one: a value that
fits `A` runs the term at `env ++ [a]` to a value that fits `R`. It is the unary Kripke relation
at a function type, the world-indexing line of `docs/core/semantics.md` §2.1. The term is
first-order data, so `Fits` gains no arrow clause (decisions row 163). A read-modify-write row
demands it of its term (decisions row 43). -/
def TermMaps (w : World) (f : Term) (env : List Val) (A R : Ty) : Prop :=
  ∀ w', w.leHost w' → ∀ a, Fits w' a A → ∃ r, evalTerm (env ++ [a]) f = some r ∧ Fits w' r R

/-- **The term relation is closed under later worlds**, by the order's transitivity: what
`storePre_mono` needs of a read-modify-write row. Quantifying over later worlds is what closes
it; a statement at one world is not closed (`Test/Program/ProtocolPosts.lean`, the control
`termMaps_oneWorld_not_mono`). -/
@[semantics "store-typing" (requirement := R4)]
theorem TermMaps.mono {w w' : World} {f : Term} {env : List Val} {A R : Ty}
    (ord : w.leHost w') (h : TermMaps w f env A R) : TermMaps w' f env A R :=
  fun w'' o a ha => h w'' (leHost_trans _ _ _ ord o) a ha

/-- **The term relation is closed under the checker's order**: a smaller parameter and a larger
result. A read-modify-write row's term is typed at the instance's parameter, and the store's
pre asks for the cell's declared type, which is equivalent to it (`RefDeclared`). A step of
`syncRow_typed` (`Typed/Denotation.lean`), where the claim `term-typed-maps` is used. -/
theorem TermMaps.widen {w : World} {f : Term} {env : List Val} {A A' R R' : Ty}
    (hA : Ty.subN A' A = true) (hR : Ty.subN R R' = true) (h : TermMaps w f env A R) :
    TermMaps w f env A' R' := by
  intro w' ord a ha
  obtain ⟨r, hr, hfit⟩ := h w' ord a (fits_subN w' hA a ha)
  exact ⟨r, hr, fits_subN w' hR r hfit⟩

/-- A row's ghost certificate: the allocated type, the promise's columns, the memo hit's error
type, or the answer column `B` of the two `modify` rows. -/
def StoreCert : SyncOp → Type
  | .refMake _ | .memoGet _ _ | .refModify _ _ _ | .refModifySome _ _ _ => Ty
  | .deferredMake | .memoBuild _ _ => Ty × Ty
  | _ => PUnit

/-- What each store row demands of its request (decisions row 136 for the scope rows). A
read-modify-write row demands a declared cell and that its term maps the cell's type into the
row's result type at every later world (`TermMaps`): `A` at the three update rows, `Option<A>`
at the three `Some` rows, `[B, A]` at `modify` and `[B, Option<A>]` at `modifySome`, where `B` is
the row's certificate. -/
def storePre (root : ProgramSource) (w : World) (op : SyncOp) (cert : StoreCert op) : Prop :=
  match op with
  | .refMake initial => Fits w initial cert
  | .refGet cell => ∃ ty, w.Ρ cell = some ty
  | .refSet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refGetAndSet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refSetAndGet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refUpdate cell f env | .refGetAndUpdate cell f env | .refUpdateAndGet cell f env =>
    ∃ ty, w.Ρ cell = some ty ∧ TermMaps w f env ty ty
  | .refUpdateSome cell f env | .refGetAndUpdateSome cell f env
  | .refUpdateSomeAndGet cell f env =>
    ∃ ty, w.Ρ cell = some ty ∧ TermMaps w f env ty (.option ty)
  -- the answer column `B` is the certificate: `modify` may answer another type than it stores
  | .refModify cell f env => ∃ ty, w.Ρ cell = some ty ∧ TermMaps w f env ty (.prod cert ty)
  | .refModifySome cell f env =>
    ∃ ty, w.Ρ cell = some ty ∧ TermMaps w f env ty (.prod cert (.option ty))
  | .deferredMake => True
  | .deferredIsDone key | .deferredPoll key | .deferredAwaitCleanup key _ _ => (w.«Π» key).isSome = true
  -- the completion fits the promise's declared columns (`CompletionStrong`'s two arms), so the
  -- completed cell stays typed; an ill-typed completion leaves no later world over the new store
  | .deferredCompleteWith key completion => ∃ a e, w.«Π» key = some (a, e) ∧
      match completion with
      | .ofExit ex => ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex
      | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ Ty.subN t a = true
  | .deferredInterruptWith key _ => (w.«Π» key).isSome = true
  | .clockNow | .sleepCancel _ _ => True
  | .scopeMake _ => True
  -- the named scope is live in the world's store, so the store never steps to a frontier
  -- (`syncOpStep` answering `none`, which the evaluator answers `unit`; row 139's liveness,
  -- read through row 156's predicate); a registered finalizer is admitted (decisions row 151
  -- (a″)), so the scope store's typing types it at `⟨unknown, never⟩`
  | .scopeAdd scope fin => ScopeLive w scope ∧ FinalizerAdmitted root w fin
  | .scopeRemove scope _ | .scopeIsClosed scope | .scopeFork scope _ => ScopeLive w scope
  | .memoFork _ | .memoRelease _ _ => True
  -- the exit that completes a memo entry fits the entry's columns, the built context and the
  -- layer's own checked error type, as `deferredCompleteWith`'s exit fits its cell's; with
  -- `memoBuild`'s row, the memo-table clause `memoGet`'s post reads (decisions row 187)
  | .memoComplete layer _ ex => ∃ l lt, Node.at_ (.eff root.program) layer.1 = some (.layer l) ∧
      Checker.checkLayer (root.scopeSig layer.1) layer.1 (LayerTerm.expandIn root.program l) = .ok lt ∧
      ExitOk w ⟨.handle Ty.contextTarget, lt.error, Env.Requirement.empty⟩ ex
  -- the looked-up layer's own checked error type (decision row 90), read through the
  -- expansion's rounds as `PointTyped` reads a node (decisions row 153 (b))
  | .memoGet layer _ => ∃ l lt, Node.at_ (.eff root.program) layer.1 = some (.layer l) ∧
      Checker.checkLayer (root.scopeSig layer.1) layer.1 (LayerTerm.expandIn root.program l) = .ok lt ∧
      lt.error = cert
  -- the entry's Deferred is declared at the layer's columns, the built context and the layer's
  -- own checked error type, read as `memoGet` reads them: the promise table's `memoBuild` row
  -- (`Typed/Vocabulary.lean`), the memo-table clause `memoGet`'s post relies on (decisions row 187)
  | .memoBuild layer _ => ∃ l lt, Node.at_ (.eff root.program) layer.1 = some (.layer l) ∧
      Checker.checkLayer (root.scopeSig layer.1) layer.1 (LayerTerm.expandIn root.program l) = .ok lt ∧
      cert = (.handle Ty.contextTarget, lt.error)

/-- What each store row's answer satisfies: the store's actual answer (decisions row 136; the
handler's adequacy is `StoreImplements`, `Typed/Adequacy.lean`). -/
def storePost (w' : World) (op : SyncOp) (cert : StoreCert op) (ans : Val) : Prop :=
  match op with
  | .refMake _ => ∃ key : RefKey, ans = Val.cell key ∧ w'.Ρ key = some cert
  | .refGet cell => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refSet cell _ => ans = Val.cell cell
  | .refGetAndSet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refSetAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refUpdate _ _ _ | .refUpdateSome _ _ _ => ans = Val.unit
  | .refGetAndUpdate cell _ _ | .refGetAndUpdateSome cell _ _ =>
    ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refUpdateAndGet cell _ _ | .refUpdateSomeAndGet cell _ _ =>
    ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refModify _ _ _ | .refModifySome _ _ _ => Fits w' ans cert
  | .deferredMake => ∃ key : DeferredKey, ans = Val.promise key ∧ w'.«Π» key = some cert
  | .deferredIsDone _ => ∃ b, ans = Val.bool b
  | .deferredPoll _ => ∃ b, ans = Val.bool b
  | .deferredCompleteWith _ _ | .deferredInterruptWith _ _ => ∃ b, ans = Val.bool b
  | .deferredAwaitCleanup _ _ _ => ans = Val.unit
  | .clockNow => ∃ n, ans = Val.nat n
  | .sleepCancel _ _ => ans = Val.unit
  -- a scope-answering row answers a present scope's handle (decisions row 156): the step
  -- installs or holds the entry, and `Fits` at `Ty.scope` reads presence (`fits_scope_inv`)
  | .scopeMake _ => Fits w' ans Ty.scope
  -- an open scope registers and answers `unit`; a closed one answers its closing exit, at
  -- `Exit<unknown, unknown>` (DI-94's release type), for the caller to run the finalizer now
  | .scopeAdd _ _ => ans = Val.unit ∨
      ∃ ex, ans = reifyExitVal ex ∧ FitsExit w' ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex
  | .scopeRemove _ _ => ans = Val.unit
  | .scopeIsClosed _ => ∃ b, ans = Val.bool b
  | .scopeFork _ _ => Fits w' ans Ty.scope
  | .memoFork _ => ∃ id, ans = Val.memoMap id ∧ MemoLive w' id
  | .memoGet _ _ => ans = Val.unit ∨ ∃ cell owner, Val.memoHit? ans = some (cell, owner) ∧
      w'.«Π» cell = some (.handle Ty.contextTarget, cert) ∧ MemoLive w' owner
  | .memoBuild _ _ => Fits w' ans Ty.scope
  | .memoComplete _ _ _ => ans = Val.unit
  -- the last observer's release answers the layer's scope handle, for the caller to close; the
  -- layer scope is present (`Stores.MemoValid`, which `StoreTyped` carries)
  | .memoRelease _ _ => ans = Val.unit ∨ Fits w' ans Ty.scope

def Ψ_S (root : ProgramSource) : Protocol World StoreSig where
  Cert := StoreCert
  pre := storePre root
  post := storePost

/-! ## The Fiber Protocol (41 FiberOp rows) -/

/-- An operation whose answer is an installed body's exit, a registration's delivery or a
spawned fiber certifies that type (`EffTy`); one answering a typed value certifies the value's
type (`Ty`). A guard certifies its intermediate type (`E4-SCHED-CE-011`). Ruling 2026-09-23,
typed-state admission audit: a `True` post refused every program consuming the answer
(`E4-SCHED-CE-013`). -/
def FiberCert : FiberOp → Type
  | .fork _ _ _ | .forkIn _ _ _ _ | .forkScoped _ _ _ | .mask _ _ | .guard_ _ | .scoped _
  | .raceAll _ _ | .raceAllFirst _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ => EffTy
  | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren | .getContext => Ty
  | _ => PUnit

/-- **Row 116's host-row entry, at the row's instance** (decisions row 183, ratified 2026-10-04):
the operation is in the domain of the signature over the source's tables (a host row is the
application's, never the program's definition block, decisions row 328), and the row's check at some request type
(`rowTy`: the template's instance at the request's match) gives columns below the certificate.
Outside the table the row is the placeholder, whose `never` columns are below every certificate,
so without the bit the entry held at every certificate at a short table and constrained at a
longer one (`Test/Program/TypedProgRows.lean`, `typedProg_not_table_monotone_of`); with it
`TypedProg` is monotone along an appended table (`typedProg_rows_append`). Read at the template
instead, the entry admitted no certificate a host success could meet at a parameter's position:
the checked type is the instance, so the host-row arm certifies at it with no bridge. -/
def bitEntry (root : ProgramSource) (op : NativeOp) (cert : EffTy) : Prop :=
  root.sig.signature.dom op = true ∧
    ∃ reqTy t, rowTy (root.sig.signature.rowOf op) reqTy = some t ∧
      t.answer.sub cert.answer = true ∧ t.error.sub cert.error = true

/-- The type an async registration's answer is certified at: a timer's `unit`, a deferred's
completion at the promise table's columns, a host row's columns from the source's row table
when the row is in its domain (`bitEntry`, row 116).
A host slot (`FinName.parkThen`'s release) is certified by the host protocol, a correlation the
state predicate owns; any other registration is not generated code and is refused.

Decisions row 137 (ratified 2026-10-01), reviewed here: the certificate is chosen by the
typing derivation, which may take it equal to the declared columns, so these comparisons stay in
`Ty.sub`; `fits_normalize` bridges a certificate to the checker's normalized type. The same holds
for `fiberPre`'s `awaitAll` and `raceAll` entries. -/
def asyncPre (root : ProgramSource) (w : World) (register : EffName) (cert : EffTy) : Prop :=
  match register with
  | .store (.registerSleep _) => Ty.unit.sub cert.answer = true
  | .registerAwait cell | .store (.registerAwait cell) =>
    ∃ a e, w.«Π» cell = some (a, e) ∧ a.sub cert.answer = true ∧ e.sub cert.error = true
  | .external op _ _ => bitEntry root op cert
  | .store (.externalRegister _) => True
  | _ => False

/-- **A typed loop point with a typed cursor** (decisions row 190 (b), `E4-TYPED-CE-037`): the
point addresses an `iterate` the checker types at `ty` under an environment its values fit, read
through the expansion's rounds as `PointTyped` reads a node, its completed view typed, and the
cursor fits the loop's checked cursor type `cursorTy.getD c0`, `c0` the initial term's type
(`Checker.check`'s `iterate` rule, `Program/Checker.lean:178-189`). `PointTyped` alone admitted a
Boolean-cursor loop entered with `unit`, whose entry installs `badShapeExit`. The loop entry's
producer is `iterate_arm` (`Typed/Denotation.lean`); its consumer, `clause_loop`
(`Typed/Commands/Clauses/Loop.lean`). The node is checked at the signature of its scope and the
stack is typed there, as `PointTyped`'s (slice CX1); a term's type is the source signature's,
which every scope shares (`ProgramSource.scopeSig_extends`). -/
def LoopPointTyped (root : ProgramSource) (w : World) (p : Point) (ty : EffTy) (cursor : Val) :
    Prop :=
  ∃ (cursorTy : Option Ty) (initial test step result : Term) (body : NativeEff) (env : List Ty)
    (c0 : Ty),
    Node.at_ (.eff root.program) p.path =
      some (.eff (.iterate cursorTy initial test step result body)) ∧
    Checker.check (root.scopeSig p.path) env p.path
      (Eff.expandIn root.program (.iterate cursorTy initial test step result body)) = .ok ty ∧
    EnvTyped w env p.env ∧ (∀ q ∈ p.completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2) ∧
    termTy root.signature env initial = some c0 ∧ Fits w cursor (cursorTy.getD c0) ∧
    StackTyped root w (scopeParams root.program p.path) p.params

def fiberPre (root : ProgramSource) (w : World) (op : FiberOp) (cert : FiberCert op) : Prop :=
  match op with
  | .getId | .yieldNow _ | .ambientScope | .sync _ | .getInterruptible => True
  -- the context set keeps every service at its key's type (decision row 90)
  | .setContext ctx => ServicesFit w ctx.services
  | .getContext => cert = .handle Ty.contextTarget
  | .await target _ => (w.Γ target).isSome = true
  | .awaitAll targets | .awaitAllFailFast targets =>
    ∃ a e, cert = .list (.exitOf a e) ∧ ∀ t ∈ targets, ∃ fty, w.Γ t = some fty ∧
      fty.answer.sub a = true ∧ fty.error.sub e = true
  | .raceAll entrants _ | .raceAllFirst entrants _ => ∀ p ∈ entrants, ∃ ty, PointTyped root w p ty ∧
      ty.answer.sub cert.answer = true ∧ ty.error.sub cert.error = true
  | .async register _ => asyncPre root w register cert
  | .suspend _ | .awaitNewChildren _ => True
  -- the queued `afterInterrupt` awaits every target (`FiberListColumns`), so the row demands
  -- each declared, as `interrupt` demands its one target (finding F-PRE)
  | .interruptAll targets _ => ∀ t ∈ targets, (w.Γ t).isSome = true
  -- the public interrupt installs `interruptAs(target, self)` (`:857`), whose row demands the
  -- target (finding F-PRE); `interruptScoped` installs the public interrupt on another fiber
  | .interrupt target | .interruptScoped target => (w.Γ target).isSome = true
  -- row 139's halting arms (seat C's census): the step halts on an unknown target or an absent
  -- scope (`FiberAction.interruptAs`, `linkScope` from `runIn` and `forkIn`,
  -- `FiberAction.closeScope`, `prepareScopedExitR`), so the row demands them, a scope's
  -- presence as `ScopeLive` (row 156); a race registration marker is `RegistrationState`'s,
  -- never typed code
  | .interruptAs target _ => (w.Γ target).isSome = true
  | .runIn target scope => (w.Γ target).isSome = true ∧ ScopeLive w scope
  | .guard_ _ | .unguard _ | .finishFinalizer _ | .construction
  | .foreignRelease _ _ | .closeWalk _ _ _
  | .cancelRace _ | .dropObservers _ | .frontier _ _ => True
  -- the walk runs each finalizer at the closing exit: the store's admission of each, and the
  -- exit's fit (seat M6E's finding; the scope registration's precedent, by name)
  | .closeIter _ order ex => (∀ fin ∈ order, FinalizerAdmitted root w fin) ∧
    FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex
  | .scopeExit _ scope _ => ScopeLive w scope
  -- the closing exit becomes the scope's (`scopeCloseSnapshot`), which the scope store types at
  -- `Exit<unknown, unknown>` (`ScopeExitOk`, DI-94) and `Stores.WF` asks valid (finding F-CLOSE,
  -- `closeScope_pre_refuses_unfit_exit`; the admission states what the program needs)
  | .closeScope scope ex =>
    ScopeLive w scope ∧ FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex
  | .raceRegister _ => False
  | .snapshotChildren => cert = .list (.fiberOf .unknown .unknown)
  | .scoped body => PointTyped root w body cert
  | .mask _ body => BodyTyped root w body cert
  | .forkScoped child _ _ => PointTyped root w child cert
  | .fork body _ _ => BodyTyped root w body cert
  | .forkIn child _ scope _ => PointTyped root w child cert ∧ ScopeLive w scope
  -- the entry walks the generator at the point (`walkR`), which halts with `badName` at a point of
  -- another node, an exit no type admits: the row names the node (seat M6E's third finding)
  | .gen p => PointTyped root w p cert ∧
      ∃ body, Node.at_ (.eff root.program) p.path = some (.eff (.gen body))
  -- the cursor at the loop's checked cursor type (decisions row 190 (b))
  | .loop p cursor => LoopPointTyped root w p cert cursor
  | .refuse _ => False

/-- What each fiber row's answer satisfies: what the machine delivers to the continuation
(decisions row 136 for the await-by-value, close-scope and close-walk rows). -/
def fiberPost (w' : World) (op : FiberOp) (cert : FiberCert op) (ans : op.answer) : Prop :=
  match op with
  | .getId => ∃ (id : FiberId), ans = Val.nat id.value
  -- the mask at a constant body (decisions row 245): one of the saved state's two images
  | .getInterruptible => ∃ (flag : Bool), ans = Val.savedMask flag
  | .getContext | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren => Fits w' ans cert
  | .setContext _ | .yieldNow _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _
  | .interruptAll _ _ | .runIn _ _ | .cancelRace _ | .dropObservers _
  | .foreignRelease _ _ | .closeWalk _ _ _ | .awaitNewChildren _ => ans = Val.unit
  -- the context's ambient scope, present by `J` (`ambientScope_live`, decisions row 156)
  | .ambientScope => Fits w' ans Ty.scope
  | .sync value => ans = value
  | .await target mode => match mode with
    | .joinEffect => ∃ ty, w'.Γ target = some ty ∧ ExitOk w' ty ans
    -- the encoded exit, the checker's own rule (`Program/Checker.lean:196`) and row 106's token
    -- rule (`observerDeliveredType`), not the target's answer column
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ Fits w' ans (.exitOf ty.answer ty.error)
  | .fork _ _ _ | .forkIn _ _ _ _ => ∃ id : FiberId, ans = Val.fiber id ∧ w'.Γ id = some cert
  | .forkScoped _ _ _ => ∃ id : FiberId, ans = .success (Val.fiber id) ∧ w'.Γ id = some cert
  | .mask _ _ | .scoped _ | .raceAll _ _ | .raceAllFirst _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ =>
    ExitOk w' cert ans
  | .unguard ex | .finishFinalizer ex | .scopeExit _ _ ex => ans = ex
  -- `Scope.close` answers `void` and the close walk its merged exit: a success or a clean
  -- failure, an exit at `⟨unit, never⟩`, never the closing argument
  | .closeScope _ _ | .closeIter _ _ _ => ExitOk w' (EffTy.pure .unit) ans
  | .guard_ kind => match ans with
    | none => True
    | some ex => kind.hasExitArm ex = true ∧ ExitOk w' cert ex
  -- a live frontier is never answered (fuel exhaustion is not an exit)
  | .frontier _ _ => False
  -- the completed exits a callback reads, each at its fiber's declared type
  | .construction => ∀ p ∈ ans, ∃ ty, w'.Γ p.1 = some ty ∧ ExitOk w' ty p.2
  | .suspend _ | .refuse _ => True

def Ψ_F (root : ProgramSource) : Protocol World FiberSig where
  Cert := FiberCert
  pre := fiberPre root
  post := fiberPost

/-! ## The program judgment -/

/-- The one typing of a reference program at an effect type. Store and fiber operations follow
`Ψ_S` and `Ψ_F`: a certificate, its precondition, and a continuation for every answer the
postcondition admits at every later world. The fiber arm excludes the four control markers,
which have their own arms. A guard's body is typed at the guard's certified intermediate type
`mid`; the saved arm runs on the exits the guard row admits at `mid`, and an exit the arm does
not take must fit the outer type. `unguard` and `finishFinalizer` carry an exit at the current
type and type no continuation: the reference machine never resumes one (`evaluateFiberR`
hands the payload to `deliverR`; `popR`'s answer glue passes it to the next frame).
The scope-exit marker is no program: `prepareScopedExitR` consumes it in the evaluation whose walk
installed it, and as current code reaching a counted step the evaluator answers `badShapeExit`
(`E4-TYPED-CE-034`). So it is typed only where the `scoped` arm puts it, the run arm of the
`onExit false` guard that arm installs (`scopedGuard`, decisions row 188 (a)): every exit runs the
scope's callback, whose scope is present (`ScopeLive`, row 156: the machine halts on an absent
scope, `E4-SCHED-CE-020`) and whose restored context fits; the callback carries the body's exit
(a finalizer's failure may combine with it when the scope closes), so the guard widens its
body's type to its own for that exit.

 The existing residual program judgment also carries its entry input and completion
position. The unit-input instance below retains the original type-only surface. Context rows
use these same constructors, so guard bodies and their callbacks retain the input guaranteed at the actual exit. -/
inductive ProgramArrow {Input Object : Type}
    (storePre : World → Input → (op : SyncOp) → StoreCert op → Prop)
    (storePost : World → Input → (op : SyncOp) → StoreCert op → Val → Prop)
    (fiberPre : World → Input → (op : FiberOp) → FiberCert op → Prop)
    (fiberPost : World → Input → (op : FiberOp) → FiberCert op → op.answer → Prop)
    (fiberInput : Input → (op : FiberOp) → op.answer → Input)
    (Exits : World → Input → Object → ExitV → Prop)
    (guardPost : World → Input → GuardKind → Object → ExitV → Prop)
    (inputOf : Object → ExitV → Input) (restoreInput : Ctx → Input)
    (Entry : Input → Object → Prop) :
    World → Input → Object → RProgram → Prop
  | pure {w : World} {input : Input} {ty : Object} {ex : ExitV}
      (exit : Exits w input ty ex) (entry : Entry input ty := by exact True.intro) :
      ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input ty (.pure ex)
  | store {w : World} {input : Input} {ty : Object} {op : SyncOp} {k : Val → RProgram}
      (cert : StoreCert op) (pre : storePre w input op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, storePost w' input op cert ans →
        ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
          w' input ty (k ans)) (entry : Entry input ty := by exact True.intro) :
      ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input ty (.vis (.inl op) k)
  | fiber {w : World} {input : Input} {ty : Object} {op : FiberOp} {k : op.answer → RProgram}
      (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
      (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
      (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex)
      (cert : FiberCert op) (pre : fiberPre w input op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, fiberPost w' input op cert ans →
        ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
          w' (fiberInput input op ans) ty (k ans))
      (entry : Entry input ty := by exact True.intro) :
      ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input ty (.vis (.inr op) k)
  | guard {w : World} {input : Input} {ty : Object} {kind : GuardKind}
      {k : Option ExitV → RProgram} (mid : Object)
      (body : ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input mid (k none))
      (run : ∀ w', w.leHost w' → ∀ ex, guardPost w' (inputOf mid ex) kind mid ex →
        ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
          w' (inputOf mid ex) ty (k (some ex)))
      (skip : ∀ w', w.leHost w' → ∀ ex, Exits w' (inputOf mid ex) mid ex →
        kind.hasExitArm ex = false → Exits w' (inputOf mid ex) ty ex)
      (entry : Entry input ty := by exact True.intro) :
      ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : World} {input : Input} {ty : Object} {ex : ExitV} {k : ExitV → RProgram}
      (payload : Exits w input ty ex) (entry : Entry input ty := by exact True.intro) :
      ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : World} {input : Input} {ty : Object} {ex : ExitV} {k : ExitV → RProgram}
      (payload : Exits w input ty ex) (entry : Entry input ty := by exact True.intro) :
      ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopedGuard {w : World} {input : Input} {ty : Object} {k : Option ExitV → RProgram}
      (mid : Object) (prev : Ctx) (sc : Nat)
      (body : ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input mid (k none))
      (callback : ∀ ex, Contracts.scopeExitCallback? (k (some ex)) = some (prev, sc, ex))
      (live : ScopeLive w sc) (services : ServicesFit w prev.services)
      (widen : ∀ w', w.leHost w' → ∀ ex, Exits w' (inputOf mid ex) mid ex →
        Exits w' (restoreInput prev) ty ex) (entry : Entry input ty := by exact True.intro) :
      ProgramArrow storePre storePost fiberPre fiberPost fiberInput Exits guardPost inputOf restoreInput Entry
        w input ty (.vis (.inr (.guard_ (.onExit false))) k)

namespace ProgramArrow
section Transport
variable {Input Object : Type}
  {SP : World → Input → (op : SyncOp) → StoreCert op → Prop}
  {SQ : World → Input → (op : SyncOp) → StoreCert op → Val → Prop}
  {FP : World → Input → (op : FiberOp) → FiberCert op → Prop}
  {FQ : World → Input → (op : FiberOp) → FiberCert op → op.answer → Prop}
  {stepInput : Input → (op : FiberOp) → op.answer → Input}
  {Ex : World → Input → Object → ExitV → Prop}
  {GP : World → Input → GuardKind → Object → ExitV → Prop}
  {inputOf : Object → ExitV → Input} {restoreInput : Ctx → Input}
  {Entry : Input → Object → Prop}

/-- Every shared program derivation supplies its entry capability bound.
Consumer: current-code, saved callback and queued resume entry positions in typed preservation. -/
theorem entry {w : World} {input : Input} {ty : Object} {p : RProgram}
    (h : ProgramArrow SP SQ FP FQ stepInput Ex GP inputOf restoreInput Entry w input ty p) :
    Entry input ty := by
  cases h <;> assumption

/-- Changing only the output object uses one constructor proof for every program instance.
Consumer: type-column widening and ambient provider completion guarantees. -/
theorem outputMap {w : World} {input : Input} {ty ty' : Object} {program : RProgram}
    (typed : ProgramArrow SP SQ FP FQ stepInput Ex GP inputOf restoreInput Entry w input ty program)
    (exits : ∀ world input exit, Ex world input ty exit → Ex world input ty' exit)
    (entries : ∀ input, Entry input ty → Entry input ty') :
    ProgramArrow SP SQ FP FQ stepInput Ex GP inputOf restoreInput Entry w input ty' program := by
  induction typed with
  | pure payload entry => exact .pure (exits _ _ _ payload) (entries _ entry)
  | store cert pre _ entry ih =>
    exact .store cert pre (fun later ordered answer post => ih later ordered answer post exits entries)
      (entries _ entry)
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ entry ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert pre
      (fun later ordered answer post => ih later ordered answer post exits entries) (entries _ entry)
  | guard mid body _ skip entry _ ihRun =>
    exact .guard mid body (fun later ordered exit post => ihRun later ordered exit post exits entries)
      (fun later ordered exit payload absent => exits _ _ _ (skip later ordered exit payload absent))
      (entries _ entry)
  | unguard payload entry => exact .unguard (exits _ _ _ payload) (entries _ entry)
  | finishFinalizer payload entry => exact .finishFinalizer (exits _ _ _ payload) (entries _ entry)
  | scopedGuard mid previous scope body callback live services widen entry _ =>
    exact .scopedGuard mid previous scope body callback live services
      (fun later ordered exit payload => exits _ _ _ (widen later ordered exit payload)) (entries _ entry)

/-- World transport uses the same seven program constructors for every input index.
`typedProg_mono` and the ambient context instance consume this law. -/
theorem mono
    (store : ∀ {w w' input op cert}, w.leHost w' → SP w input op cert → SP w' input op cert)
    (fiber : ∀ {w w' input op cert}, w.leHost w' → FP w input op cert → FP w' input op cert)
    (exits : ∀ {w w' input ty ex}, w.leHost w' → Ex w input ty ex → Ex w' input ty ex)
    {w w' : World} {input : Input} {ty : Object} {p : RProgram}
    (ord : w.leHost w')
    (h : ProgramArrow SP SQ FP FQ stepInput Ex GP inputOf restoreInput Entry w input ty p) :
    ProgramArrow SP SQ FP FQ stepInput Ex GP inputOf restoreInput Entry w' input ty p := by
  induction h generalizing w' with
  | pure exit entry => exact .pure (exits ord exit) entry
  | store cert pre next entry _ =>
    exact .store cert (store ord pre)
      (fun w'' o ans post => next w'' (leHost_trans _ _ _ ord o) ans post) entry
  | fiber notGuard notUnguard notFinish notScopeExit cert pre next entry _ =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert (fiber ord pre)
      (fun w'' o ans post => next w'' (leHost_trans _ _ _ ord o) ans post) entry
  | guard mid _ run skip entry ihBody _ =>
    exact .guard mid (ihBody ord)
      (fun w'' o ex post => run w'' (leHost_trans _ _ _ ord o) ex post)
      (fun w'' o ex fit arm => skip w'' (leHost_trans _ _ _ ord o) ex fit arm) entry
  | unguard payload entry => exact .unguard (exits ord payload) entry
  | finishFinalizer payload entry => exact .finishFinalizer (exits ord payload) entry
  | scopedGuard mid prev sc _ callback live services widen entry ihBody =>
    exact .scopedGuard mid prev sc (ihBody ord) callback (scopeLive_mono ord.1 live)
      (servicesFit_map ord.1.2.1 ord.1.2.2.1 ord.1.2.2.2.1 ord.2 ord.1.1.2
        (serviceTy_of_le ord.1) services)
      (fun w'' o ex fit => widen w'' (leHost_trans _ _ _ ord o) ex fit) entry

/-- Closing a program retains its completion position, including its context row.
The original `close_typed` and ambient guard introduction use this one constructor proof. -/
theorem close {w : World} {input : Input} {ty : Object} {p : RProgram}
    (h : ProgramArrow SP SQ FP FQ stepInput Ex GP inputOf restoreInput Entry w input ty p)
    (next : ExitV → RProgram) :
    ProgramArrow SP SQ FP FQ stepInput Ex GP inputOf restoreInput Entry w input ty
      (p.bind (fun ex => .vis (.inr (.unguard ex)) next)) := by
  induction h with
  | pure exit entry => exact .unguard exit entry
  | store cert pre _ entry ih => exact .store cert pre (fun w' o ans post => ih w' o ans post) entry
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ entry ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert pre
      (fun w' o ans post => ih w' o ans post) entry
  | guard mid _ _ skip entry ihBody ihRun =>
    exact .guard mid ihBody (fun w' o ex post => ihRun w' o ex post) skip entry
  | unguard payload entry => exact .unguard payload entry
  | finishFinalizer payload entry => exact .finishFinalizer payload entry
  | scopedGuard mid prev sc _ callback live services widen entry ihBody =>
    exact .scopedGuard mid prev sc ihBody
      (fun ex => Contracts.scopeExitCallback?_bind (callback ex) _) live services widen entry
end Transport
end ProgramArrow

/-- The original type-only surface specializes the same program arrows to unit input. -/
abbrev TypedProg (root : ProgramSource) (w : World) (ty : EffTy) (p : RProgram) : Prop :=
  ProgramArrow (fun w (_ : Unit) => storePre root w) (fun w (_ : Unit) => storePost w)
    (fun w (_ : Unit) => fiberPre root w) (fun w (_ : Unit) => fiberPost w)
    (fun _ _ _ => ()) (fun w (_ : Unit) => ExitOk w)
    (fun w (_ : Unit) kind mid ex => fiberPost w (.guard_ kind) mid (some ex))
    (fun _ _ => ()) (fun _ => ()) (fun _ _ => True) w () ty p

/-- Completion positions index the existing program arrow, not stored program syntax.
The captured getter carries its returned context's row into the provider callback. -/
inductive AmbientPosition where
  | result (type : EffTy) (success failure : Env.Requirement)
  | capturedContext (guaranteed : Env.Requirement)

namespace AmbientPosition
/-- Ordinary result positions retain their original tuple spelling. -/
instance : Coe (EffTy × Env.Requirement × Env.Requirement) AmbientPosition :=
  ⟨fun position => .result position.1 position.2.1 position.2.2⟩

/-- The scheduler reads the same declared result type from each completion position. -/
def type : AmbientPosition → EffTy
  | .result type _ _ => type
  | .capturedContext _ => EffTy.pure .context

/-- Entry coverage is independent of later success, including a captured getter's failure. -/
def failureRow : AmbientPosition → Env.Requirement
  | .result _ _ failure => failure
  | .capturedContext guaranteed => guaranteed
end AmbientPosition

/-- Select an input at the delivered exit, including the getter's actual decoded context.
Consumer: the shared program and frame input projection. -/
def ambientInput (position : AmbientPosition) (exit : ExitV) : Env.Requirement :=
  match position with
  | .result _ success failure => if exit.isSuccess then success else failure
  | .capturedContext guaranteed => match exit with
    | .success value => match Val.context? value with
      | some ctx => ctx.services.keysRow
      | none => guaranteed
    | .failure _ => guaranteed

/-- A captured context preserves both its guaranteed row and its decoded answer row.
Consumer: the provider callback; ordinary positions retain their original row judgment. -/
def AmbientBounds (available : Env.Requirement) (position : AmbientPosition) (exit : ExitV) : Prop :=
  match position with
  | .result _ _ _ => Row.Subset (ambientInput position exit) available
  | .capturedContext guaranteed => Row.Subset guaranteed available ∧
      Row.Subset (ambientInput position exit) available

/-- The selected row describes runtime coverage; membership still reads the existing world. -/
def AmbientExit (w : World) (available : Env.Requirement) (position : AmbientPosition)
    (exit : ExitV) : Prop :=
  ExitOk w position.type exit ∧ AmbientBounds available position exit

/-- A Region body enters with its intrinsic checked requirements.
A protected provider checks the actual installed map, not only the world's service table.
Consumer: ambient mask admission and the existing body-entry preservation path. -/
def BodyCoverage (root : ProgramSource) (w : World) (available : Env.Requirement)
    (body : Body) (cert : EffTy) : Prop :=
  (∀ region, body = .region region → ∃ intrinsic,
    RegionTyped root w region intrinsic ∧ Ty.subN intrinsic.answer cert.answer = true ∧
      Ty.subN intrinsic.error cert.error = true ∧ Row.Subset intrinsic.requires available ∧
      RegionStackTyped root w available region) ∧
  (∀ update region flag, body = .contextEntry update region flag → ∃ intrinsic,
    RegionTyped root w region intrinsic ∧ Ty.subN intrinsic.answer cert.answer = true ∧
      Ty.subN intrinsic.error cert.error = true ∧
      ∀ previous : Env.Ctx, previous.Satisfies available →
        (update.apply previous).Satisfies intrinsic.requires ∧
          (update.apply previous).Satisfies available ∧
          RegionStackTyped root w (update.apply previous).keysRow region)
  ∧ (∀ point, body = .at_ point ∨ (∃ ctx, body = .acquireIn point ctx ∨ body = .release point ctx) →
      AmbientStackTyped root w available (scopeParams root.program point.path) point.params)

/-- The actual captured release producer disables interruption before installing restoration.
Consumer: ambient mask entry; ordinary true-mask bodies retain their source admission. -/
def ReleaseMaskAllowed (op : FiberOp) : Prop :=
  ∀ flag point previous, op = .mask flag (.release point previous) → flag = false

/-- A typed context reader uses both ambient coverage and the world's declared service carriers.
The coarse getter remains available for internal capture and restoration. -/
def ambientFiberPre (root : ProgramSource) (w : World) (available : Env.Requirement)
    (op : FiberOp) (cert : FiberCert op) : Prop :=
  match op with
  | .getContext => cert = .context ∨ ∃ keys, cert = .contextOf keys ∧
      Row.Subset keys available ∧ ∀ key ∈ keys.elems, (w.serviceTy key).isSome = true
  | .mask _ body | .fork body _ _ => BodyTyped root w body cert ∧
      Row.Subset cert.requires available ∧
      (∀ point ctx, body = .acquireIn point ctx → ctx.services.Satisfies available) ∧
      ReleaseMaskAllowed op ∧ BodyCoverage root w available body cert
  | .scoped point =>
      PointTyped root w point cert ∧ Row.Subset (bodyRequires root.signature cert) available
  | .forkScoped point _ _ =>
      PointTyped root w point cert ∧ Row.Subset cert.requires available
  | .forkIn point _ scope _ =>
      (PointTyped root w point cert ∧ ScopeLive w scope) ∧ Row.Subset cert.requires available
  | .gen point => (PointTyped root w point cert ∧
      ∃ body, Node.at_ (.eff root.program) point.path = some (.eff (.gen body))) ∧
      Row.Subset cert.requires available
  | .loop point cursor => LoopPointTyped root w point cert cursor ∧
      Row.Subset cert.requires available
  | .raceAll entrants _ | .raceAllFirst entrants _ => ∀ point ∈ entrants, ∃ ty,
      PointTyped root w point ty ∧ ty.answer.sub cert.answer = true ∧
      ty.error.sub cert.error = true ∧ Row.Subset ty.requires available
  | other => fiberPre root w other cert

/-- The context answer keeps the entry coverage alongside its strong value membership. -/
def ambientFiberPost (w : World) (available : Env.Requirement) (op : FiberOp)
    (cert : FiberCert op) (answer : op.answer) : Prop :=
  match op with
  | .getContext => Fits w answer cert ∧ ∃ ctx, Val.context? answer = some ctx ∧
      ctx.services.Satisfies available
  | other => fiberPost w other cert answer

/-- The internal setter and captured release completion expose their actual context rows.
Consumer: source-provider entry and the existing captured-context restoring frame. -/
def ambientFiberInput (available : Env.Requirement) (op : FiberOp)
    (_answer : op.answer) : Env.Requirement :=
  match op with
  | .setContext ctx => ctx.services.keysRow
  | .mask false (.release _ previous) => previous.services.keysRow
  | .getContext => match Val.context? _answer with
    | some ctx => ctx.services.keysRow
    | none => available
  | _ => available

/-- The row-indexed instance of the same residual program arrows.
Its source consumer requires entry coverage of the checked requirement row. -/
abbrev AmbientProg (root : ProgramSource) (w : World) (available : Env.Requirement)
    (position : AmbientPosition) (p : RProgram) : Prop :=
  ProgramArrow (fun w (_ : Env.Requirement) => storePre root w)
    (fun w (_ : Env.Requirement) => storePost w)
    (ambientFiberPre root) ambientFiberPost ambientFiberInput AmbientExit
    (fun w input kind mid ex => kind.hasExitArm ex = true ∧ AmbientExit w input mid ex)
    ambientInput (fun ctx => ctx.services.keysRow)
    (fun available position => Row.Subset position.failureRow available) w available position p

/-- The actual context answer satisfies the row-indexed protocol.
No key-presence predicate substitutes for the declared service membership. -/
theorem ambient_getContext_answers {root : ProgramSource} {w : World} {available : Env.Requirement}
    {ctx : Ctx} {cert : FiberCert .getContext}
    (services : ServicesFit w ctx.services) (coverage : ctx.services.Satisfies available)
    (pre : ambientFiberPre root w available .getContext cert) :
    ambientFiberPost w available .getContext cert (Val.context ctx) := by
  refine ⟨?_, ctx, Val.context?_context ctx, coverage⟩
  rcases pre with coarse | ⟨keys, same, sub, declared⟩
  · subst cert
    exact ⟨rfl, ctx, Val.context?_context ctx, services, live_context_of_servicesFit services⟩
  · subst cert
    exact fits_contextOf_intro services (fun key member => coverage key (sub key member)) declared

/-- A typed reader certifies the actual context at its promised keys and retains the ambient row.
Its consumer is the typed source context arm and the provider's captured-context sequence. -/
theorem ambient_getContext_typed (root : ProgramSource) (w : World) (keys available : Env.Requirement)
    (covered : Row.Subset keys available)
    (declared : ∀ key ∈ keys.elems, (w.serviceTy key).isSome = true) :
    AmbientProg root w available
      ((⟨.contextOf keys, .never, keys⟩ : EffTy), available, available) (fiberValR .getContext rfl) := by
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (.contextOf keys) (.inr ⟨keys, rfl, covered, declared⟩) ?_ (Row.subset_refl available)
  intro _ _ answer post
  obtain ⟨members, ctx, decoded, coverage⟩ := post
  have bound := (Provision.satisfies_iff_subset_keysRow ctx.services available).mp coverage
  change AmbientProg root _ (match Val.context? answer with
    | some ctx => ctx.services.keysRow
    | none => available) _ _
  rw [decoded]
  exact .pure ⟨strongExit_success _ _ _ members, bound⟩ bound

/-- The actual coarse getter retains value-correlated coverage at its saved callback.
Consumer: the compiled provider's captured previous-context continuation. -/
theorem ambient_captureContext_typed (root : ProgramSource) (w : World)
    (available : Env.Requirement) :
    AmbientProg root w available (.capturedContext available) (fiberValR .getContext rfl) := by
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) .context (.inl rfl) ?_ (Row.subset_refl available)
  intro _ _ answer post
  obtain ⟨members, ctx, decoded, coverage⟩ := post
  have bound := (Provision.satisfies_iff_subset_keysRow ctx.services available).mp coverage
  change AmbientProg root _ (match Val.context? answer with
    | some ctx => ctx.services.keysRow
    | none => available) _ _
  rw [decoded]
  refine .pure ⟨strongExit_success _ _ _ members, bound, ?_⟩ bound
  change Row.Subset (match Val.context? answer with
    | some ctx => ctx.services.keysRow
    | none => available) ctx.services.keysRow
  rw [decoded]
  exact Row.subset_refl _

/-- An internal setter gives its actual success row and a failure row covered at both cuts.
Consumer: provider entry and captured-context restoration through the existing program arrow. -/
theorem ambient_setContext_guarantees (root : ProgramSource) (w : World)
    (available failure : Env.Requirement) (ctx : Ctx) (services : ServicesFit w ctx.services)
    (entry : Row.Subset failure available) (returned : Row.Subset failure ctx.services.keysRow) :
    AmbientProg root w available (EffTy.pure .unit, ctx.services.keysRow, failure)
      (fiberValR (.setContext ctx) rfl) := by
  refine .fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () services ?_ entry
  intro _ _ answer post
  change answer = Val.unit at post
  subst answer
  exact .pure ⟨strongExit_success _ _ _ True.intro, Row.subset_refl _⟩ returned

/-- The internal setter enters its actual supplied key row, rather than retaining the entry row.
The provider and restoration callbacks use this transition. -/
theorem ambient_setContext_typed (root : ProgramSource) (w : World) (available : Env.Requirement)
    (ctx : Ctx) (services : ServicesFit w ctx.services)
    (kept : Row.Subset available ctx.services.keysRow) :
    AmbientProg root w available (EffTy.pure .unit, ctx.services.keysRow, available)
      (fiberValR (.setContext ctx) rfl) :=
  ambient_setContext_guarantees root w available available ctx services (Row.subset_refl available) kept

namespace TypedProg

variable {root : ProgramSource}
abbrev pure := @ProgramArrow.pure Unit EffTy
  (fun w (_ : Unit) => storePre root w) (fun w (_ : Unit) => storePost w)
  (fun w (_ : Unit) => fiberPre root w) (fun w (_ : Unit) => fiberPost w)
  (fun _ _ _ => ()) (fun w (_ : Unit) => ExitOk w)
  (fun w (_ : Unit) kind mid ex => fiberPost w (.guard_ kind) mid (some ex))
  (fun _ _ => ()) (fun _ => ()) (fun _ _ => True)
abbrev store := @ProgramArrow.store Unit EffTy
  (fun w (_ : Unit) => storePre root w) (fun w (_ : Unit) => storePost w)
  (fun w (_ : Unit) => fiberPre root w) (fun w (_ : Unit) => fiberPost w)
  (fun _ _ _ => ()) (fun w (_ : Unit) => ExitOk w)
  (fun w (_ : Unit) kind mid ex => fiberPost w (.guard_ kind) mid (some ex))
  (fun _ _ => ()) (fun _ => ()) (fun _ _ => True)
abbrev fiber := @ProgramArrow.fiber Unit EffTy
  (fun w (_ : Unit) => storePre root w) (fun w (_ : Unit) => storePost w)
  (fun w (_ : Unit) => fiberPre root w) (fun w (_ : Unit) => fiberPost w)
  (fun _ _ _ => ()) (fun w (_ : Unit) => ExitOk w)
  (fun w (_ : Unit) kind mid ex => fiberPost w (.guard_ kind) mid (some ex))
  (fun _ _ => ()) (fun _ => ()) (fun _ _ => True)
abbrev guard := @ProgramArrow.guard Unit EffTy
  (fun w (_ : Unit) => storePre root w) (fun w (_ : Unit) => storePost w)
  (fun w (_ : Unit) => fiberPre root w) (fun w (_ : Unit) => fiberPost w)
  (fun _ _ _ => ()) (fun w (_ : Unit) => ExitOk w)
  (fun w (_ : Unit) kind mid ex => fiberPost w (.guard_ kind) mid (some ex))
  (fun _ _ => ()) (fun _ => ()) (fun _ _ => True)
abbrev unguard := @ProgramArrow.unguard Unit EffTy
  (fun w (_ : Unit) => storePre root w) (fun w (_ : Unit) => storePost w)
  (fun w (_ : Unit) => fiberPre root w) (fun w (_ : Unit) => fiberPost w)
  (fun _ _ _ => ()) (fun w (_ : Unit) => ExitOk w)
  (fun w (_ : Unit) kind mid ex => fiberPost w (.guard_ kind) mid (some ex))
  (fun _ _ => ()) (fun _ => ()) (fun _ _ => True)
abbrev finishFinalizer := @ProgramArrow.finishFinalizer Unit EffTy
  (fun w (_ : Unit) => storePre root w) (fun w (_ : Unit) => storePost w)
  (fun w (_ : Unit) => fiberPre root w) (fun w (_ : Unit) => fiberPost w)
  (fun _ _ _ => ()) (fun w (_ : Unit) => ExitOk w)
  (fun w (_ : Unit) kind mid ex => fiberPost w (.guard_ kind) mid (some ex))
  (fun _ _ => ()) (fun _ => ()) (fun _ _ => True)
abbrev scopedGuard := @ProgramArrow.scopedGuard Unit EffTy
  (fun w (_ : Unit) => storePre root w) (fun w (_ : Unit) => storePost w)
  (fun w (_ : Unit) => fiberPre root w) (fun w (_ : Unit) => fiberPost w)
  (fun _ _ _ => ()) (fun w (_ : Unit) => ExitOk w)
  (fun w (_ : Unit) kind mid ex => fiberPost w (.guard_ kind) mid (some ex))
  (fun _ _ => ()) (fun _ => ()) (fun _ _ => True)

theorem pure_inv {root : ProgramSource} {w : World} {ty : EffTy} {ex : ExitV}
    (h : TypedProg root w ty (.pure ex)) : ExitOk w ty ex := by
  cases h with
  | pure exit => exact exit

theorem store_inv {root : ProgramSource} {w : World} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
    (h : TypedProg root w ty (.vis (.inl op) k)) :
    ∃ cert : (Ψ_S root).Cert op, (Ψ_S root).pre w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, (Ψ_S root).post w' op cert ans → TypedProg root w' ty (k ans) := by
  cases h with
  | store cert pre next => exact ⟨cert, pre, next⟩

/-- The fiber arm's inversion (TY-16): an operation that is none of the four control markers is
typed by its certificate, its pre, and a continuation for every answer the post admits at every
later world. -/
theorem fiber_inv {root : ProgramSource} {w : World} {ty : EffTy} {op : FiberOp}
    {k : op.answer → RProgram} (h : TypedProg root w ty (.vis (.inr op) k))
    (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
    (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
    (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex) :
    ∃ cert : (Ψ_F root).Cert op, (Ψ_F root).pre w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, (Ψ_F root).post w' op cert ans → TypedProg root w' ty (k ans) := by
  cases h with
  | fiber _ _ _ _ cert pre next => exact ⟨cert, pre, next⟩
  | guard _ _ _ _ => exact absurd rfl (notGuard _)
  | unguard _ => exact absurd rfl (notUnguard _)
  | finishFinalizer _ => exact absurd rfl (notFinish _)
  | scopedGuard _ _ _ _ _ _ _ _ => exact absurd rfl (notGuard _)

/-- A guard's typing: the body at the guard's intermediate type `mid`, a run arm for the exits
the guard row admits at `mid` and a skip arm, both at every later world. With the Kripke-closed
frame judgment (row 135) this is the arrow of the frame the evaluator saves
(`saveR`'s `.resume kind`), with the run arm's premise curried: `TypedProg.guard_frame`, stated
below the hook protocols. Before row 135
the frame's arms were stated at one world, so the two were not the same arrow, whatever this
docstring then said. -/
theorem guard_inv {root : ProgramSource} {w : World} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : TypedProg root w ty (.vis (.inr (.guard_ kind)) k)) :
    (∃ mid : EffTy, TypedProg root w mid (k none) ∧
      (∀ w', w.leHost w' → ∀ ex, fiberPost w' (.guard_ kind) mid (some ex) →
        TypedProg root w' ty (k (some ex))) ∧
      (∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
        ExitOk w' ty ex)) ∨
    (kind = .onExit false ∧ ∃ (mid : EffTy) (prev : Ctx) (sc : Nat),
      TypedProg root w mid (k none) ∧
      (∀ ex, Contracts.scopeExitCallback? (k (some ex)) = some (prev, sc, ex)) ∧
      ScopeLive w sc ∧ ServicesFit w prev.services ∧
      (∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → ExitOk w' ty ex)) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run skip => exact .inl ⟨mid, body, run, skip⟩
  | scopedGuard mid prev sc body callback live services widen =>
    exact .inr ⟨rfl, mid, prev, sc, body, callback, live, services, widen⟩

/-- A guard of any kind but `onExit false` is an ordinary guard: its body, run and skip arms. -/
theorem guard_inv_of_ne {root : ProgramSource} {w : World} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : TypedProg root w ty (.vis (.inr (.guard_ kind)) k))
    (hk : kind ≠ .onExit false) :
    ∃ mid : EffTy, TypedProg root w mid (k none) ∧
      (∀ w', w.leHost w' → ∀ ex, fiberPost w' (.guard_ kind) mid (some ex) →
        TypedProg root w' ty (k (some ex))) ∧
      (∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
        ExitOk w' ty ex) := by
  rcases guard_inv h with plain | ⟨same, _⟩
  · exact plain
  · exact absurd same hk

/-- A guard whose run arm is not a scope's exit callback is an ordinary guard: its body, run and
skip arms (the `scopedGuard` constructor's callbacks hold at every exit). -/
theorem guard_inv_ordinary {root : ProgramSource} {w : World} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : TypedProg root w ty (.vis (.inr (.guard_ kind)) k))
    (ordinary : Contracts.scopeExitCallback? (k (some (.success .unit))) = none) :
    ∃ mid : EffTy, TypedProg root w mid (k none) ∧
      (∀ w', w.leHost w' → ∀ ex, fiberPost w' (.guard_ kind) mid (some ex) →
        TypedProg root w' ty (k (some ex))) ∧
      (∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
        ExitOk w' ty ex) := by
  rcases guard_inv h with plain | ⟨_, _, _, _, _, callback, _⟩
  · exact plain
  · rw [callback] at ordinary
    cases ordinary

end TypedProg

/-- FR-09's marker payload inversion: a typed `unguard` carries an exit at the current type. -/
theorem unguard_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.unguard ex)) k)) :
    ExitOk w ty ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload => exact payload

theorem finishFinalizer_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)) :
    ExitOk w ty ex := by
  cases h with
  | fiber _ _ notFinish _ _ _ _ => exact absurd rfl (notFinish ex)
  | finishFinalizer payload => exact payload

/-! ## Interpreter hook contracts (decisions row 190)

A saved iterator or loop frame is accepted by a protocol: an invariant that contains it and is
closed under one hook step, the postfixed (greatest-fixed-point) form. A step answers every value
that fits at every later world (decisions row 135), under every completed view typed there (row
175: the machine runs `interpRAt root m.completedExits`, whose generator and loop steps read that
view), with typed code or exit; a resumed tail lies in the invariant again with one intermediate
type. A safe loop that never finishes is admitted (`E4-TYPED-CE-036` refuted the inductive form),
and a step at a view no producer typed is not assumed (`E4-TYPED-CE-038`).

An iterator or loop frame discharges no service, and the walk passes a failure through it by the
error columns alone (`errors`, `Typed/Stack.lean`'s `popR_typed`), so a step also keeps the
requirement row from emptying (`rows`, decisions row 117 and the formal pass's G5: the side
condition of `exitOk2_transport`). Without it a loop frame at an answer no value fits carried
`die missingService` from a row requiring the scope service to an empty one (`E4-TYPED-CE-008`,
`Test/Program/H2PartOne.lean`, `MissingServiceTransport`). -/

/-- The completed views typed at a world (row 175): each listed exit's fiber is declared and the
exit fits its declaration, the `construction` post's clause. -/
def ViewTyped (w : World) (completed : List (FiberId × ExitV)) : Prop :=
  ∀ q ∈ completed, ∃ fty, w.Γ q.1 = some fty ∧ ExitOk w fty q.2

open Contracts (Greatest StepMono)

/-- A saved iterator frame's state: the world, the input and final types, the hook name. -/
abbrev IterState := World × EffTy × EffTy × EffName

/-- A saved loop frame's state: the world, the input and final types, the hook name, the cursor. -/
abbrev LoopState := World × EffTy × EffTy × EffName × Val

/-- One iterator step from `w`, its resumed tails in `I`. -/
def IteratorStep (root : ProgramSource) (I : IterState → Prop) : IterState → Prop
  | (w, tin, tout, name) =>
    tin.error = tout.error ∧
      (tout.requires = Env.Requirement.empty → tin.requires = Env.Requirement.empty) ∧
      ∀ w', w.leHost w' → ∀ completed, ViewTyped w' completed → ∀ v, Fits w' v tin.answer →
        match ((interpRAt root.program completed).iterNext name v).2 with
        | .done result => ExitOk w' tout (.success result)
        | .halt cause => ExitOk w' tout (.failure cause)
        | .resume code name' => ∃ tin', TypedProg root w' tin' code ∧ I (w', tin', tout, name')

/-- One loop step from `w`, its continued tails in `I`. -/
def LoopStep (root : ProgramSource) (I : LoopState → Prop) : LoopState → Prop
  | (w, tin, tout, name, cursor) =>
    tin.error = tout.error ∧
      (tout.requires = Env.Requirement.empty → tin.requires = Env.Requirement.empty) ∧
      ∀ w', w.leHost w' → ∀ completed, ViewTyped w' completed → ∀ v, Fits w' v tin.answer →
        match (interpRAt root.program completed).loopResume name cursor v with
        | .continue cursor' body =>
          ∃ tin', TypedProg root w' tin' body ∧ I (w', tin', tout, name, cursor')
        | .finish code => TypedProg root w' tout code

/-- An iterator frame's protocol: the greatest invariant of `IteratorStep` holds at its state. -/
abbrev IteratorProtocol (root : ProgramSource) (w : World) (tin tout : EffTy) (name : EffName) : Prop :=
  Greatest (IteratorStep root) (w, tin, tout, name)

/-- A loop frame's protocol: the greatest invariant of `LoopStep` holds at its state. -/
abbrev LoopProtocol (root : ProgramSource) (w : World) (tin tout : EffTy) (name : EffName)
    (cursor : Val) : Prop :=
  Greatest (LoopStep root) (w, tin, tout, name, cursor)

section Protocols
variable {root : ProgramSource}

@[aesop safe apply (rule_sets := [Effect4.Coind])]
theorem iteratorStep_mono : StepMono (IteratorStep root) := by
  rintro I J sub ⟨w, tin, tout, name⟩ ⟨errors, rows, next⟩
  refine ⟨errors, rows, fun w' o completed view v hv => ?_⟩
  have step := next w' o completed view v hv
  revert step
  cases ((interpRAt root.program completed).iterNext name v).2 with
  | done result => exact id
  | halt cause => exact id
  | resume code name' =>
    intro step
    obtain ⟨tin', typed, tail⟩ := step
    exact ⟨tin', typed, sub _ tail⟩

@[aesop safe apply (rule_sets := [Effect4.Coind])]
theorem loopStep_mono : StepMono (LoopStep root) := by
  rintro I J sub ⟨w, tin, tout, name, cursor⟩ ⟨errors, rows, next⟩
  refine ⟨errors, rows, fun w' o completed view v hv => ?_⟩
  have step := next w' o completed view v hv
  revert step
  cases (interpRAt root.program completed).loopResume name cursor v with
  | «continue» cursor' body =>
    intro step
    obtain ⟨tin', typed, tail⟩ := step
    exact ⟨tin', typed, sub _ tail⟩
  | finish code => exact id

theorem IteratorProtocol.unfold {w : World} {tin tout : EffTy} {name : EffName}
    (h : IteratorProtocol root w tin tout name) :
    IteratorStep root (Greatest (IteratorStep root)) (w, tin, tout, name) :=
  Greatest.unfold iteratorStep_mono h

theorem IteratorProtocol.fold {w : World} {tin tout : EffTy} {name : EffName}
    (h : IteratorStep root (Greatest (IteratorStep root)) (w, tin, tout, name)) :
    IteratorProtocol root w tin tout name :=
  Greatest.fold iteratorStep_mono h

theorem LoopProtocol.unfold {w : World} {tin tout : EffTy} {name : EffName} {cursor : Val}
    (h : LoopProtocol root w tin tout name cursor) :
    LoopStep root (Greatest (LoopStep root)) (w, tin, tout, name, cursor) :=
  Greatest.unfold loopStep_mono h

theorem LoopProtocol.fold {w : World} {tin tout : EffTy} {name : EffName} {cursor : Val}
    (h : LoopStep root (Greatest (LoopStep root)) (w, tin, tout, name, cursor)) :
    LoopProtocol root w tin tout name cursor :=
  Greatest.fold loopStep_mono h

/-- An iterator protocol holds at every later world, with the same intermediate type: its step
already answers at every later world. -/
@[aesop safe forward (rule_sets := [Effect4.Coind])]
theorem iteratorProtocol_mono {w w' : World} (ord : w.leHost w') {tin tout : EffTy}
    {name : EffName} (h : IteratorProtocol root w tin tout name) :
    IteratorProtocol root w' tin tout name := by
  obtain ⟨errors, rows, next⟩ := h.unfold
  exact IteratorProtocol.fold ⟨errors, rows, fun w'' o => next w'' (leHost_trans _ _ _ ord o)⟩

/-- A loop protocol holds at every later world, with the same intermediate type. -/
@[aesop safe forward (rule_sets := [Effect4.Coind])]
theorem loopProtocol_mono {w w' : World} (ord : w.leHost w') {tin tout : EffTy} {name : EffName}
    {cursor : Val} (h : LoopProtocol root w tin tout name cursor) :
    LoopProtocol root w' tin tout name cursor := by
  obtain ⟨errors, rows, next⟩ := h.unfold
  exact LoopProtocol.fold ⟨errors, rows, fun w'' o => next w'' (leHost_trans _ _ _ ord o)⟩

end Protocols

/-- The three named hook arrows (slice 5 brief §3.3 as amended 2026-09-23), each closed under
later worlds (row 135). The async clause types the cancellation only for an incoming failure
that is itself typed at the frame's type, at the world the failure arrives in, the evidence
`popR` holds at that arm (`E4-SCHED-CE-010`). -/
def frameProtocols (root : ProgramSource) : Contracts.FrameProtocols where
  asyncFinalizer w tin tout name := tin = tout ∧ ∀ w', w.leHost w' →
    ∀ cause, ExitOk w' tin (.failure cause) → cause.hasInterrupts = true →
      TypedProg root w' tout ((interpR root.program).cancelThenFail name cause)
  iterator := IteratorProtocol root
  loop := LoopProtocol root
  scopeExit w prev sc := ScopeLive w sc ∧ ServicesFit w prev.services

@[aesop norm simp (rule_sets := [Effect4.Coind])]
theorem frameProtocols_iterator (root : ProgramSource) :
    (frameProtocols root).iterator = IteratorProtocol root := rfl

@[aesop norm simp (rule_sets := [Effect4.Coind])]
theorem frameProtocols_loop (root : ProgramSource) :
    (frameProtocols root).loop = LoopProtocol root := rfl

/-- An iterator frame is accepted by a protocol at the current world (row 135's closure is the
protocol's own). The bank's control: it closes only with `Effect4.Coind`. -/
theorem frameAccepts_iter {root : ProgramSource} {w : World} {tin tout : EffTy} {name : EffName}
    (h : IteratorProtocol root w tin tout name) :
    Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w tin tout (.iter name) :=
  .iter name (by aesop (rule_sets := [Effect4.Coind]))

/-- A loop frame is accepted by a protocol at the current world. -/
theorem frameAccepts_loop {root : ProgramSource} {w : World} {tin tout : EffTy} {name : EffName}
    {cursor : Val} (h : LoopProtocol root w tin tout name cursor) :
    Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w tin tout
      (.loop name cursor) :=
  .loop name cursor (by aesop (rule_sets := [Effect4.Coind]))

/-- The async finalizer's clause holds at every later world. -/
theorem asyncFinalizerProtocol_mono {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    {tin tout : EffTy} {name : EffName} (h : (frameProtocols root).asyncFinalizer w tin tout name) :
    (frameProtocols root).asyncFinalizer w' tin tout name :=
  ⟨h.1, fun w'' o => h.2 w'' (leHost_trans _ _ _ ord o)⟩

namespace TypedProg

/-- **A guard's typing is the saved frame's arrow**: the body is typed at `mid`, and the frame
the evaluator saves (`saveR f kind (fun ex => k (some ex))`, `EvaluateR.lean:147`) is accepted
from `mid` to the guard's type, at every later world. -/
theorem guard_frame {root : ProgramSource} {w : World} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : TypedProg root w ty (.vis (.inr (.guard_ kind)) k)) :
    ∃ mid : EffTy, TypedProg root w mid (k none) ∧
      Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w mid ty
        (.resume kind fun ex => k (some ex)) := by
  rcases guard_inv h with ⟨mid, body, run, skip⟩ | ⟨rfl, mid, prev, sc, body, callback, live, services, widen⟩
  · exact ⟨mid, body, .resume kind _ (fun w' ord ex hex arm => run w' ord ex ⟨arm, hex⟩) skip⟩
  · refine ⟨mid, body, .scopedResume _ prev sc callback (fun w' ord => ⟨scopeLive_mono ord.1 live, ?_⟩) widen⟩
    exact servicesFit_map ord.1.2.1 ord.1.2.2.1 ord.1.2.2.2.1 ord.2 ord.1.1.2
      (serviceTy_of_le ord.1) services

end TypedProg

/-! ## Settling Case 1: Polymorphic ref allocation and read on heterogeneous heap -/

def refAllocCont : Val → RProgram
  | .handle 2 index => .vis (.inl (.refGet ⟨index⟩)) fun v => .pure (.success v)
  | _ => .pure (.success (Val.bool false))

def refAllocGetProg : RProgram :=
  .vis (.inl (.refMake (Val.bool true))) refAllocCont

theorem strongValue_bool_true (w : World) : Fits w (Val.bool true) .bool := trivial

theorem strongExit_bool (w : World) (v : Val) (hv : Fits w v .bool) :
    ExitOk w (EffTy.pure .bool) (.success v) := strongExit_success w (EffTy.pure .bool) v hv

theorem settling_ref_allocation (root : ProgramSource) (w : World) (_h0 : HeapTypedAt w ⟨0⟩ .nat) :
    TypedProg root w (EffTy.pure .bool) refAllocGetProg := by
  refine TypedProg.store (cert := Ty.bool) (strongValue_bool_true w) ?_
  intro w' _ ans hpost
  rcases hpost with ⟨key, rfl, hkey⟩
  dsimp only [refAllocCont]
  refine TypedProg.store (cert := ()) ⟨Ty.bool, hkey⟩ ?_
  intro w'' hle v hpost'
  rcases hpost' with ⟨ty', hkey', hv⟩
  have extendsΡ := hle.1.2.2.2.1
  have sameKey : w''.Ρ key = some Ty.bool := extendsΡ key Ty.bool hkey
  change w''.Ρ key = some ty' at hkey'
  rw [sameKey] at hkey'
  cases hkey'
  exact TypedProg.pure (strongExit_bool w'' v hv)

theorem settling_ref_preserves_nat (w w' : World) (ordered : w.leHost w') (h0 : HeapTypedAt w ⟨0⟩ .nat) :
    HeapTypedAt w' ⟨0⟩ .nat :=
  heapTypedAt_mono w w' ⟨0⟩ .nat ordered h0

/-! ## Settling Case 2: Addressed fork and mask with body admission -/

def forkProg (child : Body) : RProgram :=
  .vis (.inr (.fork child ⟨false, false, .inherit⟩ [])) fun ans => .pure (.success ans)

def maskProg (flag : Bool) (body : Body) : RProgram :=
  .vis (.inr (.mask flag body)) fun ans => .pure ans

theorem settling_fork (root : ProgramSource) (w : World) (child : Body) (cert : EffTy)
    (hbody : BodyTyped root w child cert) :
    TypedProg root w (EffTy.pure (.fiberOf cert.answer cert.error)) (forkProg child) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbody ?_
  intro w' _ ans hpost
  dsimp only [Ψ_F, fiberPost] at hpost
  rcases hpost with ⟨id, rfl, hid⟩
  exact TypedProg.pure ⟨⟨cert, hid, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩

theorem settling_mask (root : ProgramSource) (w : World) (flag : Bool) (body : Body) (cert : EffTy)
    (hbody : BodyTyped root w body cert) :
    TypedProg root w cert (maskProg flag body) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbody ?_
  intro w' _ ans hpost
  dsimp only [Ψ_F, fiberPost] at hpost
  exact TypedProg.pure hpost

/-! FR-09's payload inversions, restated over the one judgment under their M3a names. -/

/-! World weakening (ruling 2026-09-23, audit A4; decisions rows 87 and 135): typing survives
every later world the host order allows. Every continuation of `TypedProg` is typed at the
world its answer arrives in, so only the leaves, the demands and a guard's body need transport:
the leaves by the membership transport laws, the demands by `storePre_mono` and
`fiberPre_mono`, the body by induction. The saved stack is Kripke-closed (`Contracts`), so a
saved frame transports once its code does (`savedOk_mono`). -/

/-- Value membership persists along the host-world order, with the ledger's binder order. -/
theorem strongValue_mono (w w' : World) (ty : Ty) (v : Val) :
    w.leHost w' → Fits w v ty → Fits w' v ty :=
  fun ordered h => fits_mono ordered h

/-- Exit membership persists along the host-world order, with the ledger's binder order. -/
theorem strongExit_mono (w w' : World) (ty : EffTy) (ex : ExitV) :
    w.leHost w' → ExitOk w ty ex → ExitOk w' ty ex :=
  fun ordered h => ⟨fitsExit_mono ordered h.1, h.2⟩

section Mono
variable {w w' : World}

theorem envTyped_mono (ord : w.leHost w') {env : List Ty} {vals : List Val}
    (h : EnvTyped w env vals) : EnvTyped w' env vals :=
  ⟨h.1, fun i ty v hi hv => fits_mono ord (h.2 i ty v hi hv)⟩

/-- **A typed stack stays typed at every later world** (slice CX1): its sites are first-order
data, and their values' membership persists. A step of `pointTyped_mono` and of every arm that
builds a point at a later world. -/
theorem stackTyped_mono (ord : w.leHost w') {src : ProgramSource} :
    ∀ {ps : List ParamDecl} {stack : List (List ArgSite)},
      StackTyped src w ps stack → StackTyped src w' ps stack
  | _, [], h => h
  | _, _ :: rest, h => fun j q hq => by
    obtain ⟨site, arg, env, t, hs, hat, hc, ha, he, hr⟩ := h j q hq
    exact ⟨site, arg, env, t, hs, hat, hc, ha, envTyped_mono ord he,
      stackTyped_mono ord (stack := rest) hr⟩

theorem pointTyped_mono (ord : w.leHost w') {src : ProgramSource} {p : Point} {ty : EffTy}
    (h : PointTyped src w p ty) : PointTyped src w' p ty := by
  obtain ⟨e, env, hat, hchk, henv, hview, hstack⟩ := h
  refine ⟨e, env, hat, hchk, envTyped_mono ord henv, fun q hq => ?_, stackTyped_mono ord hstack⟩
  obtain ⟨fty, hfty, hex⟩ := hview q hq
  exact ⟨fty, ord.1.2.1 _ _ hfty, strongExit_mono _ _ _ _ ord hex⟩

/-- A typed loop point with a typed cursor stays typed at every later world (decisions row
190 (b)). -/
theorem loopPointTyped_mono (ord : w.leHost w') {src : ProgramSource} {p : Point} {ty : EffTy}
    {cursor : Val} (h : LoopPointTyped src w p ty cursor) : LoopPointTyped src w' p ty cursor := by
  obtain ⟨cursorTy, initial, test, step, result, body, env, c0, hat, hcheck, henv, hview, hc0,
    hfit, hstack⟩ := h
  refine ⟨cursorTy, initial, test, step, result, body, env, c0, hat, hcheck, envTyped_mono ord henv,
    fun q hq => ?_, hc0, fits_mono ord hfit, stackTyped_mono ord hstack⟩
  obtain ⟨fty, hfty, hex⟩ := hview q hq
  exact ⟨fty, ord.1.2.1 _ _ hfty, strongExit_mono _ _ _ _ ord hex⟩

theorem layerPointTyped_mono (ord : w.leHost w') {src : ProgramSource} {p : Point} {lt : LayerTy}
    (h : LayerPointTyped src w p lt) : LayerPointTyped src w' p lt := by
  obtain ⟨l, hat, hchk, henv, hview, hstack⟩ := h
  refine ⟨l, hat, hchk, henv, fun q hq => ?_, stackTyped_mono ord hstack⟩
  obtain ⟨fty, hfty, hex⟩ := hview q hq
  exact ⟨fty, ord.1.2.1 _ _ hfty, strongExit_mono _ _ _ _ ord hex⟩

/-- Region admission transports through the existing world order.
Consumer: the protected provider's saved and queued body positions. -/
theorem regionTyped_mono (ord : w.leHost w') {src : ProgramSource} {body : Region} {ty : EffTy}
    (typed : RegionTyped src w body ty) : RegionTyped src w' body ty := by
  fun_cases cata_region (regionTypingAlgebra src w) body with
  | case1 => exact pointTyped_mono ord typed
  | case2 | case3 =>
    obtain ⟨lt, same, point, scope, memo⟩ := typed
    exact ⟨lt, same, layerPointTyped_mono ord point, scopeLive_mono ord.1 scope,
      memoLive_mono ord.1 memo⟩
  | case4 =>
    obtain ⟨bodyTy, point, same, carriers⟩ := typed
    refine ⟨bodyTy, pointTyped_mono ord point, same, fun key keyed carrier declared => ?_⟩
    exact carriers key keyed carrier (serviceTy_of_le ord.1 key carrier declared)

/-- Protected-entry update admission uses the existing transitive host order.
Consumer: bodyTyped_mono. -/
theorem contextUpdateTyped_mono (ord : w.leHost w') {update : Env.ContextUpdate}
    (typed : ContextUpdateTyped w update) : ContextUpdateTyped w' update :=
  fun later ordered => typed later (leHost_trans _ _ _ ord ordered)

/-- A finalizer's admission is upward closed (decisions row 151 (a″)): a capture's
environment and services by membership's transport, a scope's presence by scope persistence. -/
theorem finalizerAdmitted_mono (root : ProgramSource) (ord : w.leHost w') (fin : FinName)
    (h : FinalizerAdmitted root w fin) : FinalizerAdmitted root w' fin := by
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  have hRho : TableExtends w.Ρ w'.Ρ := ord.1.2.2.2.1
  cases fin with
  | foreign c =>
    obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, hsvc, hstack⟩ := h
    exact ⟨acquire, release, env, t, a, hnode, hcheck, hacq, envTyped_mono ord henv,
      servicesFit_map ord.1.2.1 hPi hRho ord.2 ord.1.1.2 (serviceTy_of_le ord.1)
        hsvc, stackTyped_mono ord hstack⟩
  | release _ _ => exact h
  | closeChildScope _ | closeChildOnFailure _ | detachFromParent _ _ => exact scopeLive_mono ord.1 h
  | interruptFiber _ _ => exact isSome_extends ord.1.2.1 h
  | awaitNewChildren _ | parkThen _ | memoEntry _ _ | memoDone _ _ => trivial

theorem bodyTyped_mono (ord : w.leHost w') {src : ProgramSource} {b : Body} {ty : EffTy}
    (h : BodyTyped src w b ty) : BodyTyped src w' b ty := by
  have services : ∀ {ctx : Ctx}, ServicesFit w ctx.services → ServicesFit w' ctx.services :=
    fun h => servicesFit_map ord.1.2.1 ord.1.2.2.1 ord.1.2.2.2.1 ord.2 ord.1.1.2
      (serviceTy_of_le ord.1) h
  cases h with
  | at_ p ty h => exact .at_ p ty (pointTyped_mono ord h)
  | fin name ex h hex =>
    exact .fin name ex (finalizerAdmitted_mono src ord name h) (fitsExit_mono ord hex)
  | raceCleanup race => exact .raceCleanup race
  | acquireIn p ctx ty h node hsvc =>
    exact .acquireIn p ctx ty (pointTyped_mono ord h) node (services hsvc)
  | release p prev ty h hsvc => exact .release p prev ty (pointTyped_mono ord h) (services hsvc)
  | layerBuild p m scope lt h live memo =>
    exact .layerBuild p m scope lt (layerPointTyped_mono ord h) (scopeLive_mono ord.1 live)
      (memoLive_mono ord.1 memo)
  | region body bodyTy ty typed answer error =>
    exact .region body bodyTy ty (regionTyped_mono ord typed) answer error
  | contextEntry update body flag bodyTy ty typed answer error updateTyped =>
    exact .contextEntry update body flag bodyTy ty (regionTyped_mono ord typed) answer error
      (contextUpdateTyped_mono ord updateTyped)

/-- Every store row's demand is upward closed (all 31 rows). -/
theorem storePre_mono (root : ProgramSource) (ord : w.leHost w') (op : SyncOp)
    (cert : StoreCert op) (h : storePre root w op cert) : storePre root w' op cert := by
  have hRho : TableExtends w.Ρ w'.Ρ := ord.1.2.2.2.1
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  cases op with
  | refMake initial =>
    simp only [storePre] at h ⊢
    exact fits_mono ord h
  | refGet cell =>
    simp only [storePre] at h ⊢
    obtain ⟨ty, hty⟩ := h
    exact ⟨ty, hRho _ _ hty⟩
  | refUpdate cell _ _ | refGetAndUpdate cell _ _ | refUpdateAndGet cell _ _
  | refUpdateSome cell _ _ | refGetAndUpdateSome cell _ _ | refUpdateSomeAndGet cell _ _
  | refModify cell _ _ | refModifySome cell _ _ =>
    simp only [storePre] at h ⊢
    obtain ⟨ty, hty, maps⟩ := h
    exact ⟨ty, hRho _ _ hty, maps.mono ord⟩
  | refSet cell v | refGetAndSet cell v | refSetAndGet cell v =>
    simp only [storePre] at h ⊢
    obtain ⟨ty, hty, hv⟩ := h
    exact ⟨ty, hRho _ _ hty, fits_mono ord hv⟩
  | deferredIsDone key | deferredPoll key | deferredAwaitCleanup key _ _
  | deferredInterruptWith key _ =>
    simp only [storePre] at h ⊢
    exact isSome_extends hPi h
  | deferredCompleteWith key completion =>
    simp only [storePre] at h ⊢
    obtain ⟨a, e, hkey, typed⟩ := h
    refine ⟨a, e, hPi _ _ hkey, ?_⟩
    cases completion with
    | ofExit ex => exact strongExit_mono _ _ _ _ ord typed
    | ofRefGet cell =>
      obtain ⟨t, ht, sub⟩ := typed
      exact ⟨t, hRho _ _ ht, sub⟩
  | deferredMake | memoBuild _ _ | memoGet _ _ => exact h
  | scopeAdd scope fin => exact ⟨scopeLive_mono ord.1 h.1, finalizerAdmitted_mono root ord fin h.2⟩
  | scopeRemove scope _ | scopeIsClosed scope | scopeFork scope _ =>
    simp only [storePre] at h ⊢
    exact scopeLive_mono ord.1 h
  | memoComplete layer _ ex =>
    obtain ⟨l, lt, hat, hcheck, hex⟩ := h
    exact ⟨l, lt, hat, hcheck, strongExit_mono _ _ _ _ ord hex⟩
  | clockNow | sleepCancel _ _ | scopeMake _ | memoFork _ | memoRelease _ _ =>
    exact trivial

theorem asyncPre_mono (root : ProgramSource) (ord : w.leHost w') (register : EffName)
    (cert : EffTy) (h : asyncPre root w register cert) : asyncPre root w' register cert := by
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  unfold asyncPre at h ⊢
  split at h
  · exact h
  · obtain ⟨a, e, hc, ha, he⟩ := h
    exact ⟨a, e, hPi _ _ hc, ha, he⟩
  · obtain ⟨a, e, hc, ha, he⟩ := h
    exact ⟨a, e, hPi _ _ hc, ha, he⟩
  · exact h
  · exact h
  · exact h.elim

/-- Every fiber row's demand is upward closed (all 41 rows). -/
theorem fiberPre_mono (root : ProgramSource) (ord : w.leHost w') (op : FiberOp)
    (cert : FiberCert op) (h : fiberPre root w op cert) : fiberPre root w' op cert := by
  have hGamma : TableExtends w.Γ w'.Γ := ord.1.2.1
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  have hRho : TableExtends w.Ρ w'.Ρ := ord.1.2.2.2.1
  cases op with
  | fork body _ _ => exact bodyTyped_mono ord h
  | mask _ body => exact bodyTyped_mono ord h
  -- row 139: scope entries persist along the host order (`scopeLive_mono`, row 156), the fiber
  -- table grows
  | forkIn child _ scope _ => exact ⟨pointTyped_mono ord h.1, scopeLive_mono ord.1 h.2⟩
  | forkScoped child _ _ => exact pointTyped_mono ord h
  | «scoped» body => exact pointTyped_mono ord h
  | gen p => exact ⟨pointTyped_mono ord h.1, h.2⟩
  | loop p _ => exact loopPointTyped_mono ord h
  | await target _ =>
    simp only [fiberPre] at h ⊢
    exact isSome_extends hGamma h
  | awaitAll targets | awaitAllFailFast targets =>
    simp only [fiberPre] at h ⊢
    obtain ⟨a, e, hc, hall⟩ := h
    refine ⟨a, e, hc, fun t ht => ?_⟩
    obtain ⟨fty, hf, ha, he⟩ := hall t ht
    exact ⟨fty, hGamma _ _ hf, ha, he⟩
  | raceAll entrants _ | raceAllFirst entrants _ =>
    simp only [fiberPre] at h ⊢
    intro p hp
    obtain ⟨ty, hpt, ha, he⟩ := h p hp
    exact ⟨ty, pointTyped_mono ord hpt, ha, he⟩
  | async register _ => exact asyncPre_mono root ord register cert h
  | setContext ctx =>
    simp only [fiberPre] at h ⊢
    exact servicesFit_map ord.1.2.1 hPi hRho ord.2 ord.1.1.2 (serviceTy_of_le ord.1) h
  | getContext | snapshotChildren => exact h
  | refuse _ | raceRegister _ => exact (h : False).elim
  | interruptAs target _ | interrupt target | interruptScoped target =>
    simp only [fiberPre] at h ⊢
    exact isSome_extends hGamma h
  | runIn target scope =>
    simp only [fiberPre] at h ⊢
    exact ⟨isSome_extends hGamma h.1, scopeLive_mono ord.1 h.2⟩
  | interruptAll targets _ =>
    simp only [fiberPre] at h ⊢
    exact fun t ht => isSome_extends hGamma (h t ht)
  | scopeExit _ scope _ =>
    simp only [fiberPre] at h ⊢
    exact scopeLive_mono ord.1 h
  | closeScope scope _ =>
    simp only [fiberPre] at h ⊢
    exact ⟨scopeLive_mono ord.1 h.1, fitsExit_mono ord h.2⟩
  | getId | yieldNow _ | ambientScope | sync _ | suspend _ | getInterruptible
  | awaitNewChildren _ | guard_ _ | unguard _
  | finishFinalizer _ | construction | foreignRelease _ _
  | closeWalk _ _ _ | cancelRace _ | dropObservers _
  | frontier _ _ => exact trivial
  | closeIter _ order _ =>
    exact ⟨fun fin hf => finalizerAdmitted_mono root ord fin (h.1 fin hf), fitsExit_mono ord h.2⟩

end Mono

/-- **`TypedProg` is world-monotone** (closes `typedProg_mono`; seat ALGEBRA's P2,
2026-10-01). Every continuation clause already quantifies over later worlds, so only the
leaves, the demands and the guard's body need transport. -/
theorem typedProg_mono (root : ProgramSource) (w w' : World) (ty : EffTy) (p : RProgram)
    (ord : w.leHost w') (h : TypedProg root w ty p) : TypedProg root w' ty p := by
  refine ProgramArrow.mono ?_ ?_ ?_ ord h
  · intro before after input op cert ordered pre
    exact storePre_mono root ordered op cert pre
  · intro before after input op cert ordered pre
    exact fiberPre_mono root ordered op cert pre
  · intro before after input position exit ordered fits
    exact strongExit_mono before after position exit ordered fits

/-- A saved frame of the typed state transports along the host order. -/
theorem savedOk_mono (root : ProgramSource) (w w' : World) (final : EffTy) (x : RSaved)
    (ord : w.leHost w')
    (h : Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w final x) :
    Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w' final x :=
  Contracts.savedOk_mono (fun {w w'} {ty} {p} o hp => typedProg_mono root w w' ty p o hp) ord h

/-! ## `TypedProg` along an appended row table (decisions rows 115, 116; TY-12)

An appended row extends the source's signature under the same service declarations
(`SigApp.rows_append`), so every precondition that reads the source transports along it: the
checked points (`check_ext`), the memo layer (`checkLayer_ext`) and the host-row entry, whose
domain bit puts the operation in the shorter table's domain, where the longer table's row is the
same (`bitEntry_rows_append`). No postcondition reads the source. So `TypedProg` is monotone along
an appended table (`typedProg_rows_append`), beside its monotonicity along the world order
(`typedProg_mono`). Without the bit it is not (`Test/Program/TypedProgRows.lean`,
`typedProg_not_table_monotone_of`). Moved from that battery (seat A), where it was proved under
the entry's transport as a hypothesis; the bit makes it hold outright. -/

/-- **Row 116's entry transports along an appended table** (proved): the bit puts the operation in
the shorter domain, where the longer table's row is the same, so its check at the request type is
too. -/
theorem bitEntry_rows_append (src src' : ProgramSource) (t' : RowTable)
    (htab : src'.table = src.table ++ t') (op : NativeOp) (cert : EffTy)
    (h : bitEntry src op cert) : bitEntry src' op cert := by
  obtain ⟨hdom, reqTy, t, hrowTy, ha, he⟩ := h
  have hrow := (rows_append src.table t').row op hdom
  show (nativeSignature src'.table).dom op = true ∧
    ∃ reqTy t, rowTy ((nativeSignature src'.table).rowOf op) reqTy = some t ∧
      t.answer.sub cert.answer = true ∧ t.error.sub cert.error = true
  rw [htab, hrow.2]
  exact ⟨hrow.1, reqTy, t, hrowTy, ha, he⟩

section RowsAppend

variable (src src' : ProgramSource) (t' : RowTable)
  (hprog : src'.program = src.program) (htab : src'.table = src.table ++ t')
  (hsvc : src'.services = src.services)
include hprog htab hsvc

/-- The longer source's signature extends the shorter one's: an appended row table under the
same service declarations, and the same program, so the same definition block
(`SigExtends.withDefs`, decisions row 328). -/
theorem signature_rows_append : SigExtends src.signature src'.signature := by
  have htables : SigExtends src.sig.signature src'.sig.signature := by
    show SigExtends src.sig.signature (SigApp.mk src'.table src'.services).signature
    rw [htab, hsvc]
    exact SigApp.rows_append src.sig t'
  show SigExtends (src.sig.signature.withDefs src.program.defsOf)
    (src'.sig.signature.withDefs src'.program.defsOf)
  rw [hprog]
  exact htables.withDefs _

/-- The signature at a path extends along an appended table (`SigExtends.withParams`): the same
program, so the same scope. -/
theorem scopeSig_rows_append (path : List Nat) :
    SigExtends (src.scopeSig path) (src'.scopeSig path) := by
  show SigExtends (src.signature.withParams (scopeParams src.program path))
    (src'.signature.withParams (scopeParams src'.program path))
  rw [hprog]
  exact (signature_rows_append src src' t' hprog htab hsvc).withParams _

/-- A typed stack stays typed along an appended table (slice CX1): each site's check extends. -/
theorem stackTyped_rows_append {w : World} :
    ∀ {ps : List ParamDecl} {stack : List (List ArgSite)},
      StackTyped src w ps stack → StackTyped src' w ps stack
  | _, [], h => h
  | _, _ :: rest, h => fun j q hq => by
    obtain ⟨site, arg, env, t, hs, hat, hc, ha, he, hr⟩ := h j q hq
    refine ⟨site, arg, env, t, hs, ?_, ?_, ha, he, ?_⟩
    · rw [hprog]
      exact hat
    · rw [hprog]
      exact check_ext (scopeSig_rows_append src src' t' hprog htab hsvc site.path) hc
    · exact (congrArg (fun program => StackTyped src' w (scopeParams program site.path) rest)
        hprog).mpr (stackTyped_rows_append (stack := rest) hr)

theorem pointTyped_rows_append {w : World} {point : Point} {ty : EffTy}
    (h : PointTyped src w point ty) : PointTyped src' w point ty := by
  obtain ⟨e, env, hat, hcheck, henv, hview, hstack⟩ := h
  refine ⟨e, env, ?_, ?_, henv, hview, ?_⟩
  · rw [hprog]
    exact hat
  · rw [hprog]
    exact check_ext (scopeSig_rows_append src src' t' hprog htab hsvc point.path) hcheck
  · rw [hprog]
    exact stackTyped_rows_append src src' t' hprog htab hsvc hstack

theorem loopPointTyped_rows_append {w : World} {point : Point} {ty : EffTy} {cursor : Val}
    (h : LoopPointTyped src w point ty cursor) : LoopPointTyped src' w point ty cursor := by
  obtain ⟨cursorTy, initial, test, step, result, body, env, c0, hat, hcheck, henv, hview, hc0,
    hfit, hstack⟩ := h
  refine ⟨cursorTy, initial, test, step, result, body, env, c0, ?_, ?_, henv, hview, ?_, hfit, ?_⟩
  · rw [hprog]
    exact hat
  · rw [hprog]
    exact check_ext (scopeSig_rows_append src src' t' hprog htab hsvc point.path) hcheck
  · rw [(signature_rows_append src src' t' hprog htab hsvc).termTy env initial]
    exact hc0
  · rw [hprog]
    exact stackTyped_rows_append src src' t' hprog htab hsvc hstack

theorem layerPointTyped_rows_append {w : World} {point : Point} {lt : LayerTy}
    (h : LayerPointTyped src w point lt) : LayerPointTyped src' w point lt := by
  obtain ⟨l, hat, hcheck, henv, hview, hstack⟩ := h
  refine ⟨l, ?_, ?_, henv, hview, ?_⟩
  · rw [hprog]
    exact hat
  · rw [hprog]
    exact checkLayer_ext (scopeSig_rows_append src src' t' hprog htab hsvc point.path) hcheck
  · rw [hprog]
    exact stackTyped_rows_append src src' t' hprog htab hsvc hstack

/-- A capture typed under the shorter source is typed under the longer one: its node is the
same program's, and the checker's verdicts extend along an appended row table. -/
theorem captureTyped_rows_append {w : World} {c : Capture}
    (h : CaptureTyped src w c) : CaptureTyped src' w c := by
  obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, services, hstack⟩ := h
  refine ⟨acquire, release, env, t, a, ?_, ?_, ?_, henv, services, ?_⟩
  · rw [hprog]
    exact hnode
  · rw [hprog]
    exact check_ext (scopeSig_rows_append src src' t' hprog htab hsvc c.path) hcheck
  · rw [hprog]
    exact check_ext (scopeSig_rows_append src src' t' hprog htab hsvc c.path) hacq
  · rw [hprog]
    exact stackTyped_rows_append src src' t' hprog htab hsvc hstack

theorem finalizerAdmitted_rows_append {w : World} {fin : FinName}
    (h : FinalizerAdmitted src w fin) : FinalizerAdmitted src' w fin := by
  cases fin with
  | foreign c => exact captureTyped_rows_append src src' t' hprog htab hsvc h
  | _ => exact h

/-- Region admission retains its source at an appended host-row table.
Consumer: bodyTyped_rows_append. -/
theorem regionTyped_rows_append {w : World} {body : Region} {ty : EffTy}
    (typed : RegionTyped src w body ty) : RegionTyped src' w body ty := by
  fun_cases cata_region (regionTypingAlgebra src w) body with
  | case1 => exact pointTyped_rows_append src src' t' hprog htab hsvc typed
  | case2 | case3 =>
    obtain ⟨lt, same, point, scope, memo⟩ := typed
    exact ⟨lt, same, layerPointTyped_rows_append src src' t' hprog htab hsvc point, scope, memo⟩
  | case4 =>
    obtain ⟨bodyTy, point, same, carriers⟩ := typed
    exact ⟨bodyTy, pointTyped_rows_append src src' t' hprog htab hsvc point, same, carriers⟩

theorem bodyTyped_rows_append {w : World} {body : Body} {ty : EffTy}
    (h : BodyTyped src w body ty) : BodyTyped src' w body ty := by
  cases h with
  | at_ p ty hp => exact .at_ p ty (pointTyped_rows_append src src' t' hprog htab hsvc hp)
  | fin name ex hf hex =>
    exact .fin name ex (finalizerAdmitted_rows_append src src' t' hprog htab hsvc hf) hex
  | raceCleanup race => exact .raceCleanup race
  | acquireIn p ctx ty hp node services =>
    refine .acquireIn p ctx ty (pointTyped_rows_append src src' t' hprog htab hsvc hp) ?_ services
    rw [hprog]
    exact node
  | release p prev ty hp services =>
    exact .release p prev ty (pointTyped_rows_append src src' t' hprog htab hsvc hp) services
  | layerBuild p m scope lt hp live memo =>
    exact .layerBuild p m scope lt (layerPointTyped_rows_append src src' t' hprog htab hsvc hp) live
      memo
  | region body bodyTy ty typed answer error =>
    exact .region body bodyTy ty (regionTyped_rows_append src src' t' hprog htab hsvc typed)
      answer error
  | contextEntry update body flag bodyTy ty typed answer error updateTyped =>
    exact .contextEntry update body flag bodyTy ty
      (regionTyped_rows_append src src' t' hprog htab hsvc typed) answer error updateTyped

theorem storePre_rows_append {w : World} {op : SyncOp} {cert : StoreCert op}
    (h : storePre src w op cert) : storePre src' w op cert := by
  cases op with
  | memoGet layer m =>
    obtain ⟨l, lt, hat, hcheck, herr⟩ := h
    refine ⟨l, lt, ?_, ?_, herr⟩
    · rw [hprog]
      exact hat
    · rw [hprog]
      exact checkLayer_ext (scopeSig_rows_append src src' t' hprog htab hsvc layer.1) hcheck
  | memoBuild layer m =>
    obtain ⟨l, lt, hat, hcheck, hcert⟩ := h
    refine ⟨l, lt, ?_, ?_, hcert⟩
    · rw [hprog]
      exact hat
    · rw [hprog]
      exact checkLayer_ext (scopeSig_rows_append src src' t' hprog htab hsvc layer.1) hcheck
  | memoComplete layer m ex =>
    obtain ⟨l, lt, hat, hcheck, hex⟩ := h
    refine ⟨l, lt, ?_, ?_, hex⟩
    · rw [hprog]
      exact hat
    · rw [hprog]
      exact checkLayer_ext (scopeSig_rows_append src src' t' hprog htab hsvc layer.1) hcheck
  | scopeAdd scope fin =>
    exact ⟨h.1, finalizerAdmitted_rows_append src src' t' hprog htab hsvc h.2⟩
  | _ => exact h

omit hprog hsvc in
theorem asyncPre_rows_append {w : World} {register : EffName} {cert : EffTy}
    (h : asyncPre src w register cert) : asyncPre src' w register cert := by
  cases register with
  | external op req _ => exact bitEntry_rows_append src src' t' htab op cert h
  | store name => cases name <;> exact h
  | _ => exact h

theorem fiberPre_rows_append {w : World} {op : FiberOp} {cert : FiberCert op}
    (h : fiberPre src w op cert) : fiberPre src' w op cert := by
  cases op with
  | raceAll entrants race | raceAllFirst entrants race =>
    intro p hp
    obtain ⟨ty, hpt, ha, he⟩ := h p hp
    exact ⟨ty, pointTyped_rows_append src src' t' hprog htab hsvc hpt, ha, he⟩
  | async register token => exact asyncPre_rows_append src src' t' htab h
  | «scoped» body => exact pointTyped_rows_append src src' t' hprog htab hsvc h
  | mask flag body => exact bodyTyped_rows_append src src' t' hprog htab hsvc h
  | forkScoped child options path => exact pointTyped_rows_append src src' t' hprog htab hsvc h
  | fork body options path => exact bodyTyped_rows_append src src' t' hprog htab hsvc h
  | forkIn child options scope path =>
    exact ⟨pointTyped_rows_append src src' t' hprog htab hsvc h.1, h.2⟩
  | gen p =>
    refine ⟨pointTyped_rows_append src src' t' hprog htab hsvc h.1, ?_⟩
    rw [hprog]
    exact h.2
  | loop p name => exact loopPointTyped_rows_append src src' t' hprog htab hsvc h
  | closeIter _ order _ =>
    exact ⟨fun fin hf => finalizerAdmitted_rows_append src src' t' hprog htab hsvc (h.1 fin hf), h.2⟩
  | _ => exact h

/-- **`TypedProg` is monotone along an appended row table** (TY-12's positive control, proved;
rows 115, 116): the same program typed under the shorter source is typed under the longer one, at
every world and type. -/
theorem typedProg_rows_append :
    ∀ {w : World} {ty : EffTy} {p : RProgram}, TypedProg src w ty p → TypedProg src' w ty p := by
  intro w ty p h
  unfold TypedProg at h
  generalize unit_eq : () = input at h
  clear unit_eq
  induction h with
  | pure exit => exact .pure exit
  | store cert pre next _entry ih =>
    exact .store cert (storePre_rows_append src src' t' hprog htab hsvc pre)
      fun w' hle ans hpost => ih w' hle ans hpost
  | fiber notGuard notUnguard notFinish notScopeExit cert pre next _entry ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert
      (fiberPre_rows_append src src' t' hprog htab hsvc pre)
      fun w' hle ans hpost => ih w' hle ans hpost
  | guard mid body run skip _entry ihbody ihrun =>
    exact .guard mid ihbody (fun w' hle ex hpost => ihrun w' hle ex hpost) skip
  | unguard payload entry => exact .unguard payload entry
  | finishFinalizer payload entry => exact .finishFinalizer payload entry
  | scopedGuard mid prev sc _ callback live services widen _entry ihbody =>
    exact .scopedGuard mid prev sc ihbody callback live services widen

end RowsAppend

end Effect4.Program.Typed

-- `SavedOk` transport joins it (row 87: `preds_savedOk_mono`), so it is counted once.
