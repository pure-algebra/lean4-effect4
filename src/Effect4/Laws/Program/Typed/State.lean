import Effect4.Laws.Program.Typed.Sources
import Aesop

/-!
# Typed/State — the typed-state skeleton (GENERATED)

Emitted by `#emit_typed_state` (`Laws/Auto/TypedStateGen.lean`) from the position census of
[Effect4.Program.Sched.RState, Effect4.Program.Sched.RCmd] and the source table `Typed/Sources.lean`. One `Ok` per owner, nested along the
containment edges, parametric in the carrier predicates `Preds`. Regenerate; never edit.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed

-- `W` is the typing tables and the store: layer 1 instantiates it.
variable {W : Type}

/-- Where a position's expected type comes from, as data the predicates read. -/
inductive Expect
  | root
  | fiber (id : Effect4.FiberId)
  | promise (cell : Effect4.Machine.DeferredKey)
  | refColumn
  | row (op : Effect4.Program.NativeOp)
  | checker (point : Effect4.Program.Point)
  | const (ty : Effect4.Program.EffTy)
  | hook (name : String)

structure Preds (W : Type) where
  program : W → Expect → Effect4.Program.Sched.RProgram → Prop
  StackOk : W → Expect → List Effect4.Program.Sched.ScopeFrame → Prop
  InterruptOnly : W → Expect → Option Effect4.Machine.CauseV → Prop
  PendingOk : W → Expect → List (Effect4.Machine.Pending Effect4.Program.EffName Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann) → Prop
  exit : W → Expect → Effect4.Machine.ExitV → Prop
  ResumeOk : W → Expect → Effect4.Program.Sched.RProgram → Prop
  ServiceOk : W → Expect → Effect4.Machine.Ctx → Prop
  RaceOk : W → Expect → List (Effect4.Machine.Race Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann Effect4.Program.Sched.RProgram) → Prop
  HeapNat : W → Effect4.Machine.Stores → Prop
  PromiseTable : W → Effect4.Machine.Stores → Prop
  CaptureOk : W → Expect → List Effect4.Store.Val → Prop

structure RSavedOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Program.Sched.RSaved) : Prop where
  c0 : P.program w e x.current
  c1 : P.StackOk w e x.stack
  c2 : P.InterruptOnly w e x.interruptedCause

def TaskOk (P : Preds W) (w : W) (e : Expect) : Effect4.Machine.Task Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann Effect4.Program.Sched.RProgram → Prop
  | .start _child => True
  | .resume _target _token answer => P.ResumeOk w e answer
  | .wake _list _phase => True

structure BucketOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.Bucket Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann Effect4.Program.Sched.RProgram) : Prop where
  c0 : ∀ v0, v0 ∈ x.tasks → TaskOk P w e v0

structure DispatcherOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.Dispatcher Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann Effect4.Program.Sched.RProgram) : Prop where
  c0 : ∀ v0, v0 ∈ x.buckets → BucketOk P w e v0

structure RunFiberOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.RunFiber Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann Effect4.Machine.Ctx Effect4.Program.Sched.RProgram Effect4.Program.Sched.RSaved) : Prop where
  c0 : RSavedOk P w (.fiber (x.id)) x.frame
  c1 : P.PendingOk w e x.pending
  c2 : ∀ v0, x.finalizing = some v0 → P.exit w (.fiber (x.id)) v0
  c3 : ∀ v0, x.exit = some v0 → P.exit w (.fiber (x.id)) v0
  c4 : DispatcherOk P w e x.dispatcher
  c5 : P.ServiceOk w e x.context

structure CaptureOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.Capture) : Prop where
  c0 : P.CaptureOk w e x.env
  c1 : P.ServiceOk w e x.ctx

def FinNameOk (P : Preds W) (w : W) (e : Expect) : Effect4.Machine.FinName → Prop
  | .interruptFiber _fiber _skipSelf => True
  | .closeChildScope _scope => True
  | .detachFromParent _parent _key => True
  | .release _label _fails => True
  | .awaitNewChildren _snapshot => True
  | .parkThen _slot => True
  | .foreign capture => CaptureOk P w e capture
  | .closeChildOnFailure _scope => True
  | .memoEntry _layer _memoMap => True
  | .memoDone _layer _memoMap => True

def ScopeStateOk (P : Preds W) (w : W) (e : Expect) : Effect4.ScopeState Nat Effect4.Machine.FinName Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann → Prop
  | .empty => True
  | .openEmpty => True
  | .openInline _key finalizer => FinNameOk P w e finalizer
  | .openMap entries => ∀ v0, v0 ∈ entries → FinNameOk P w e (v0).2
  | .closed _exit => True  -- REFUSED Effect4.ScopeState.closed.exit: the release's exit parameter is typed at the acquire's exit; rc.112 says Exit<unknown, unknown> (composed graph §9, DI owed)

structure ScopeOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Scope Nat Effect4.Machine.FinName Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann) : Prop where
  c0 : ScopeStateOk P w e x.state

structure ScopeEntryOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.ScopeEntry) : Prop where
  c0 : ScopeOk P w e x.scope

structure ScopeStoreOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.ScopeStore) : Prop where
  c0 : ∀ v0, v0 ∈ x.entries → ScopeEntryOk P w e v0

structure MemoEntryOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.MemoEntry) : Prop where
  c0 : FinNameOk P w e x.finalizer

structure MemoMapOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.MemoMap) : Prop where
  c0 : ∀ v0, v0 ∈ x.entries → MemoEntryOk P w e (v0).2

structure StoresOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.Stores) : Prop where
  c0 : P.HeapNat w x
  c1 : P.PromiseTable w x
  c2 : ScopeStoreOk P w e x.scopes
  c3 : ∀ v0, v0 ∈ x.memo → MemoMapOk P w e v0
  c4 : True  -- REFUSED Effect4.Machine.Stores.externals: external rows are the table-aware slice (DI-57); the reference parks them forever

structure RunMachineOk (P : Preds W) (w : W) (e : Expect) (x : Effect4.Machine.RunMachine Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann Effect4.Machine.Ctx Effect4.Machine.Stores Effect4.Program.Sched.RProgram Effect4.Program.Sched.RSaved Unit) : Prop where
  c0 : ∀ v0, v0 ∈ x.fibers → RunFiberOk P w e v0
  c1 : P.RaceOk w e x.races
  c2 : StoresOk P w e x.state

def CmdOk (P : Preds W) (w : W) (e : Expect) : Effect4.Machine.Cmd Effect4.Program.EffName Effect4.Program.EffThunk Effect4.Machine.Val Effect4.Machine.Err Effect4.Machine.Defect Effect4.FiberId Effect4.Machine.Ann Effect4.Program.Sched.RProgram → Prop
  | .evaluate _fiber => True
  | .loop _fiber _yielding => True
  | .deliver _fiber _yielding => True
  | .finish fiber exit => P.exit w (.fiber (fiber)) exit
  | .resume _fiber _token answer => P.ResumeOk w e answer
  | .launch _race => True
  | .enrollRace _race _child => True
  | .registrationDone _race _yielding => True
  | .interruptTarget _target _who _extra => True
  | .afterInterrupt _host _yielding _kind => True
  | .raceCancel _race _host _yielding _remaining _visited => True
  | .trackChild _parent _child => True
  | .observe fiber exit _observer => P.exit w (.fiber (fiber)) exit
  | .exitDone _fiber => True
  | .closeParAwait _host _yielding _fibers => True
  | .link _mode _scope _target _interruptor _extra => True
  | .drainDue => True
  | .wake _list _phase => True

abbrev RStateOk (P : Preds W) (w : W) (x : Effect4.Program.Sched.RState) : Prop := RunMachineOk P w Expect.root x
abbrev RCmdOk (P : Preds W) (w : W) (x : Effect4.Program.Sched.RCmd) : Prop := CmdOk P w Expect.root x

/-! ## The search: `repeat constructor` on the intro side, the accessors on the elim side -/

attribute [aesop safe constructors] RSavedOk
attribute [aesop safe forward] RSavedOk.c0 RSavedOk.c1 RSavedOk.c2
attribute [aesop norm unfold] TaskOk
attribute [aesop safe constructors] BucketOk
attribute [aesop safe forward] BucketOk.c0
attribute [aesop safe constructors] DispatcherOk
attribute [aesop safe forward] DispatcherOk.c0
attribute [aesop safe constructors] RunFiberOk
attribute [aesop safe forward] RunFiberOk.c0 RunFiberOk.c1 RunFiberOk.c2 RunFiberOk.c3 RunFiberOk.c4 RunFiberOk.c5
attribute [aesop safe constructors] CaptureOk
attribute [aesop safe forward] CaptureOk.c0 CaptureOk.c1
attribute [aesop norm unfold] FinNameOk
attribute [aesop norm unfold] ScopeStateOk
attribute [aesop safe constructors] ScopeOk
attribute [aesop safe forward] ScopeOk.c0
attribute [aesop safe constructors] ScopeEntryOk
attribute [aesop safe forward] ScopeEntryOk.c0
attribute [aesop safe constructors] ScopeStoreOk
attribute [aesop safe forward] ScopeStoreOk.c0
attribute [aesop safe constructors] MemoEntryOk
attribute [aesop safe forward] MemoEntryOk.c0
attribute [aesop safe constructors] MemoMapOk
attribute [aesop safe forward] MemoMapOk.c0
attribute [aesop safe constructors] StoresOk
attribute [aesop safe forward] StoresOk.c0 StoresOk.c1 StoresOk.c2 StoresOk.c3 StoresOk.c4
attribute [aesop safe constructors] RunMachineOk
attribute [aesop safe forward] RunMachineOk.c0 RunMachineOk.c1 RunMachineOk.c2
attribute [aesop norm unfold] CmdOk
/-! ## Refused (named debt; each is a decisions or DI row)
- Effect4.ScopeState.closed.exit: the release's exit parameter is typed at the acquire's exit; rc.112 says Exit<unknown, unknown> (composed graph §9, DI owed)
- Effect4.Machine.Stores.externals: external rows are the table-aware slice (DI-57); the reference parks them forever
-/


end Effect4.Program.Typed
