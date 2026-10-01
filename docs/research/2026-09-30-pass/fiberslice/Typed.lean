import Research.Pass.FiberSlice.Core
import Research.Pass.FiberSlice.Proofs
import Effect4.Laws.Program.Typed.Assembly

/-! Task 3, the typed layer: the M6-dependent statements the slice owes, elaborated against the
real typed world, reference machine and typed state, so they are exact. They are declared as
obligations in the repository's style (`ProofGraph.Obligation … := ⟨⟩`), not proved: each
depends on M6. The runtime half they compose with is proved in `Proofs.lean`
(`envelopeD_fits_table`, `fits_narrower`). Research evidence, outside the Test root. -/

set_option autoImplicit false

namespace Research.Pass.FiberSlice.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Research.Pass.FiberSlice

/-- `fiberDecl` over any instantiation of the machine: it reads only `fiber?` and the origin.
At the native machine it is `fiberDecl`; at the reference machine it is what M6 reads. -/
def fiberDeclOf {κ φ η : Type} (sig : Signature NativeOp) (root : NativeEff)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores κ φ η) (id : FiberId) :
    Option EffTy :=
  match m.fiber? id with
  | none => none
  | some f =>
    match f.origin with
    | .root => if id = ⟨0⟩ then typeOfProgram sig root else none
    | .forked _ _ site => siteDecl sig root site

/-- At the native machine, `fiberDeclOf` is the prototype's `fiberDecl`. -/
theorem fiberDeclOf_native (sig : Signature NativeOp) (root : NativeEff) (m : NativeMachine) :
    fiberDeclOf sig root m = fiberDecl sig root m := by
  funext id
  unfold fiberDeclOf fiberDecl
  cases m.fiber? id with
  | none => rfl
  | some f =>
    cases f.origin with
    | root => rfl
    | forked _ _ site => rfl

/-- The fiber part of the contract's `RegistryAgrees` (§3), at the reference machine. -/
def FiberRegistryAgrees (root : ProgramSource) (w : Typed.World) (m : RState) : Prop :=
  Proofs.Narrower w.Γ (fiberDeclOf (nativeSignature root.table) root.program m)

/-- The constructor-complete strong value the membership amendment (B3) needs, fiber part: the
same one recursion, read against the world's own fiber table. -/
def StrongValueFibers (w : Typed.World) (ty : Ty) (v : Val) : Prop :=
  ValueOk w ty v ∧ fits w.Γ w.state.externals.allocated v ty = true ∧ HandlesLive w v

namespace M6Wanted

/-- T1. Every typed state agrees with the derived registry on fibers. Depends on M6
(`TypedState` and its preservation), on typing source points at `envAt`'s environment, and on
the fork ledger's lookup facts (origins never change, fibers are never removed). -/
theorem typedState_fiberRegistry (root : ProgramSource) (rootTy : EffTy) (w : Typed.World)
    (m : RState) :
    ProofGraph.Obligation (TypedState root rootTy w m → FiberRegistryAgrees root w m) := ⟨⟩

end M6Wanted

/-- T2, proved from T1. What the registry admits is a strong value in the world, fiber part: the
`fits` step is `fits_narrower`, the shape is `ValueOk` itself. So once M6 supplies T1, the
typed guarantee's fiber clause needs nothing more from the boundary. -/
theorem admitted_value_strong (root : ProgramSource) (w : Typed.World) (m : RState) (ty : Ty)
    (v : Val) (hreg : FiberRegistryAgrees root w m)
    (hfits : fits (fiberDeclOf (nativeSignature root.table) root.program m)
      w.state.externals.allocated v ty = true)
    (hty : Val.hasTy v ty w.state.externals.allocated = true) (hlive : HandlesLive w v) :
    StrongValueFibers w ty v :=
  ⟨hty, Proofs.fits_narrower _ w.Γ _ hreg v ty hfits, hlive⟩

#print axioms fiberDeclOf_native
#print axioms admitted_value_strong

end Research.Pass.FiberSlice.Typed
