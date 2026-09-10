import Effect4.Program.Native

/-! Executable value admission lives below Laws so the application API can use it.
The associated inversions and term-typing proofs stay in `Laws/Program/Typed.lean`. -/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- The handle spellings the internal kinds own, each defined once beside its type
(`NativeOp.refTy`, `NativeOp.deferredTy`, `Ty.scope`, `Ty.context`). The `hasTy` arms below
read the same names, so this list and those arms cannot drift apart. -/
def internalHandleTargets : List String :=
  [NativeOp.refTarget, NativeOp.deferredTarget, Ty.scopeTarget, Ty.contextTarget]

/-- An external allocation may not reuse an internal spelling: a byte-7 handle would
otherwise read as a Ref, Deferred, Scope or Context handle by its target alone. -/
def externalHandleTarget (target : String) : Bool :=
  !internalHandleTargets.contains target

/-- Which values inhabit which types of the native cut (plan §2.1, ENSURES 1), by the type.
The scalars against the carrier's own frames; a handle against the spelling of its kind byte
(`HandleKind`, `Machine/Value.lean`): `Val.cell` against `NativeOp.refTy`, `Val.promise`
against `NativeOp.deferredTy` (`Native.lean`), `Val.scopeHandle` against `Ty.scope`, and a
context — a value `Val.context?` reads back — against `Ty.context` (`Eff.lean`); the fiber
handle against `.fiberOf`, and a snapshot of fiber handles (`Val.snapshot?`) against a `.list`
of them; a reified exit against `.exitOf` — a failure's cause must read back and every typed
failure must inhabit its error column (DI-62); a reified cause against `.causeOf` by the same
error fold; the two-cell `list` `Val.tuple` builds (`Native.lean`)
against `.prod`; a `list` against `.list` when every member does; a union as the disjunction
of its members; a string against the carrier's `str` frame and an option against its `none`
and `some` frames (DB-15). An external handle at byte 7 must name its exact target
in the supplied allocation table; the default empty table admits none. Every other
pair is a refusal named in the module header. -/
def Val.hasTy (v : Val) (ty : Ty) (allocated : List String := []) : Bool :=
  match ty with
  | .unit => match v with | .unit => true | _ => false
  | .nat => match v with | .nat _ => true | _ => false
  | .bool => match v with | .bool _ => true | _ => false
  | .string => match v with | .str _ => true | _ => false
  | .option inner =>
    match v with
    | .none => true
    | .some x => Val.hasTy x inner allocated
    | _ => false
  | .handle target =>
    match v with
    | .handle kind index =>
      match HandleKind.ofByte? kind with
      | some .cell => target == NativeOp.refTarget
      | some .promise => target == NativeOp.deferredTarget
      | some .scope => target == Ty.scopeTarget
      | some .external => externalHandleTarget target && allocated[index]? == some target
      | _ => false
    | _ => target == Ty.contextTarget && (Val.context? v).isSome
  | .fiberOf _ _ => match v with | Value.fiber _ => true | _ => false
  | .exitOf a e =>
    match v with
    | Val.exitOk x => Val.hasTy x a allocated
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => causeAdmits (fun w _ => Val.hasTy w e allocated) e c
      | none => false
    | _ => false
  | .causeOf e =>
    match Val.cause? v with
    | some c => causeAdmits (fun w _ => Val.hasTy w e allocated) e c
    | none => false
  | .prod ta tb =>
    match v with
    | .list [x, y] => Val.hasTy x ta allocated && Val.hasTy y tb allocated
    | _ => false
  | .list ty =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ids.all (fun id => Val.hasTy (Val.fiber id) ty allocated)
      | none => false
    | .list values => values.all fun x => Val.hasTy x ty allocated
    | _ => false
  | .union l r => Val.hasTy v l allocated || Val.hasTy v r allocated
  | _ => false

/-- The typed error part of a completion; defects and interruptions stay outside `E`.
This is the shared reason fold at the default empty allocation table. -/
def errAdmits (ty : Ty) : Reason Err Defect FiberId Ann → Bool :=
  reasonAdmits (fun v t => Val.hasTy v t) ty

/-- Membership of a reified cause at the public, default-allocation interface. The recursive
`Val.hasTy` arms close over their own allocation table and use the same cause fold. -/
def hasTyCause (v : Val) (e : Ty) : Bool :=
  match Val.cause? v with
  | some c => causeAdmits (fun w t => Val.hasTy w t) e c
  | none => false

end Effect4.Program
