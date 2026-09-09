import Effect4.Program.Native

/-! Executable value admission lives below Laws so the application API can use it.
The associated inversions and term-typing proofs stay in `Laws/Program/Typed.lean`. -/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- Which values inhabit which types of the native cut (plan §2.1, ENSURES 1), by the type.
The scalars against the carrier's own frames; a handle against the spelling of its kind byte
(`HandleKind`, `Machine/Value.lean`): `Val.cell` against `NativeOp.refTy`, `Val.promise`
against `NativeOp.deferredTy` (`Native.lean`), `Val.scopeHandle` against `Ty.scope`, and a
context — a value `Val.context?` reads back — against `Ty.context` (`Eff.lean`); the fiber
handle against `.fiberOf`, and a snapshot of fiber handles (`Val.snapshot?`) against a `.list`
of them; a reified exit against `.exitOf` — a failure's cause must read back, its error column
is not checked (`TYPED-FB-CAUSE`); the two-cell `list` `Val.tuple` builds (`Native.lean`)
against `.prod`; a `list` against `.list` when every member does; a union as the disjunction
of its members; a string against the carrier's `str` frame and an option against its `none`
and `some` frames (DB-15). Every other pair is a refusal named in the module header. -/
def Val.hasTy (v : Val) : Ty → Bool
  | .unit => match v with | .unit => true | _ => false
  | .nat => match v with | .nat _ => true | _ => false
  | .bool => match v with | .bool _ => true | _ => false
  | .string => match v with | .str _ => true | _ => false
  | .option inner =>
    match v with
    | .none => true
    | .some x => Val.hasTy x inner
    | _ => false
  | .handle target =>
    match v with
    | .handle kind _ =>
      match HandleKind.ofByte? kind with
      | some .cell => target == "Ref.Ref<number>"
      | some .promise => target == "Deferred.Deferred<number, number>"
      | some .scope => target == "Scope.Scope"
      | _ => false
    | _ => target == "Context.Context<unknown>" && (Val.context? v).isSome
  | .fiberOf _ _ => match v with | Value.fiber _ => true | _ => false
  | .exitOf a _ =>
    match v with
    | Val.exitOk x => Val.hasTy x a
    | Value.exitErr written => (causeImage.ofVal written).isSome
    | _ => false
  | .prod ta tb =>
    match v with
    | .list [x, y] => Val.hasTy x ta && Val.hasTy y tb
    | _ => false
  | .list ty =>
    match v with
    | Value.fiberSnapshot _ =>
      match ty with
      | .fiberOf _ _ => (Val.snapshot? v).isSome
      | _ => false
    | .list values => values.all fun x => Val.hasTy x ty
    | _ => false
  | .union l r => Val.hasTy v l || Val.hasTy v r
  | _ => false

end Effect4.Program
