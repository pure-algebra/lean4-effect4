import Effect4.Laws.Program.Typed

/-!
# Typed contract — the value typing of the native cut, frozen

Plan: `docs/research/2026-09-05-slice-1-compile-ground.md` §2 (lane 1). Packet:
`Test/contracts/program-denotation.contract.md`, ENSURES 1–9. The module under contract is
`src/Effect4/Laws/Program/Typed.lean`.

Every obligation below is ascribed at its exact proposition and supplied by name with `@`, so
a declaration that keeps the frozen name but weakens the statement fails here
(`Test/Program/ProvisionContract.lean` is the model). The executable receipts are `#guard`s
over first-order values: `Val.hasTy` on one value of each inhabited type and one refusal per
uninhabited type, `evalTerm` on every atom with its typed arguments, `NativeOp.syncOpOf` on
every sync row's request shape, and the two register rows as pairs of guards. `Val.hasTy` is
well-founded, so its guards are evaluations, never `decide`; the one `#guard` that renders a
type (`Ty.render`) keeps the bytes inside the guard (`AGENTS.md`, trust).

Register rows (`Test/Counterexamples/REGISTER.md`):

* `E4-TYPED-CE-001` — a term that types always evaluates. Retired 2026-09-08 (DB-15, the host
  rows slice): strings are machine values on the native route, `.lit (.str "x")` evaluates to
  `Val.str "x"`, and `evalTerm_isSome` holds with no `noStr` premise. The ID is kept; the
  guards below pin the statement it used to refute.
* `E4-TYPED-CE-002` — `Val.nat` inhabits `.int` because both print as `number`. Refuted:
  `Val.hasTy (.nat 1) .int = false` while `Ty.render .nat = Ty.render .int`; `.int` is a
  refusal of the value typing (`TYPED-FB-INT`), the printer's identification is not the
  typing's.
-/

set_option autoImplicit false

namespace Test.Program.TypedContract

open Effect4
open Effect4.Machine
open Effect4.Program

/-! ## The frozen statements -/

section Statements

-- The ratified host-rows step 4 adds the allocation table. Pin the full signature
-- and keep the original two-argument call at its default empty table.
#check (@Effect4.Program.Val.hasTy : Val → Ty → List String → Bool)
#check ((fun v t => Effect4.Program.Val.hasTy v t) : Val → Ty → Bool)

#check (@Effect4.Program.Fits : List Val → TyEnv → Prop)

#check (@Effect4.Program.Fits.get? :
  ∀ {env : List Val} {tys : TyEnv}, Fits env tys →
    ∀ {i : Nat} {v : Val} {t : Ty}, env[i]? = some v → tys[i]? = some t → Val.hasTy v t = true)

#check (@Effect4.Program.Fits.length :
  ∀ {env : List Val} {tys : TyEnv}, Fits env tys → env.length = tys.length)

#check (@Effect4.Program.Fits.append :
  ∀ {env : List Val} {tys : TyEnv}, Fits env tys →
    ∀ {v : Val} {t : Ty}, Val.hasTy v t = true → Fits (env ++ [v]) (tys ++ [t]))

#check (@Effect4.Program.Val.hasTy_string_inv :
  ∀ {v : Val}, Val.hasTy v .string = true → ∃ s, v = Val.str s)

#check (@Effect4.Program.Val.hasTy_option_inv :
  ∀ {v : Val} {t : Ty}, Val.hasTy v (.option t) = true →
    v = Store.Val.none ∨ ∃ x, v = Store.Val.some x ∧ Val.hasTy x t = true)

#check (@Effect4.Program.Lit.toVal_hasTy :
  ∀ (l : Lit) (v : Val), l.toVal = some v → Val.hasTy v l.ty = true)

#check (@Effect4.Program.Lit.toVal_isSome : ∀ (l : Lit), l.toVal.isSome = true)

#check (@Effect4.Program.nativeAtom_typed :
  ∀ (atom : String) (tys : List Ty) (ty : Ty) (vs : List Val),
    nativeAtomTy atom tys = some ty → Fits vs tys →
      ∃ v, nativeAtom atom vs = some v ∧ Val.hasTy v ty = true)

#check (@Effect4.Program.evalTerm_hasTy :
  ∀ (t : Term) (env : List Val) (tys : TyEnv) (ty : Ty) (v : Val),
    Fits env tys → termTy nativeSignature tys t = some ty → evalTerm env t = some v →
      Val.hasTy v ty = true)

#check (@Effect4.Program.evalTerms_hasTy :
  ∀ (ts : Terms) (env : List Val) (tys : TyEnv) (tl : List Ty) (vs : List Val),
    Fits env tys → termsTy nativeSignature tys ts = some tl → evalTerms env ts = some vs →
      Fits vs tl)

#check (@Effect4.Program.evalTerm_isSome :
  ∀ (t : Term) (env : List Val) (tys : TyEnv) (ty : Ty),
    Fits env tys → termTy nativeSignature tys t = some ty → (evalTerm env t).isSome = true)

#check (@Effect4.Program.evalTerms_isSome :
  ∀ (ts : Terms) (env : List Val) (tys : TyEnv) (tl : List Ty),
    Fits env tys → termsTy nativeSignature tys ts = some tl → (evalTerms env ts).isSome = true)

#check (@Effect4.Program.syncOpOf_isSome :
  ∀ (op : NativeOp) (v : Val),
    Val.hasTy v (NativeOp.row op).request = true → (NativeOp.row op).kind = .sync →
      (NativeOp.syncOpOf op v).isSome = true)

#check (@Effect4.Program.syncOpOf_async_none :
  ∀ (op : NativeOp) (v : Val), (NativeOp.row op).kind = .async → NativeOp.syncOpOf op v = none)

end Statements

/-! ## `Val.hasTy` — one value of each inhabited type -/

section Inhabited

#guard Val.hasTy Val.unit .unit
#guard Val.hasTy (Val.nat 3) .nat
#guard Val.hasTy (Val.bool true) .bool
#guard Val.hasTy (Val.cell ⟨0⟩) NativeOp.refTy
#guard Val.hasTy (Val.promise ⟨0⟩) NativeOp.deferredTy
#guard Val.hasTy (Val.scopeHandle 0) Ty.scope
#guard Val.hasTy (Val.context emptyCtx) Ty.context
#guard Val.hasTy (Val.fiber ⟨1⟩) (.fiberOf .nat .never)
#guard Val.hasTy (Val.fibers [⟨1⟩, ⟨2⟩]) (.list (.fiberOf (.handle "unknown") (.handle "unknown")))
#guard Val.hasTy (Val.exitOk (Val.nat 1)) (.exitOf .nat .nat)
#guard Val.hasTy (Val.exitErr (Cause.fail (Err.tag 1))) (.exitOf .nat .nat)
-- a tagged package error's cause reads back through its image (`ctor 2 [str, str]`)
#guard Val.hasTy (Val.exitErr (Cause.fail (Err.tagged "SqlError" "boom"))) (.exitOf .nat (.prod .string .string))
#guard causeImage.ofVal (causeImage.toVal (Cause.fail (Err.tagged "SqlError" "boom"))) =
  some (Cause.fail (Err.tagged "SqlError" "boom"))
#guard Val.hasTy (Val.tuple [Val.nat 1, Val.bool true]) (.prod .nat .bool)
#guard Val.hasTy Val.exitNil (.list .nat)
#guard Val.hasTy (Val.list [Val.nat 1, Val.nat 2]) (.list .nat)
#guard Val.hasTy (Val.nat 1) (.union .nat .bool)
#guard Val.hasTy (Val.bool true) (.union .nat .bool)
-- DB-15: a string against the carrier's `str` frame; an option against `none` and `some`
#guard Val.hasTy (Val.str "x") .string
#guard Val.hasTy Store.Val.none (.option .nat)
#guard Val.hasTy (Store.Val.some (Val.nat 1)) (.option .nat)
#guard Val.hasTy (Store.Val.some (Store.Val.some (Val.str "s"))) (.option (.option .string))
#guard Val.hasTy (Val.list [Val.tuple [Val.str "a", Val.str "7"]]) (.list (.prod .string .string))

-- TYPED-FB-CAUSE: the cause of a reified failed exit is not checked
#guard Val.hasTy (Val.exitErr (Cause.fail Err.boom)) (.exitOf .nat .bool)

end Inhabited

/-! ## `Val.hasTy` — one refusal per uninhabited type, and the mismatches -/

section Refused

#guard Val.hasTy (Val.nat 1) .int = false
#guard Val.hasTy Val.unit .string = false
#guard Val.hasTy Val.unit (.option .unit) = false
#guard Val.hasTy (Val.exitOk Val.unit) (.except .nat .unit) = false
#guard Val.hasTy (Val.exitErr (Cause.fail (Err.tag 1))) (.causeOf .nat) = false
#guard Val.hasTy Val.unit .never = false
#guard Val.hasTy (Val.cell ⟨0⟩) (.handle "Ref.Ref<string>") = false
#guard Val.hasTy (Val.cell ⟨0⟩) NativeOp.deferredTy = false
#guard Val.hasTy (Val.exitOk (Val.nat 1)) (.exitOf .bool .nat) = false
#guard Val.hasTy (Val.tuple [Val.nat 1]) (.prod .nat .nat) = false
#guard Val.hasTy (Val.list [Val.nat 1, Val.bool true]) (.list .nat) = false
-- U1: the carrier's other frames and a malformed shape of a runtime one are refusals too
#guard Val.hasTy (Val.nat 1) .string = false
#guard Val.hasTy Store.Val.none .nat = false
#guard Val.hasTy (Store.Val.some (Val.bool true)) (.option .nat) = false
#guard Val.hasTy (Val.str "x") (.option .string) = false
#guard Val.hasTy (Store.Val.handle 9 0) NativeOp.refTy = false
#guard Val.hasTy (Value.memoMap 0) (.handle "Layer.MemoMap") = false
#guard Val.hasTy (Value.exitErr (Val.nat 1)) (.exitOf .nat .nat) = false
#guard Val.hasTy (Value.fiberSnapshot (Val.list [Val.nat 1])) (.list (.fiberOf .nat .never)) = false
#guard Val.hasTy (Value.fiberContext (Val.nat 1) (Val.nat 2) (Val.nat 3)) Ty.context = false
#guard Val.hasTy (Val.nat 1) (.union .bool .unit) = false

end Refused

/-! ## The register rows -/

section Rows

-- E4-TYPED-CE-001, retired (DB-15): a `str` literal types and evaluates to the `str` frame
#guard termTy nativeSignature [] (.lit (.str "x")) = some .string
#guard evalTerm [] (.lit (.str "x")) = some (Val.str "x")
#guard evalTerm [Val.str "a"] (.app "pair" (.cons (.var 0) (.cons (.lit (.str "b")) .nil)))
  = some (Val.tuple [Val.str "a", Val.str "b"])

-- E4-TYPED-CE-002: `Val.nat` does not inhabit `.int`, though both render as `number`
#guard Val.hasTy (Val.nat 1) .int = false
#guard Ty.render .nat = Ty.render .int
#guard Val.hasTy (Val.nat 1) .nat = true

end Rows

/-! ## The atoms with their typed arguments (`Native.lean:59-84`) -/

section Atoms

#guard termTy nativeSignature [] (.app "succ" (.cons (.lit (.nat 1)) .nil)) = some .nat
#guard evalTerm [] (.app "succ" (.cons (.lit (.nat 1)) .nil)) = some (Val.nat 2)
#guard termTy nativeSignature [] (.app "pred" (.cons (.lit (.nat 1)) .nil)) = some .nat
#guard evalTerm [] (.app "pred" (.cons (.lit (.nat 1)) .nil)) = some (Val.nat 0)
#guard termTy nativeSignature [] (.app "isZero" (.cons (.lit (.nat 0)) .nil)) = some .bool
#guard evalTerm [] (.app "isZero" (.cons (.lit (.nat 0)) .nil)) = some (Val.bool true)
#guard termTy nativeSignature [] (.app "not" (.cons (.lit (.bool true)) .nil)) = some .bool
#guard evalTerm [] (.app "not" (.cons (.lit (.bool true)) .nil)) = some (Val.bool false)
#guard termTy nativeSignature [.nat, .nat] (.app "add" (.cons (.var 0) (.cons (.var 1) .nil))) = some .nat
#guard evalTerm [Val.nat 2, Val.nat 3] (.app "add" (.cons (.var 0) (.cons (.var 1) .nil))) = some (Val.nat 5)
#guard termTy nativeSignature [.nat, .nat] (.app "lt" (.cons (.var 0) (.cons (.var 1) .nil))) = some .bool
#guard evalTerm [Val.nat 2, Val.nat 3] (.app "lt" (.cons (.var 0) (.cons (.var 1) .nil))) = some (Val.bool true)
#guard termTy nativeSignature [.nat, .nat] (.app "eq" (.cons (.var 0) (.cons (.var 1) .nil))) = some .bool
#guard evalTerm [Val.nat 2, Val.nat 3] (.app "eq" (.cons (.var 0) (.cons (.var 1) .nil))) = some (Val.bool false)
#guard termTy nativeSignature [.nat, .bool] (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))) = some (.prod .nat .bool)
#guard evalTerm [Val.nat 2, Val.bool true] (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))) = some (Val.tuple [Val.nat 2, Val.bool true])
#guard termTy nativeSignature [.prod .nat .bool] (.app "fst" (.cons (.var 0) .nil)) = some .nat
#guard evalTerm [Val.tuple [Val.nat 2, Val.bool true]] (.app "fst" (.cons (.var 0) .nil)) = some (Val.nat 2)
#guard termTy nativeSignature [.prod .nat .bool] (.app "snd" (.cons (.var 0) .nil)) = some .bool
#guard evalTerm [Val.tuple [Val.nat 2, Val.bool true]] (.app "snd" (.cons (.var 0) .nil)) = some (Val.bool true)
-- an ill-typed application is refused by the typing and by the evaluation
#guard termTy nativeSignature [] (.app "succ" (.cons (.lit (.bool true)) .nil)) = none
#guard evalTerm [] (.app "succ" (.cons (.lit (.bool true)) .nil)) = none

end Atoms

/-! ## `NativeOp.syncOpOf` on each sync row's request shape (`Native.lean:145-232`) -/

section Rows20

#guard Val.hasTy (Val.nat 0) (NativeOp.row .refMake).request
#guard NativeOp.syncOpOf .refMake (Val.nat 0) = some (SyncOp.refMake (Val.nat 0))
#guard Val.hasTy (Val.cell ⟨0⟩) (NativeOp.row .refGet).request
#guard NativeOp.syncOpOf .refGet (Val.cell ⟨0⟩) = some (SyncOp.refGet ⟨0⟩)
#guard Val.hasTy (Val.tuple [Val.cell ⟨0⟩, Val.nat 1]) (NativeOp.row .refSet).request
#guard NativeOp.syncOpOf .refSet (Val.tuple [Val.cell ⟨0⟩, Val.nat 1]) = some (SyncOp.refSet ⟨0⟩ (Val.nat 1))
#guard NativeOp.syncOpOf .refGetAndSet (Val.tuple [Val.cell ⟨0⟩, Val.nat 1]) = some (SyncOp.refGetAndSet ⟨0⟩ (Val.nat 1))
#guard NativeOp.syncOpOf .refSetAndGet (Val.tuple [Val.cell ⟨0⟩, Val.nat 1]) = some (SyncOp.refSetAndGet ⟨0⟩ (Val.nat 1))
#guard NativeOp.syncOpOf (.refUpdate .incr) (Val.cell ⟨0⟩) = some (SyncOp.refUpdate ⟨0⟩ .incr)
#guard NativeOp.syncOpOf (.refGetAndUpdate .incr) (Val.cell ⟨0⟩) = some (SyncOp.refGetAndUpdate ⟨0⟩ .incr)
#guard NativeOp.syncOpOf (.refUpdateAndGet .incr) (Val.cell ⟨0⟩) = some (SyncOp.refUpdateAndGet ⟨0⟩ .incr)
#guard NativeOp.syncOpOf (.refUpdateSome .zeroWhenPositive) (Val.cell ⟨0⟩) = some (SyncOp.refUpdateSome ⟨0⟩ .zeroWhenPositive)
#guard NativeOp.syncOpOf (.refGetAndUpdateSome .zeroWhenPositive) (Val.cell ⟨0⟩) = some (SyncOp.refGetAndUpdateSome ⟨0⟩ .zeroWhenPositive)
#guard NativeOp.syncOpOf (.refUpdateSomeAndGet .zeroWhenPositive) (Val.cell ⟨0⟩) = some (SyncOp.refUpdateSomeAndGet ⟨0⟩ .zeroWhenPositive)
#guard NativeOp.syncOpOf (.refModify .takeAndBump) (Val.cell ⟨0⟩) = some (SyncOp.refModify ⟨0⟩ .takeAndBump)
#guard NativeOp.syncOpOf (.refModifySome .noChange) (Val.cell ⟨0⟩) = some (SyncOp.refModifySome ⟨0⟩ .noChange)
#guard Val.hasTy Val.unit (NativeOp.row .deferredMake).request
#guard NativeOp.syncOpOf .deferredMake Val.unit = some SyncOp.deferredMake
#guard Val.hasTy (Val.promise ⟨0⟩) (NativeOp.row .deferredIsDone).request
#guard NativeOp.syncOpOf .deferredIsDone (Val.promise ⟨0⟩) = some (SyncOp.deferredIsDone ⟨0⟩)
#guard NativeOp.syncOpOf .deferredPoll (Val.promise ⟨0⟩) = some (SyncOp.deferredPoll ⟨0⟩)
#guard Val.hasTy (Val.tuple [Val.promise ⟨0⟩, Val.nat 7]) (NativeOp.row .deferredSucceed).request
#guard NativeOp.syncOpOf .deferredSucceed (Val.tuple [Val.promise ⟨0⟩, Val.nat 7]) =
  some (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 7))))
#guard NativeOp.syncOpOf .deferredFail (Val.tuple [Val.promise ⟨0⟩, Val.nat 7]) =
  some (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.failure (Cause.fail (Err.tag 7)))))
#guard Val.hasTy Val.unit (NativeOp.row (.scopeMake .sequential)).request
#guard NativeOp.syncOpOf (.scopeMake .sequential) Val.unit = some (SyncOp.scopeMake .sequential)
#guard NativeOp.syncOpOf (.scopeMake .parallel) Val.unit = some (SyncOp.scopeMake .parallel)
-- the async row decodes to nothing, and a wrong shape decodes to nothing
#guard (NativeOp.row .deferredAwait).kind = .async
#guard NativeOp.syncOpOf .deferredAwait (Val.promise ⟨0⟩) = none
#guard NativeOp.syncOpOf .refGet (Val.nat 0) = none
#guard Val.hasTy (Val.nat 0) (NativeOp.row .refGet).request = false
-- the timer (A4): the sleep row is async and decodes to no store operation; the clock read is a
-- value row on `unit` decoding to `clockNow`
#guard (NativeOp.row .sleep).kind = .async ∧ (NativeOp.row .sleep).shape = .call
#guard Val.hasTy (Val.nat 5) (NativeOp.row .sleep).request
#guard NativeOp.syncOpOf .sleep (Val.nat 5) = none
#guard (NativeOp.row .clockNow).kind = .sync ∧ (NativeOp.row .clockNow).shape = .value
#guard Val.hasTy Val.unit (NativeOp.row .clockNow).request
#guard NativeOp.syncOpOf .clockNow Val.unit = some SyncOp.clockNow
#guard NativeOp.syncOpOf .clockNow (Val.nat 0) = none

end Rows20

end Test.Program.TypedContract
