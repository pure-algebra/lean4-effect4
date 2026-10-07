import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.Admit

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

Added 2026-09-09 (rows DI-17, DI-26, DI-62), changing no existing statement. The obligations are `Extends`, `hasTy_mono`, `hasTy_append`, `Fits_iff_FitsIn_nil`,
`FitsIn.append`, `FitsIn.mono` (`src/Effect4/Laws/Program/Typed.lean`) and `errOf_valOfErr`,
`valOfErr_errOf`, `errAdmits_eq_reasonAdmits`, `hasTyCause_exitErr`, `external_error_typed`,
`external_oracle_error_typed`, `fits_childWith` (`src/Effect4/Laws/Program/Admit.lean`).
The new executable claims are:

* allocation — a handle is typed only in a table naming its target at its own index; a
  different target, a different index and the empty table all refuse; appending to the table
  keeps every existing membership (`hasTy_mono`'s content, seen).
* `Fits` versus `FitsIn` — one external handle is refused by `Fits` (whose table is the
  default `[]`) and admitted by `FitsIn` at the table that minted it. This is the pair the
  generalisation exists for.
* the error image — `valOfErr` inverts natural, text and package-pair errors. Every admitted
  failure introduction has an exact image; unsupported values are refused (DI-62).
* `hasTyCause` — a tagged package error is admitted at `prod string string` and refused at
  `nat`; a `boom` is refused at every type; a defect and an interruption are admitted at
  `never`, because `E = never` bounds the typed failures only.

The cause and failed-exit guards exercise the S2 membership cutover. Fiber membership still
reads neither of its columns; those shape-only controls remain fixed.
-/

set_option autoImplicit false

namespace Test.Program.TypedContract

open Effect4
open Effect4.Machine
open Effect4.Program

/-! ## `Val.hasTy` — one value of each inhabited type -/

section Inhabited

#guard Val.hasTy Val.unit .unit
#guard Val.hasTy (Val.nat 3) .nat
#guard Val.hasTy (Val.bool true) .bool
#guard Val.hasTy (Val.cell ⟨0⟩) (.refOf .nat)
#guard Val.hasTy (Val.promise ⟨0⟩) (.deferredOf .nat .nat)
-- a cell or a promise fits its handle type at any argument (the state plan's T3a): what it holds
-- is the world's tables' to type
#guard Val.hasTy (Val.cell ⟨0⟩) (.refOf (.record [("n", false, .string)]))
#guard Val.hasTy (Val.promise ⟨0⟩) (.deferredOf .unit .never)
-- red: the retired spellings have no member (`Val.hasTy_handle_retired`)
#guard !Val.hasTy (Val.cell ⟨0⟩) (.handle "Ref.Ref<number>")
#guard !Val.hasTy (Val.promise ⟨0⟩) (.handle "Deferred.Deferred<number, number>")
#guard !inhabited (.handle "Ref.Ref<number>")
#guard !inhabited (.app "Deferred.Deferred<number, number>" [])
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

-- DI-62: a payloadless boom does not inhabit the declared error column.
#guard Val.hasTy (Val.exitErr (Cause.fail Err.boom)) (.exitOf .nat .bool) = false

-- Result keeps Except's stored shape; the developer alias follows Effect's A, E order.
#guard Ty.result .string .nat = Ty.except .nat .string
#guard (Ty.result .string .nat).render = "Result.Result<string, number>"
#guard Val.hasTy (.ctor 0 [.nat 7]) (Ty.result .string .nat)
#guard Val.hasTy (.ctor 1 [.str "ok"]) (Ty.result .string .nat)
#guard !Val.hasTy (.ctor 0 [.str "wrong"]) (Ty.result .string .nat)
#guard !Val.hasTy (.ctor 1 [.nat 7]) (Ty.result .string .nat)
#guard !Val.hasTy (.ctor 2 [.nat 7]) (Ty.result .string .nat)
#guard !Val.hasTy (.ctor 1 []) (Ty.result .string .nat)
#guard !Val.hasTy (.ctor 1 [.str "ok", .str "extra"]) (Ty.result .string .nat)
#guard !Val.hasTy (.ctor 0 [.nat 0]) (Ty.result .string .never)
#guard Val.hasTy (.some (.ctor 1 [.str "ok"])) (.option (Ty.result .string .nat))
#guard Val.hasTy (.ctor 1 [Value.external 0]) (Ty.result (.handle "Result.Resource") .nat) ["Result.Resource"]
#guard !Val.hasTy (.ctor 1 [Value.external 0]) (Ty.result (.handle "Result.Resource") .nat)

end Inhabited

/-! ## `Val.hasTy` — one refusal per uninhabited type, and the mismatches -/

section Refused

#guard Val.hasTy (Val.str "1") .int = false
#guard Val.hasTy Val.unit .string = false
#guard Val.hasTy Val.unit (.option .unit) = false
#guard Val.hasTy (Val.exitOk Val.unit) (.except .nat .unit) = false
#guard Val.hasTy (Val.exitErr (Cause.fail (Err.tag 1))) (.causeOf .bool) = false
#guard Val.hasTy Val.unit .never = false
#guard Val.hasTy (Val.cell ⟨0⟩) (.handle "Ref.Ref<string>") = false
#guard Val.hasTy (Val.cell ⟨0⟩) (.deferredOf .nat .nat) = false
#guard Val.hasTy (Val.exitOk (Val.nat 1)) (.exitOf .bool .nat) = false
#guard Val.hasTy (Val.tuple [Val.nat 1]) (.prod .nat .nat) = false
#guard Val.hasTy (Val.list [Val.nat 1, Val.bool true]) (.list .nat) = false
-- U1: the carrier's other frames and a malformed shape of a runtime one are refusals too
#guard Val.hasTy (Val.nat 1) .string = false
#guard Val.hasTy Store.Val.none .nat = false
#guard Val.hasTy (Store.Val.some (Val.bool true)) (.option .nat) = false
#guard Val.hasTy (Val.str "x") (.option .string) = false
#guard Val.hasTy (Store.Val.handle 9 0) (.refOf .nat) = false
#guard Val.hasTy (Value.exitErr (Val.nat 1)) (.exitOf .nat .nat) = false
#guard Val.hasTy (Value.fiberSnapshot (Val.list [Val.nat 1])) (.list (.fiberOf .nat .never)) = false
#guard Val.hasTy (Value.fiberContext (Val.nat 1) (Val.nat 2) (Val.nat 3)) Ty.context = false
-- a memo map's handle has its own type since decisions row 187 (refused before it); at another
-- handle type it is refused
#guard Val.hasTy (Value.memoMap 0) (.handle "Layer.MemoMap") = true
#guard Val.hasTy (Value.memoMap 0) (.handle "Scope.Scope") = false
#guard Val.hasTy (Val.nat 1) (.union .bool .unit) = false

end Refused

/-! ## Allocation: a handle is typed only in a table naming its target (DI-17) -/

section Allocation

-- byte 7 is the external kind; the target spelling is read at the handle's own index
#guard Val.hasTy (Store.Val.handle 7 0) (.handle "Host.Resource") ["Host.Resource"]
#guard !(Val.hasTy (Store.Val.handle 7 0) (.handle "Host.Resource") ["Other.Resource"])
#guard !(Val.hasTy (Store.Val.handle 7 1) (.handle "Host.Resource") ["Host.Resource"])
#guard !(Val.hasTy (Store.Val.handle 7 0) (.handle "Host.Resource"))
#guard Val.hasTy (Store.Val.some (Val.list [Store.Val.handle 7 0]))
  (.option (.list (.handle "Host.Resource"))) ["Host.Resource", "Other"]
-- a registration appends, and an append keeps every existing membership (`hasTy_append`)
#guard Val.hasTy (Store.Val.handle 7 0) (.handle "Host.Resource")
  (["Host.Resource"] ++ ["Other.Resource"])
-- a target spelling says which kind of resource a handle names, never whether it is still
-- open or which run minted it: both of these are the same membership
#guard Val.hasTy (Store.Val.handle 7 0) (.handle "Host.Resource") ["Host.Resource"] =
  Val.hasTy (Store.Val.handle 7 0) (.handle "Host.Resource") ["Host.Resource", "Other"]

-- the pair `FitsIn` exists for: the default empty table refuses a live external handle
#guard !(Val.hasTy (Value.external 0) (.handle NativeOp.sqlTarget))
#guard Val.hasTy (Value.external 0) (.handle NativeOp.sqlTarget) [NativeOp.sqlTarget]

end Allocation

/-! ## The error image and the cause fold (DI-62, DI-26) -/

section ErrorImage

-- `valOfErr` inverts `errOf` off `boom`
#guard valOfErr Err.boom = none
#guard valOfErr (Err.tag 7) = some (Val.nat 7)
#guard valOfErr (Err.tagged "SqlError" "m") = some (Val.list [Val.str "SqlError", Val.str "m"])
#guard errOf (Val.nat 7) = Err.tag 7
#guard errOf (Val.list [Val.str "SqlError", Val.str "m"]) = Err.tagged "SqlError" "m"
-- DI-62: text has an exact image, including the text "boom".
#guard errOf (Val.str "lost") = Err.text "lost"
#guard valOfErr (Err.text "boom") = some (.str "boom")
#guard errOf (Val.str "boom") ≠ Err.boom
#guard errOf (Val.bool true) = Err.boom

-- the bridge, read on each reason shape: `errAdmits` is the fold at `Val.hasTy`
#guard errAdmits .nat (Reason.fail (Err.tag 7) ReasonAnnotations.empty) =
  reasonAdmits (fun v t => Val.hasTy v t) .nat (Reason.fail (Err.tag 7) ReasonAnnotations.empty)
#guard errAdmits .nat (Reason.fail Err.boom ReasonAnnotations.empty) =
  reasonAdmits (fun v t => Val.hasTy v t) .nat (Reason.fail Err.boom ReasonAnnotations.empty)
#guard errAdmits .never (Reason.die Defect.badName ReasonAnnotations.empty) =
  reasonAdmits (fun v t => Val.hasTy v t) .never (Reason.die Defect.badName ReasonAnnotations.empty)

-- `hasTyCause` on a reified failed exit
#guard hasTyCause (Val.exitErr (Cause.fail (Err.tagged "A" "m"))) (.prod .string .string)
#guard !(hasTyCause (Val.exitErr (Cause.fail (Err.tagged "A" "m"))) .nat)
#guard hasTyCause (Val.exitErr (Cause.fail (Err.tag 7))) .nat
#guard !(hasTyCause (Val.exitErr (Cause.fail Err.boom)) .nat)
-- `E = never` bounds the typed failures only: a defect and an interruption stay admitted
#guard hasTyCause (Val.exitErr (Cause.die Defect.badName)) .never
#guard hasTyCause (Val.exitErr (Cause.interrupt none)) .never
-- a value that is not a reified failed exit has no cause to read
#guard !(hasTyCause (Val.nat 1) .nat)
#guard !(hasTyCause (Val.exitOk (Val.nat 1)) .nat)

-- DI-62: all three error introductions consult the same supported type language.
#guard supportedErrTy .never
#guard supportedErrTy .nat
#guard supportedErrTy .string
#guard supportedErrTy (.prod .string .string)
#guard supportedErrTy (.union .nat (.union .string (.prod .string .string)))
#guard !(supportedErrTy .bool)
#guard !(supportedErrTy (.union .nat .bool))
#guard !(supportedErrTy (.prod .string .nat))
#guard !(supportedErrTy (.handle "Db"))
#guard (effTy nativeSignature [] (.fail (.lit (.str "lost")))).isSome
#guard (effTy nativeSignature [] (.failCause (.fail (.lit (.str "lost"))))).isSome
#guard effTy nativeSignature [] (.fail (.lit (.bool true))) = none
#guard effTy nativeSignature [] (.failCause (.fail (.lit (.bool true)))) = none
-- DI-74: a `die` carries an admitted error value, the same domain as `fail`
#guard effTy nativeSignature [] (.failCause (.die (.lit (.str "hi")))) = some ⟨.never, .never, .empty⟩
#guard effTy nativeSignature [] (.failCause (.die (.lit (.nat 3)))) = some ⟨.never, .never, .empty⟩
#guard effTy nativeSignature [] (.failCause (.die (.lit (.bool true)))) = none
#guard effTy nativeSignature [Ty.scope] (.failCause (.die (.var 0))) = none
#guard effTy nativeSignature [Ty.scope] (.fail (.var 0)) = none
#guard effTy nativeSignature []
  (.failCause (.both (.fail (.lit (.nat 1))) (.fail (.lit (.bool true))))) = none
#guard (effTy nativeSignature [.union .nat .string] (.fail (.var 0))).isSome
#guard effTy nativeSignature [.union .nat .bool] (.fail (.var 0)) = none

-- Exact error/defect images, including malformed shape refusals and old ordinal pins.
#guard Err.image.toVal .boom = .ctor 0 []
#guard Err.image.toVal (.tag 4) = .ctor 1 [.nat 4]
#guard Err.image.toVal (.tagged "A" "m") = .ctor 2 [.str "A", .str "m"]
#guard Err.image.toVal (.text "m") = .ctor 3 [.str "m"]
#guard ofErr (.ctor 3 [.nat 1]) = none
#guard ofErr (.ctor 3 []) = none
#guard ofErr (.ctor 3 [.str "a", .str "b"]) = none
#guard Defect.image.toVal (.user 4) = .ctor 4 [.nat 4]
#guard Defect.image.toVal (.error (.text "m")) = .ctor 5 [.ctor 3 [.str "m"]]
#guard ofDefect (.ctor 5 [.ctor 3 [.nat 1]]) = none
#guard ofDefect (.ctor 5 []) = none
#guard ofDefect (.ctor 5 [.ctor 99 []]) = none
#guard ofDefect (.ctor 5 [.ctor 0 [], .ctor 0 []]) = none
#guard ([Err.boom, .tag 3, .tagged "A" "m", .text "s"]).all (fun e =>
  Defect.image.ofVal (Defect.image.toVal (.error e)) == some (.error e))

-- Decisions row 120: an error payload is a handle-free record frame, written `ctor 4 [frame]` and
-- read back exactly. A frame holding a handle, a frame repeating a name and a non-frame are not
-- payloads, and their images are refused.
def notFoundFrame : Val :=
  (Effect4.Machine.Record.build ["_tag", "id"] [.str "NotFound", .nat 9]).getD .unit
def handleFrame : Val := .ctor 0 [.list [.str "_tag"], .list [Val.cell ⟨0⟩]]
#guard isPayload notFoundFrame
#guard !isPayload handleFrame
#guard !isPayload (.ctor 0 [.list [.str "a", .str "a"], .list [.nat 1, .nat 2]])
#guard !isPayload (.nat 3)
#guard (Payload.image.ofVal notFoundFrame).map (fun p => Err.image.toVal (.payload p)) =
  some (.ctor 4 [notFoundFrame])
#guard ((Payload.image.ofVal notFoundFrame).map Err.payload).all fun e =>
  ofErr (Err.image.toVal e) == some e &&
    Defect.image.ofVal (Defect.image.toVal (.error e)) == some (.error e)
#guard ofErr (.ctor 4 [.nat 3]) = none
#guard ofErr (.ctor 4 [handleFrame]) = none
#guard ofErr (.ctor 4 []) = none
-- `errOf` reads the frame and `valOfErr` gives it back; a frame with a handle stays `boom`.
#guard valOfErr (errOf notFoundFrame) = some notFoundFrame
#guard errOf handleFrame = .boom
-- The admitted record error types: a required literal `_tag` (ruling (b)), payload-admissible
-- fields (ruling (a)), and no other spelling (ruling (c)).
def notFoundTy : Ty := .record [("_tag", false, .lit "NotFound"), ("id", false, .nat)]
#guard supportedErrTy notFoundTy
#guard Val.hasTy notFoundFrame notFoundTy
#guard Val.hasTy (Val.exitErr (Cause.fail (errOf notFoundFrame))) (.causeOf notFoundTy)
#guard Val.hasTy (Val.exitErr (Cause.fail (errOf notFoundFrame))) (.exitOf .nat notFoundTy)
#guard !(Val.hasTy (Val.exitErr (Cause.fail (errOf notFoundFrame))) (.causeOf .string))
#guard !supportedErrTy (.record [("id", false, .nat)])
#guard !supportedErrTy (.record [("_tag", false, .string), ("id", false, .nat)])
#guard !supportedErrTy (.record [("_tag", true, .lit "E"), ("id", false, .nat)])
#guard !supportedErrTy (.record [("_tag", false, .lit "E"), ("cause", false, .unknown)])
#guard !supportedErrTy (.record [("_tag", false, .lit "E"), ("n", false, .int)])
#guard !supportedErrTy (.record [("_tag", false, .lit "E"), ("ref", false, .refOf .nat)])
#guard !supportedErrTy (.record [("_tag", false, .lit "E"), ("at", false, .option (.handle "Db"))])
#guard !supportedErrTy (.record [("_tag", false, .lit "E"), ("message", false, .string)])
#guard !supportedErrTy (.record [("_tag", false, .lit "E")])
#guard supportedErrTy (.record [("_tag", false, .lit "E"), ("message", false, .string), ("id", false, .nat)])
#guard supportedErrTy (.record [("_tag", false, .lit "E"), ("at", false, .record [("x", false, .nat)])])
#guard supportedErrTy (.record [("_tag", false, .lit "E"), ("ids", false, .list .nat), ("why", true, .string)])
#guard supportedErrTy (.union notFoundTy (.prod (.lit "Other") .string))
-- The atom `tagIs` reads a record's `_tag` beside a pair's tag; a record with another tag, or
-- none, misses.
#guard NativeAtom.eval .tagIs [.str "NotFound", notFoundFrame] = some (.bool true)
#guard NativeAtom.eval .tagIs [.str "Other", notFoundFrame] = some (.bool false)
#guard NativeAtom.eval .tagIs [.str "NotFound", .list [.str "NotFound", .str "m"]] = some (.bool true)
#guard NativeAtom.eval .tagIs [.str "x",
  (Effect4.Machine.Record.build ["id"] [.nat 1]).getD .unit] = some (.bool false)
-- A promoted payload keeps its record (`Defect.ofError`, DI-31).
#guard ((Payload.image.ofVal notFoundFrame).map fun p =>
  Defect.ofError (.payload p) == .error (.payload p)) = some true

-- Cause and failed-exit E checks reject a single bad reason in a mixed cause.
#guard Val.hasTy (Val.exitErr (Cause.fail (.tag 1))) (.causeOf .nat)
#guard Val.hasTy (Val.exitErr (Cause.fail (.text "lost"))) (.causeOf .string)
#guard Val.hasTy (Val.exitErr (Cause.fail (.text "lost"))) (.exitOf .nat .string)
#guard !(Val.hasTy (Val.exitErr (Cause.fail (.text "lost"))) (.causeOf .nat))
#guard !(Val.hasTy (Val.exitErr (Cause.fail (.tagged "A" "m"))) (.exitOf .nat .string))
#guard !(Val.hasTy (Val.exitErr (Cause.combine (Cause.fail (.tag 1)) (Cause.fail (.text "s")))) (.causeOf .nat))
#guard Val.hasTy (Val.exitErr (Cause.combine (Cause.fail (.tag 1)) (Cause.fail (.text "s")))) (.causeOf (.union .nat .string))
#guard Val.hasTy (Val.exitErr (Cause.combine (Cause.die (.error (.text "s"))) (Cause.interrupt none))) (.causeOf .never)
#guard !(Val.hasTy (Val.exitErr (Cause.combine (Cause.fail (.tag 1)) (Cause.fail .boom))) (.causeOf .nat))
#guard !(Val.hasTy (Value.exitErr (.ctor 99 [])) (.causeOf .nat))
#guard !(Val.hasTy (Value.exitErr (.ctor 99 [])) (.exitOf .nat .nat))
#guard !(Val.hasTy (Val.exitOk (.nat 1)) (.causeOf .nat))

-- Wrappers agree with the allocation-aware branch; unrelated allocation changes do not
-- alter closed error values, while successful exits still consult their resource column.
#guard Val.hasTy (Val.exitErr (Cause.fail (.text "s"))) (.causeOf .string) ["Db"] =
  causeAdmits (fun v t => Val.hasTy v t ["Db"]) .string (Cause.fail (.text "s"))
#guard Val.hasTy (Val.exitOk (Value.external 0)) (.exitOf (.handle "Db") .string) ["Db"]
#guard Val.hasTy (Val.exitOk (Value.external 0)) (.exitOf (.handle "Db") .string) ["Db", "Other"]
#guard !(Val.hasTy (Val.exitOk (Value.external 0)) (.exitOf (.handle "Db") .string) [])

end ErrorImage

/-! ## The register rows -/

section Rows

-- E4-TYPED-CE-001, retired (DB-15): a `str` literal types and evaluates to the `str` frame
#guard termTy nativeSignature [] (.lit (.str "x")) = some .string
#guard evalTerm [] (.lit (.str "x")) = some (Val.str "x")
#guard evalTerm [Val.str "a"] (.app "pair" (.cons (.var 0) (.cons (.lit (.str "b")) .nil)))
  = some (Val.tuple [Val.str "a", Val.str "b"])

-- E4-TYPED-CE-002, retired 2026-10-02 (decisions row 121, the nesting images): `.int`'s image is
-- `nat`'s and the signed frame, so `Val.nat` inhabits `.int` by that inclusion, not because both
-- render as `number`; the signed frame is no `nat`
#guard Val.hasTy (Val.nat 1) .int = true
#guard Val.hasTy (.negInt 0) .int = true
#guard Val.hasTy (.negInt 0) .nat = false
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

/-! ### The literal rule and subsumption (part 4, 2026-09-12; DI-15, DI-55)

A string literal is `string` in general position and `lit` as an argument of `pair`
(`litArgTy`, `Signature.constAtom`); a fixed-signature atom accepts an argument at a subtype
of its parameter (`NativeAtom.typeOf`). The pins the packet asks for: `pair x y` with `x` a
`string` variable stays `prod string string`; `eq (fst (pair "A" m)) "A"` is `bool`;
`fail (pair "A" m)` puts `prod (lit "A") string` in the error column and `supportedErrTy`
accepts it — as it accepts the literal message `pair("SqlError", "boom")`, which the
const-generic prelude `pair` types at `readonly ["SqlError", "boom"]`. -/

-- general position: `string`; `pair`'s argument: `lit`
#guard termTy nativeSignature [] (.lit (.str "A")) = some .string
#guard termTy nativeSignature [.string]
  (.app "pair" (.cons (.lit (.str "A")) (.cons (.var 0) .nil))) = some (.prod (.lit "A") .string)
#guard termTy nativeSignature []
  (.app "pair" (.cons (.lit (.str "A")) (.cons (.lit (.str "m")) .nil)))
  = some (.prod (.lit "A") (.lit "m"))
-- a `string` variable stays `string`
#guard termTy nativeSignature [.string, .string]
  (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))) = some (.prod .string .string)
-- every other atom sees a literal at `string`; `eq` takes two strings, so two literals
#guard termTy nativeSignature []
  (.app "eq" (.cons (.lit (.str "a")) (.cons (.lit (.str "b")) .nil))) = some .bool
-- subsumption at a fixed-signature atom: `eq (fst (pair "A" m)) "A"`
#guard termTy nativeSignature [.string]
  (.app "eq" (.cons
    (.app "fst" (.cons (.app "pair" (.cons (.lit (.str "A")) (.cons (.var 0) .nil))) .nil))
    (.cons (.lit (.str "A")) .nil))) = some .bool
-- `never` is a subtype of every parameter; a literal is not a `nat`
#guard termTy nativeSignature [.never] (.app "succ" (.cons (.var 0) .nil)) = some .nat
#guard termTy nativeSignature [.lit "x"] (.app "succ" (.cons (.var 0) .nil)) = none
-- the literal rule evaluates, and the value inhabits the literal type
#guard evalTerm [Val.str "m"] (.app "pair" (.cons (.lit (.str "A")) (.cons (.var 0) .nil)))
  = some (Val.tuple [Val.str "A", Val.str "m"])
#guard Val.hasTy (Val.tuple [Val.str "A", Val.str "m"]) (.prod (.lit "A") .string)
-- `fail (pair "A" m)`: the error column and its support
#guard typeOf nativeSignature
  (.bind (.succeed (.lit (.str "m")))
    (.fail (.app "pair" (.cons (.lit (.str "A")) (.cons (.var 0) .nil)))))
  = some ⟨.never, .prod (.lit "A") .string, .empty⟩
#guard supportedErrTy (.prod (.lit "A") .string)
#guard supportedErrTy (.prod (.lit "A") (.lit "boom"))
#guard !(supportedErrTy (.prod (.lit "A") .nat))
#guard typeOf nativeSignature
  (.fail (.app "pair" (.cons (.lit (.str "SqlError")) (.cons (.lit (.str "boom")) .nil))))
  = some ⟨.never, .prod (.lit "SqlError") (.lit "boom"), .empty⟩
-- the tag test (part 4 commit 3): typed `bool` at a string tag, evaluated by `tagHit`
#guard termTy nativeSignature [.union (.prod (.lit "A") .string) .string]
  (.app "tagIs" (.cons (.lit (.str "A")) (.cons (.var 0) .nil))) = some .bool
#guard evalTerm [Val.tuple [Val.str "A", Val.str "m"]]
  (.app "tagIs" (.cons (.lit (.str "A")) (.cons (.var 0) .nil))) = some (Val.bool true)
#guard evalTerm [Val.str "A"]
  (.app "tagIs" (.cons (.lit (.str "A")) (.cons (.var 0) .nil))) = some (Val.bool false)

/-! ### Eager option elimination (DI-78)

These controls use the ordinary term evaluator and its environment. An option's selected
payload keeps its shape and allocation identity; a default must inhabit the payload type.
The malformed-default control distinguishes eager application from a lazy callback. -/

private def optionDefault : Term := .app "getOrElse" (.cons (.var 0) (.cons (.var 1) .nil))

#guard termTy nativeSignature [.option .nat] (.app "isSome" (.cons (.var 0) .nil)) = some .bool
#guard evalTerm [Store.Val.none] (.app "isSome" (.cons (.var 0) .nil)) = some (.bool false)
#guard evalTerm [Store.Val.some (.nat 3)] (.app "isSome" (.cons (.var 0) .nil)) = some (.bool true)
#guard termTy nativeSignature [.option .nat, .nat] optionDefault = some .nat
#guard evalTerm [Store.Val.none, .nat 9] optionDefault = some (.nat 9)
#guard evalTerm [Store.Val.some (.nat 3), .nat 9] optionDefault = some (.nat 3)
#guard termTy nativeSignature [.option .string, .lit "fallback"] optionDefault = some .string
#guard evalTerm [Store.Val.none, .str "fallback"] optionDefault = some (.str "fallback")
#guard termTy nativeSignature [.option .nat, .string] optionDefault = some (.union .nat .string)
#guard termTy nativeSignature [.option .never, .nat] optionDefault = some .nat
#guard termTy nativeSignature [.nat, .string] optionDefault = none

-- Nested options are retained as values, including an inner None selected from Some.
#guard termTy nativeSignature [.option (.option .nat), .option .nat] optionDefault =
  some (.option .nat)
#guard evalTerm [Store.Val.some Store.Val.none, Store.Val.some (.nat 9)] optionDefault =
  some Store.Val.none
#guard evalTerm [Store.Val.none, Store.Val.some (.nat 9)] optionDefault =
  some (Store.Val.some (.nat 9))

-- Extraction retains an existing external handle; membership still needs its allocation.
#guard termTy nativeSignature [.option (.handle "Host.Resource"), .handle "Host.Resource"]
  optionDefault = some (.handle "Host.Resource")
#guard evalTerm [Store.Val.some (Value.external 0), Value.external 1] optionDefault =
  some (Value.external 0)
#guard evalTerm [Store.Val.none, Value.external 1] optionDefault = some (Value.external 1)
#guard match evalTerm [Store.Val.some (Value.external 0), Value.external 1] optionDefault with
  | some value => Val.hasTy value (.handle "Host.Resource") ["Host.Resource", "Host.Resource"]
  | none => false
#guard match evalTerm [Store.Val.some (Value.external 0), Value.external 1] optionDefault with
  | some value => !Val.hasTy value (.handle "Host.Resource") []
  | none => false

-- Even a present value cannot hide a malformed fallback application.
#guard evalTerm [Store.Val.some (.nat 3)]
  (.app "getOrElse" (.cons (.var 0)
    (.cons (.app "succ" (.cons (.lit (.bool true)) .nil)) .nil))) = none
#guard termTy nativeSignature [.option .nat]
  (.app "getOrElse" (.cons (.var 0)
    (.cons (.app "succ" (.cons (.lit (.bool true)) .nil)) .nil))) = none

end Atoms

/-! ## `NativeOp.syncOpOf` on each sync row's request shape (`NativeOp.row`, `NativeOp.syncOpOf`)

The `Ref` and `Deferred` rows are templates (the state plan's T3a): a value fits a row's request at
an instance, and a bare template admits no value (a parameter has no member, decisions row 155). -/

section Rows20

/-- The instance at `nat`, the one today's battery programs use. -/
def atNat (t : Ty) : Ty := t.instantiate [(0, .nat), (1, .nat)]

#guard Val.hasTy (Val.nat 0) (atNat (NativeOp.row .refMake).request)
#guard !Val.hasTy (Val.nat 0) (NativeOp.row .refMake).request
#guard NativeOp.syncOpOf .refMake [] (Val.nat 0) = some (SyncOp.refMake (Val.nat 0))
-- `Ref.make` decodes any initial value: the instance never decides the decoding
#guard NativeOp.syncOpOf .refMake [] (Val.str "x") = some (SyncOp.refMake (Val.str "x"))
#guard Val.hasTy (Val.cell ⟨0⟩) (atNat (NativeOp.row .refGet).request)
#guard NativeOp.syncOpOf .refGet [] (Val.cell ⟨0⟩) = some (SyncOp.refGet ⟨0⟩)
#guard Val.hasTy (Val.tuple [Val.cell ⟨0⟩, Val.nat 1]) (atNat (NativeOp.row .refSet).request)
#guard Val.hasTy (Val.tuple [Val.cell ⟨0⟩, Val.str "a"])
  ((NativeOp.row .refSet).request.instantiate [(0, .string)])
#guard NativeOp.syncOpOf .refSet [] (Val.tuple [Val.cell ⟨0⟩, Val.nat 1]) = some (SyncOp.refSet ⟨0⟩ (Val.nat 1))
#guard NativeOp.syncOpOf .refGetAndSet [] (Val.tuple [Val.cell ⟨0⟩, Val.nat 1]) = some (SyncOp.refGetAndSet ⟨0⟩ (Val.nat 1))
#guard NativeOp.syncOpOf .refSetAndGet [] (Val.tuple [Val.cell ⟨0⟩, Val.nat 1]) = some (SyncOp.refSetAndGet ⟨0⟩ (Val.nat 1))
-- a read-modify-write row hands the store its own binder term and the point's environment
-- (decisions row 43; the state plan's T3b), whatever the term and the environment are
#guard [NativeOp.refUpdateWith, .refGetAndUpdateWith, .refUpdateAndGetWith, .refUpdateSomeWith,
    .refGetAndUpdateSomeWith, .refUpdateSomeAndGetWith, .refModifyWith, .refModifySomeWith].zip
    [SyncOp.refUpdate, .refGetAndUpdate, .refUpdateAndGet, .refUpdateSome, .refGetAndUpdateSome,
     .refUpdateSomeAndGet, .refModify, .refModifySome] |>.all fun (row, store) =>
  [([] : List Val), [Val.nat 7, Val.str "x"]].all fun env =>
    [Term.var 0, .app "add" (.cons (.var 2) (.cons (.var 0) .nil))].all fun f =>
      NativeOp.syncOpOf (row f) env (Val.cell ⟨0⟩) == some (store ⟨0⟩ f env)
-- the request is a cell: any other value decodes to nothing, as at the rows without a term
#guard NativeOp.syncOpOf (.refUpdateWith (.var 0)) [] (Val.nat 0) = none
#guard Val.hasTy (Val.cell ⟨0⟩) (atNat (NativeOp.row (.refModifyWith (.var 0))).request)
#guard Val.hasTy Val.unit (NativeOp.row (.deferredMakeOf .nat .nat)).request
#guard NativeOp.syncOpOf (.deferredMakeOf .nat .nat) [] Val.unit = some SyncOp.deferredMake
#guard Val.hasTy (Val.promise ⟨0⟩) (atNat (NativeOp.row .deferredIsDone).request)
#guard NativeOp.syncOpOf .deferredIsDone [] (Val.promise ⟨0⟩) = some (SyncOp.deferredIsDone ⟨0⟩)
#guard NativeOp.syncOpOf .deferredPoll [] (Val.promise ⟨0⟩) = some (SyncOp.deferredPoll ⟨0⟩)
#guard Val.hasTy (Val.tuple [Val.promise ⟨0⟩, Val.nat 7]) (atNat (NativeOp.row .deferredSucceed).request)
#guard NativeOp.syncOpOf .deferredSucceed [] (Val.tuple [Val.promise ⟨0⟩, Val.nat 7]) =
  some (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.success (Val.nat 7))))
#guard NativeOp.syncOpOf .deferredFail [] (Val.tuple [Val.promise ⟨0⟩, Val.nat 7]) =
  some (SyncOp.deferredCompleteWith ⟨0⟩ (Completion.ofExit (Exit.failure (Cause.fail (Err.tag 7)))))
#guard Val.hasTy Val.unit (NativeOp.row (.scopeMake .sequential)).request
#guard NativeOp.syncOpOf (.scopeMake .sequential) [] Val.unit = some (SyncOp.scopeMake .sequential)
#guard NativeOp.syncOpOf (.scopeMake .parallel) [] Val.unit = some (SyncOp.scopeMake .parallel)
-- the async row decodes to nothing, and a wrong shape decodes to nothing
#guard (NativeOp.row .deferredAwait).kind = .async
#guard NativeOp.syncOpOf .deferredAwait [] (Val.promise ⟨0⟩) = none
#guard NativeOp.syncOpOf .refGet [] (Val.nat 0) = none
#guard Val.hasTy (Val.nat 0) (atNat (NativeOp.row .refGet).request) = false
-- the timer (A4): the sleep row is async and decodes to no store operation; the clock read is a
-- value row on `unit` decoding to `clockNow`
#guard (NativeOp.row .sleep).kind = .async ∧ (NativeOp.row .sleep).shape = .call
#guard Val.hasTy (Val.nat 5) (NativeOp.row .sleep).request
#guard NativeOp.syncOpOf .sleep [] (Val.nat 5) = none
#guard (NativeOp.row .clockNow).kind = .sync ∧ (NativeOp.row .clockNow).shape = .value
#guard Val.hasTy Val.unit (NativeOp.row .clockNow).request
#guard NativeOp.syncOpOf .clockNow [] Val.unit = some SyncOp.clockNow
#guard NativeOp.syncOpOf .clockNow [] (Val.nat 0) = none

end Rows20

/-! ## The eight term rows: the checker types the binder term (the state plan's T3b)

A read-modify-write row carries a binder term (decisions row 43). The checker matches the
request against `Ref<A>`, types the term at the node's environment extended by `A`
(`Signature.termUse`), and matches the term's type against the shape's result template
(`bindTerm`, `Typing/Rules.lean`). A node here sits under one binder that holds the cell, so the
node's level is 1 and the term reads the cell's value at `var 1`. Finite checks of named
programs; the theorems are `syncRow_typed` and `termMaps_of_typed`
(`Laws/Program/Typed/Denotation.lean`). -/

section TermRows

/-- The cell's current value at a node of level 1. -/
def cur : Term := .var 1

def app1 (f : String) (x : Term) : Term := .app f (.cons x .nil)
def app2 (f : String) (x y : Term) : Term := .app f (.cons x (.cons y .nil))
def none' : Term := .app "none" .nil

/-- One term row on the cell at `var 0`, checked with a cell of `element` in scope. -/
def rowCheck (element : Ty) (op : NativeOp) : Except TypeRefusal EffTy :=
  Checker.check nativeSignature [.refOf element] [] (.perform op (.var 0))

/-- The type the row answers on a cell of numbers. -/
def answers (op : NativeOp) : Option Ty := (rowCheck .nat op).toOption.map (·.answer)

-- the checker types each of the eight rows at a term: the three that answer nothing answer
-- `void`, the four that answer the cell's value answer its type, and `modify` answers `B`
#guard answers (.refUpdateWith (app1 "succ" cur)) = some .unit
#guard answers (.refGetAndUpdateWith (app1 "succ" cur)) = some .nat
#guard answers (.refUpdateAndGetWith (app2 "mul" cur (.lit (.nat 2)))) = some .nat
#guard answers (.refUpdateSomeWith (app1 "some" (app1 "succ" cur))) = some .unit
#guard answers (.refGetAndUpdateSomeWith none') = some .nat
#guard answers (.refUpdateSomeAndGetWith
  (.app "ite" (.cons (app2 "lt" (.lit (.nat 0)) cur) (.cons (app1 "some" (.lit (.nat 0)))
    (.cons none' .nil))))) = some .nat
-- `modify` answers `B`, bound from the term's type: here a boolean, on a cell of numbers
#guard answers (.refModifyWith (app2 "pair" (app1 "isZero" cur) (app1 "succ" cur))) = some .bool
#guard answers (.refModifySomeWith (app2 "pair" (.lit (.str "s")) none')) = some (.lit "s")
-- every row types no error and needs nothing
#guard (rowCheck .nat (.refModifyWith (app2 "pair" cur cur))).toOption =
  some ⟨.nat, .never, .empty⟩

-- every name's image types at its row, at levels 1 to 4 (the corpus draws exactly these)
#guard (List.range 4).all fun k => NativeOp.termRows.all fun row => fnNames.all fun g =>
  (Checker.check nativeSignature (List.replicate (k + 1) (.refOf .nat)) []
    (.perform (row.1 (FnName.image row.2 (k + 1) g)) (.var 0))).toOption.isSome

-- the term is typed at the cell's element type, not at `number`
#guard (rowCheck .string (.refUpdateWith (app2 "concat" cur (.lit (.str "!"))))).toOption.isSome
#guard Checker.refusal (rowCheck .string (.refUpdateWith (app1 "succ" cur))) =
  some ⟨[], .binderTerm "refUpdateWith" .string⟩
#guard (rowCheck (.prod .nat .string) (.refGetAndUpdateWith
  (app2 "pair" (app1 "succ" (app1 "fst" cur)) (app1 "snd" cur)))).toOption.map (·.answer) =
  some (.prod .nat .string)

-- a term with no type at the parameter is refused as a term, named by its row
#guard Checker.refusal (rowCheck .nat (.refUpdateWith (app1 "succ" (.lit (.bool true))))) =
  some ⟨[], .binderTerm "refUpdateWith" .nat⟩
-- so is a variable past the current value: the environment ends at the cell's value
#guard Checker.refusal (rowCheck .nat (.refUpdateWith (.var 2))) =
  some ⟨[], .binderTerm "refUpdateWith" .nat⟩
-- a term of the wrong result type is refused with the type it has and the one the row asks for
#guard Checker.refusal (rowCheck .nat (.refUpdateWith (.lit (.str "x")))) =
  some ⟨[], .resultNotSubtype "refUpdateWith" .string .nat⟩
#guard Checker.refusal (rowCheck .nat (.refUpdateSomeWith (app1 "succ" cur))) =
  some ⟨[], .resultNotSubtype "refUpdateSomeWith" .nat (.option .nat)⟩
#guard Checker.refusal (rowCheck .nat (.refModifyWith (app1 "succ" cur))) =
  some ⟨[], .resultNotSubtype "refModifyWith" .nat (.prod .never .nat)⟩
-- the request is checked first: a term row on a number is the request's refusal
#guard (Checker.refusal (Checker.check nativeSignature [.nat] []
    (.perform (.refUpdateWith (.lit (.str "x"))) (.var 0)))).map (·.reason.head) =
  some "requestNotSubtype"

/-- An outer capture: a number bound around the node, between the cell and the node. The node
sits at level 2: the cell's value is `var 2` and the outer number `var 1`. -/
def captureEnv : TyEnv := [.refOf .nat, .nat]

#guard (Checker.check nativeSignature captureEnv []
  (.perform (.refUpdateWith (app2 "add" (.var 2) (.var 1))) (.var 0))).toOption =
  some ⟨.unit, .never, .empty⟩
-- the capture is typed at its own type: a captured string is no number
#guard Checker.refusal (Checker.check nativeSignature [.refOf .nat, .string] []
    (.perform (.refUpdateWith (app2 "add" (.var 2) (.var 1))) (.var 0))) =
  some ⟨[], .binderTerm "refUpdateWith" .nat⟩

/-! ### `B`'s binding and the interim guard (decisions rows 213, 299 and 303)

`Ref.modify`'s `B` occurs covariantly, in the term's result template `[B, A]`. The match by
bounds joins the lower bounds that the term's type offers `B`. At a binder term it stands under
the interim guard (`Bounds.matchTerm`): those lower bounds must have a greatest one. A term whose
type is a union of two pairs offers `"a"` and `"b"`, which have no order, so the guard refuses the
term, although `B := "a" | "b"` puts the term's type under the instance. The same function
written as a pair has the raw product type, offers one lower bound, and binds the union. The
guard goes when the TypeScript printer writes a row's type arguments at the join. -/

/-- `["a", number] | ["b", number]`: the type of an outer value that is one of two pairs. -/
def pairUnion : Ty := .union (.prod (.lit "a") .nat) (.prod (.lit "b") .nat)

/-- The cell, then the outer pair; the node sits at level 2. -/
def unionEnv : TyEnv := [.refOf .nat, pairUnion]

-- red: the term is the outer variable. Its type offers `B` two lower bounds with no order, and
-- the interim guard refuses
#guard Checker.refusal (Checker.check nativeSignature unionEnv []
    (.perform (.refModifyWith (.var 1)) (.var 0))) =
  some ⟨[], .resultNotSubtype "refModifyWith" pairUnion (.prod .never .nat)⟩
-- yet the binding exists: at `B := "a" | "b"` the term's type is under the instance, and the
-- match by bounds alone answers it
#guard Ty.sub pairUnion.normalize
  ((Ty.prod (.var 1) (.var 0)).instantiate [(0, .nat), (1, .union (.lit "a") (.lit "b"))]).normalize
#guard (Bounds.matchB [(0, .nat)] (.prod (.var 1) (.var 0)) pairUnion).map
    (fun σ => (Ty.instantiate σ (.var 1)).normalize) = some (.union (.lit "a") (.lit "b"))
-- the same function as a pair of the two components has the raw product type and binds the union
#guard (Checker.check nativeSignature [.refOf .nat, .union (.lit "a") (.lit "b")] []
    (.perform (.refModifyWith (app2 "pair" (.var 1) (.var 2))) (.var 0))).toOption.map (·.answer) =
  some (.union (.lit "a") (.lit "b"))

end TermRows

end Test.Program.TypedContract
