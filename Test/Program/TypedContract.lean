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

#guard Val.hasTy (Val.nat 1) .int = false
#guard Val.hasTy Val.unit .string = false
#guard Val.hasTy Val.unit (.option .unit) = false
#guard Val.hasTy (Val.exitOk Val.unit) (.except .nat .unit) = false
#guard Val.hasTy (Val.exitErr (Cause.fail (Err.tag 1))) (.causeOf .bool) = false
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
#guard (effTy nativeSignature [] (.yieldError (.lit (.str "lost")))).isSome
#guard (effTy nativeSignature [] (.failCause (.fail (.lit (.str "lost"))))).isSome
#guard effTy nativeSignature [] (.fail (.lit (.bool true))) = none
#guard effTy nativeSignature [] (.yieldError (.lit (.bool true))) = none
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
