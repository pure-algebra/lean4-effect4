module

public import Effect4.Program.Typing.Table

/-!
# Program.Typing.Call — the checked instance of a host call, at the call's address

Slice H9 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310), in the
module form of decisions row 200. The typed print (the plan's slice PRINT) reads it.

**The question.** The checker computes the type instance at a call (`checkRow`,
`Program/Typing/Rules.lean`) and answers the two instantiated columns as the node's type.
`focusAt` keeps that type at the call's address. `callAt` projects it, with the request's type.
The law is `callAt_rowTy` (`Laws/Program/Typing/Call.lean`).
-/

set_option autoImplicit false

@[expose] public section

namespace Effect4.Program

variable {Op : Type}

/-- **The checked instance of a call**: the operation, the type of its request at the call, and
the row's answer and error columns at that request. -/
structure CallInstance (Op : Type) where
  /-- the operation that the call performs -/
  op : Op
  /-- the type of the request at the call -/
  request : Ty
  /-- the row's answer column, instantiated at the request and normalized -/
  answer : Ty
  /-- the row's error column, instantiated at the request and normalized -/
  error : Ty
deriving DecidableEq

/-- **The checked instance of the call at an address.** The focus at the address is a `perform`:
its type holds the instantiated columns (`focusAt`), and the request's type is the term's type
in the focus's environment. `none` where the address holds no `perform`, or where the checker
refuses on the way or at the call. -/
def callAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) :
    Option (CallInstance Op) :=
  (focusAt s env0 p path).bind fun focus =>
    match focus.program with
    | .perform op request =>
      (termTy s focus.env request).map fun requestTy =>
        ⟨op, requestTy, focus.ty.answer, focus.ty.error⟩
    | _ => none

/-- **Every call of a program with its checked instance**, in the order of the address table. -/
def calls (s : Signature Op) (env0 : TyEnv) (p : Eff Op) : List (List Nat × CallInstance Op) :=
  (Node.addresses (.eff p)).filterMap fun a => (callAt s env0 p a).map fun c => (a, c)

end Effect4.Program
