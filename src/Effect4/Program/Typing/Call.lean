module

public import Effect4.Program.Typing.Table

/-!
# Program.Typing.Call — the checked instance of a host call, at the call's address

Slice H9 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310), in the
module form of decisions row 200. The typed print (the plan's slice PRINT) reads it.

**The question.** The checker computes the type instance at a call (`checkRow`,
`Program/Typing/Rules.lean`) and answers the two instantiated columns as the node's type.
`focusAt` keeps that type at the call's address. `callAt` projects it, with the request's type
and the bindings that instantiate the columns (`rowBindings`). The typed print writes a call's
type arguments from those bindings. The laws are `callAt_rowTy` and `checkRow_rowBindings`
(`Laws/Program/Typing/Call.lean`).
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
  /-- the bindings that instantiate the two columns: the row's bindings at the request
  (`rowBindings`). The typed print writes the call's type arguments from them. -/
  bindings : Ty.Subst
deriving DecidableEq

/-- **The bindings of a row's use at a request type**: the request's match by bounds, then the
binder term's (`bindTerm`). The row check instantiates the row's columns with them
(`checkRow`). It answers wherever the match and the term bind, formed columns or not. Where the
row check answers, it answers that answer's bindings (`checkRow_rowBindings`,
`Laws/Program/Typing/Call.lean`). -/
def rowBindings (row : Row) (request : Ty) (use : Option TermUse := none) : Option Ty.Subst :=
  (Bounds.matchB [] row.request.normalize request.normalize).bind fun σ =>
    (bindTerm σ use).toOption

/-- **The checked instance of the call at an address.** The focus at the address is a `perform`:
its type holds the instantiated columns (`focusAt`), and the request's type is the term's type
in the focus's environment. The bindings are the row's at that type. `none` where the address
holds no `perform`, or where the checker refuses on the way or at the call. -/
def callAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) :
    Option (CallInstance Op) :=
  (focusAt s env0 p path).bind fun focus =>
    match focus.program with
    | .perform op request =>
      (termTy s focus.env request).bind fun requestTy =>
        (rowBindings (s.rowOf op) requestTy (s.termUse focus.env op)).map fun bindings =>
          ⟨op, requestTy, focus.ty.answer, focus.ty.error, bindings⟩
    | _ => none

end Effect4.Program
