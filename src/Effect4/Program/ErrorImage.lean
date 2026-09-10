import Effect4.Program.Eff
import Effect4.Machine.Stores

/-!
# Program.ErrorImage — the closed error image and parameterized cause folds

Rows DI-62 (lossless admitted failures), DI-26 (external failure admission), and DI-17
(cause/exit membership). `errOf` and `valOfErr` connect the closed error alphabet to native
values. `boom` has no typed payload and its inverse is `none`; only unchecked execution of
unsupported values reaches that collapse. The typing introductions consult `supportedErrTy`
in `Program/Eff.lean` before accepting an error term.

`reasonAdmits` and `causeAdmits` accept a membership predicate so `Program/Typed.lean` can
use the same fold both recursively and at external admission. The recursive caller closes
over the smaller type and its allocation table; this module has no dependency on `Val.hasTy`.
The conversion and membership laws live in `Laws/Program/{Typed,Admit}.lean`.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- The represented error image: natural, text, and the two-string package payload.
Every other raw value collapses to `boom`; the supported-error typing guards exclude those
values at each admitted failure introduction (DI-62). -/
def errOf : Val → Err
  | .nat n => .tag n
  | .str s => .text s
  | .list [.str t, .str m] => .tagged t m
  | _ => .boom

/-- The partial inverse of `errOf`. `boom` has no typed payload; no arm invents one. -/
def valOfErr : Err → Option Val
  | .boom => none
  | .tag n => some (.nat n)
  | .tagged tag message => some (.list [.str tag, .str message])
  | .text s => some (.str s)

/-- Does one reason of a cause stay inside the declared error type, at the supplied notion of
membership? A typed failure must have an image (`valOfErr`) that is a member of the type; a
`boom` has none and is refused at every type. A defect and an interruption are outside the
error type by construction (`causeTy`, `src/Effect4/Program/Typing.lean`: `die` and
`interrupt` leaves have error type `never`), so they are admitted whatever the type is —
`E = never` does not mean a computation cannot die or be interrupted. -/
def reasonAdmits (member : Val → Ty → Bool) (ty : Ty) :
    Reason Err Defect FiberId Ann → Bool
  | .fail e _ =>
    match valOfErr e with
    | some v => member v ty
    | none => false
  | .die _ _ | .interrupt _ _ => true

/-- A whole cause stays inside the declared error type when every reason does. `List.all` on
the reason list is the same shape the `.list` arm of `Val.hasTy` already uses, so the
`.causeOf` arm added at the cutover recurses structurally on the smaller type. -/
def causeAdmits (member : Val → Ty → Bool) (ty : Ty) (c : CauseV) : Bool :=
  c.reasons.all (reasonAdmits member ty)

end Effect4.Program
