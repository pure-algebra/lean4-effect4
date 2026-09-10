import Effect4.Program.Eff
import Effect4.Machine.Stores

/-!
# Program.ErrorImage — the error image between the value carrier and the error alphabet

Rows: DI-62 (the admissible error image at every introduction), DI-26 (the failure branch of
an external answer), DI-17 (`FitsIn` and the cause/exit arms of `Val.hasTy`).
Plan: `docs/research/2026-09-09-foundation-settlement-v2.md` §2 DI-62, "Module layout".

This module owns two things and nothing else:

* `valOfErr : Err → Option Val` — the partial inverse of `errOf`
  (`src/Effect4/Program/Compile.lean`, the `Val → Err` direction). It is partial on purpose:
  `errOf` collapses every unrecognised shape to `Err.boom`, and a collapse has no inverse.
  `errOf` itself moves here at the S2 cutover, beside its inverse; today it stays where its
  clients are and the two round-trip laws are stated in `src/Effect4/Laws/Program/Admit.lean`.
* `reasonAdmits` and `causeAdmits` — the admission folds of a cause, **parameterised by a
  membership function** `member : Val → Ty → Bool` rather than fixed at `Val.hasTy`.

## Why the folds are parameterised

`Val.hasTy` (`src/Effect4/Program/Typed.lean`) is above this module: the import chain is
`Eff → Typing → Native → Typed → Compile`, `Err` enters at `Machine/Stores.lean` and is
reachable from `Native` on. The two consumers of the folds sit on opposite sides of that
chain — `errAdmits` (`Compile.lean`) reads `Val.hasTy`, and the `.causeOf` / `.exitOf` arms of
`Val.hasTy` itself must read the same fold — so a fold that named `Val.hasTy` directly would
be an import cycle. Parameterising by membership breaks it: this module sits below `Native`,
`Typed.lean` instantiates `member := fun v t => Val.hasTy v t allocated` and exports the
result under the existing `Effect4.Program` names, and no client changes.

The allocation table is closed over by the instantiating caller rather than threaded as a
third argument of `member`: `Val → Ty → Bool` is the shape both call sites want (`errAdmits`
uses the default empty table; the `Val.hasTy` arms pass their own `allocated`), and a
`Val → Ty → List String → Bool` parameter would force every caller to re-thread a table it
has already fixed. This is a refinement of v2 DI-62's wording, recorded in
`docs/research/2026-09-09-seat-error-laws.md`.

## What this module refuses

* `Err.value (v : Val)` — a constructor carrying an arbitrary value is refused (v2's
  what-not-to-do list). The error alphabet stays a closed, first-order, append-only image;
  `valOfErr` is total *into* `Option` because of it.
* `supportedErrTy : Ty → Bool` does **not** live here. It is a predicate on `Ty` alone with
  no `Val` in it, so it belongs beside `Ty` in `src/Effect4/Program/Eff.lean`, where the three
  typing introductions (`Typing.lean`, `fail`, `yieldError`, each `CauseTerm.fail` leaf) can
  read it without importing the carrier. It lands there at the S2 cutover.
* No arm of `valOfErr` invents a payload. `Err.boom` is *no* typed payload, and it maps to
  `none`, never to a placeholder value; that is what makes `errAdmits` refuse a `boom` at
  every error type including `never`.

## What the S2 cutover adds here

One arm, and only one: `Err.text s ↦ some (.str s)` in `valOfErr`, the day `Err.text`
(`ctor 3 [str s]`) is appended in `src/Effect4/Machine/Stores.lean`. `reasonAdmits` gains no
arm — it already matches `.fail e _` for every `e` — so a text error is admitted at `.string`
exactly when `member (.str s) ty` holds. The recipe is §6 of
`docs/research/2026-09-09-seat-error-laws.md`.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- The error alphabet read back as a value: the partial inverse of `errOf`
(`src/Effect4/Program/Compile.lean`). `tag n` is the number it was built from and
`tagged t m` the two-cell `prod string string` of DB-15; `boom` carries no typed payload and
has no image, so it is `none` — not a placeholder value.

At the S2 cutover this gains `| .text s => some (.str s)` (DI-62). -/
def valOfErr : Err → Option Val
  | .boom => none
  | .tag n => some (.nat n)
  | .tagged tag message => some (.list [.str tag, .str message])

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
