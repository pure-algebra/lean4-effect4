# Surface handler contract

Status: breaker packet, red, 2026-09-04 (wave 1b, for wave 2d of
`docs/research/2026-09-04-surface-library-plan.md` §13.2, under the rulings of
§13.7)

Implementation (owed): `Effect4/Surface/Handler.lean`

Battery: `Effect4Test/Surface/HandlerContract.lean`

Counterexamples: `E4-SURFACE-CE-076` through `E4-SURFACE-CE-087`

Witnesses: `Effect4Test/Counterexamples/Surface/Handler.lean`

Reads: `Effect4/Syntax/Typing.lean` (`Ty`, `EffTy`, `Signature`, `typeOf`,
`EffTy.joinAnswer`), `Effect4/Syntax/Eff.lean` (`Eff`, `Row`, `Ty.join`,
`Ty.key`), `Effect4/Syntax/Print.lean` (`print`, `PrintRefusal`, `printDecl`)

Shared: `test/contracts/surface-facts.contract.md` owns the `Refusal`
alphabet; this contract adds six constructors and owns their clause order.

Pins: rc.112 `unstable/httpapi/HttpApiBuilder.ts:126` (`group`), `:441`
(`endpoint`), `:620` (`Handlers.handle`)

## Purpose

This is the sentence the operator asked for, made checkable: **the same `Eff`
the AST relation lane prints and compiles is the handler language of the
surface, its `EffTy` is decided by `typeOf`, and the surface rows say what
that type must be.**

An endpoint's rows already determine the type rc.112 will demand of its
handler, `Effect<Success, Error, Requires>`, and the estate already owns a
data carrier for exactly that shape. `Endpoint.effTy` computes it from the
rows; `Handler.fits` asks `typeOf` whether a given program has it. A handler
whose program does not have the endpoint's type is refused before any bytes
exist, which is the typed-hole discipline of plan §13.2.

The three functions are not conveniences. Each is the *only* place a
particular class of defect can be caught: `answerTy` is where "this endpoint
returns something the type language cannot name" surfaces, `errorTy` is where
a declared error the handler never produces surfaces, and the requirement row
is where a handler reaching a service the endpoint did not declare surfaces.
Deleting any one of them moves that defect to the host, or past it.

## Frozen public declarations

All in namespace `Effect4.Surface`, over
`open Effect4.Syntax (Ty EffTy Signature Eff typeOf)` and
`Effect4.Deep.Env.Requirement`.

```lean
def Endpoint.answerTy {refs} (e : Endpoint refs) : Except Refusal Ty
def Endpoint.errorTy  {refs} (e : Endpoint refs) : Except Refusal Ty

def Endpoint.requirement {refs}
    (services : List (String × Effect4.ServiceKey)) (e : Endpoint refs) :
    Except Refusal Requirement

def Endpoint.effTy {refs}
    (services : List (String × Effect4.ServiceKey)) (e : Endpoint refs) :
    Except Refusal EffTy

structure Handler (refs : List Effect4.ReferenceEntry) (Op : Type) where
  endpoint : String
  sig      : Signature Op
  body     : Eff Op

def Handler.fits {refs} {Op : Type}
    (services : List (String × Effect4.ServiceKey))
    (e : Endpoint refs) (h : Handler refs Op) : Bool :=
  match Endpoint.effTy services e with
  | .error _ => false
  | .ok ty   => Effect4.Syntax.typeOf h.sig h.body = some ty

def Handler.Fits {refs} {Op : Type} (services) (e) (h) : Prop :=
  Handler.fits services e h = true

def Handler.stubBody {refs} (e : Endpoint refs) : TypeScript.Expr

def handlersModule {refs} {Op : Type}
    (services : List (String × Effect4.ServiceKey))
    (a : Api refs) (handlers : List (Handler refs Op)) :
    Except Refusal TypeScript.Module
```

New `Refusal` constructors (appended; appending is not a breaking change per
`surface-facts.contract.md`):

```lean
  | responseNotAnEntity (endpoint : String) (status : Nat)
  | serviceKeyUnknown (endpoint service : String)
  | handlerUnknownEndpoint (endpoint : String)
  | handlerDuplicate (api endpoint : String)
  | handlerTypeMismatch (endpoint : String)
  | handlerNotPrintable (endpoint refusal : String)
```

`handlerNotPrintable`'s second field is the *constructor name* of
`Effect4.Syntax.PrintRefusal` (`"choose"` or `"internalAction"`), not a
rendered message, per plan §14.2's rule that a refusal carries names and never
prose.

`handlersModule` is monomorphic in `Op`: one perform alphabet per API module.
A heterogeneous handler list would need a `Σ Op : Type, Handler refs Op`,
which lifts the carrier out of `Type 0` and out of this slice's
representation rules. See finding 1 below.

## Observations

1. `Endpoint.answerTy e`, `Endpoint.errorTy e`, `Endpoint.effTy services e`,
   each `Except Refusal _`, compared against an exact `.ok` value or an exact
   `.error` value. Never `isOk`.
2. `Handler.fits services e h : Bool`, on a fixture alphabet of four rows,
   one row per attack.
3. `handlersModule services a handlers : Except Refusal TypeScript.Module`,
   compared against its exact refusal on the negative rows and observed as
   `.isOk` on the positive ones; the emitted bytes are the harness's business.
4. `Ty.join` on two entity handles, compared against the exact `Ty` value
   including member order.

## Acceptance conditions

### `answerTy`

Clause order, first refusal wins:

| # | case | result |
| --- | --- | --- |
| 1 | `e.success = []` | `.error (.successEmpty e.id)` |
| 2 | one success, `ResponseBody.void` | `.ok Ty.unit` |
| 3 | one success, `ResponseBody.json s` with `s.rep = Schema.reference name` | `.ok (Ty.handle name)` |
| 4 | one success, any other body | `.error (.responseNotAnEntity e.id status)` |
| 5 | several successes | the `Ty.join` of each success's own answer, left to right, with clause 4 applying to each |

Clause 4 covers **every** success body that is neither `void` nor a
`reference`: an inline `struct`, a bare `string`, an `array`, and a
`ResponseBody.stream`. A stream has no `Ty` in v1 (there is no `Stream`
constructor in `Effect4.Syntax.Ty`), so it is refused here rather than
approximated by its chunk type (`E4-SURFACE-CE-083`).

**The union is admitted, not refused** (`E4-SURFACE-CE-080`). rc.112 types a
multi-success handler's answer as the union of the success bodies, so refusing
it here would make the model narrower than the host and would make the plan's
own §12.2 open question unaskable. Two consequences are pinned rather than
left implicit:

- `Ty.join` is canonical by `Ty.key`, which orders a `handle` by the UTF-8
  bytes of its target. The union's member order is therefore **not** the
  endpoint's success declaration order: `join (handle "User") (handle
  "Address")` is `Ty.union (handle "Address") (handle "User")`, whichever
  order the successes were written in.
- `Handler.fits` is exact equality of `EffTy`, so a handler for a two-success
  endpoint must have that union as its answer, not one member of it. A body
  answering only `handle "User"` does not fit.

### `errorTy`

`.ok Ty.never` when `e.errors = []`. Otherwise the `Ty.join` of each error
body's answer under the same clauses 2 to 4 as `answerTy`, with clause 4's
refusal carrying that error's status. A `void` error body contributes
`Ty.unit`.

`Ty.never` is the empty union by construction (`Ty.members .never = []`), so
`errorTy` of an endpoint with no errors is the same value `EffTy.pure`
produces, and no special case is needed anywhere downstream.

### `requirement` and `effTy`

`Endpoint.requirement services e` looks every name of `e.requires` up in
`services` and answers `Requirement.ofList` of the keys found. A name absent
from the table is `.error (.serviceKeyUnknown e.id name)` and **never** an
empty requirement or a silently dropped row (`E4-SURFACE-CE-085`): a dropped
requirement makes `fits` accept a handler that reaches a service the
deployment need not provide, which is exactly the join
`surface-deploy.contract.md` relies on.

`effTy services e = do let a ← answerTy e; let r ← errorTy e; let q ←
requirement services e; pure ⟨a, r, q⟩`, in that clause order.

### `fits`

`Handler.fits` is `false` whenever `effTy` refuses. It is **not**
`typeOf h.sig h.body = (Endpoint.effTy services e).toOption`: that spelling
makes an untypeable body fit an endpoint with no computable type, because both
sides are `none`. This is the one vacuity in the packet and it has its own row
(`E4-SURFACE-CE-084`).

`fits` compares the whole `EffTy`, so all three components are load-bearing:
the answer (`E4-SURFACE-CE-076`), the error (`E4-SURFACE-CE-077`) and the
requirement row (`E4-SURFACE-CE-078`).

### `handlersModule`

Spelling, pinned:

```
HttpApiBuilder.group(<Api>, "<group>", (handlers) =>
  handlers.handle("<id>", (request) => <printed body>))
```

one `group` call per group of `a`, one `handle` per endpoint of that group, in
declaration order. Clause order, first refusal wins:

| # | clause | refusal | id |
| --- | --- | --- | --- |
| 1 | every handler names an endpoint of `a` | `handlerUnknownEndpoint h.endpoint` | `E4-SURFACE-CE-081` |
| 2 | no two handlers name one endpoint | `handlerDuplicate a.id id` | `E4-SURFACE-CE-087` |
| 3 | every handler fits its endpoint | `handlerTypeMismatch e.id` | `E4-SURFACE-CE-082` |
| 4 | every fitting handler's body prints | `handlerNotPrintable e.id refusal` | `E4-SURFACE-CE-079` |

An endpoint with **no** handler is not a refusal: it emits a typed stub whose
body is `Effect.fail(new NotImplemented())` under the declared type, so the
module typechecks either way (`E4-SURFACE-CE-086`).

Clause 4 is the sharp one. `Effect4.Syntax.print` refuses `choose` and the
five internal fiber actions by name, and a printer refusal on a handler that
*fits* must surface as a `Refusal`, never degrade into the stub. Degrading
would emit a module that typechecks and silently does not implement the
endpoint the user wrote a body for, which is the worst outcome available: the
stub is indistinguishable from an unimplemented endpoint, so the loss is not
visible anywhere downstream.

The requirement row is not spelled in the emitted type.
`Effect4.Syntax.printDecl` declares `Effect.Effect<A, E>` only when the
requirement is empty and leaves the type to inference otherwise; a handler
with a requirement therefore emits an untyped constant, and this contract
claims nothing about the third type parameter. See finding 3.

## Assurance allocation

Graph edge `SURFACE-PG-HANDLER`, obligations:

| obligation | evidence at landing |
| --- | --- |
| identity | `answerTy`/`errorTy`/`effTy` pinned against exact `Ty` and `EffTy` values on the fixtures, including the union's member order |
| admission | `Handler.fits` true on the fitting handler, false on each of the four mutants, and false whenever `effTy` refuses |
| bridges | the `requires`/`ServiceKey` join to `surface-deploy.contract.md`, and the `Signature`/`typeOf` join to `Effect4/Syntax/Typing.lean` |
| targets | `handlersModule` refusals; the emitted bytes and their typecheck are the harness's, and the rule stays `RuleStance.emitted` |
| counterexamples | `E4-SURFACE-CE-076` through `E4-SURFACE-CE-087` |

The emitter is a new census row for `surface-emit.contract.md`,
`apiHandlers` / `surface.api.handlers`, landing `RuleStance.emitted` with
`Rule.refuses` naming `body.choose` and `body.internalAction`. It is **not**
added to `Rule.all` by this packet: the eleven ids are frozen in
`surface-emit.contract.md` and a twelfth is a coordination item, recorded as
finding 2.

## What this contract does not claim

No run agreement: nothing here claims an emitted handler answers what the
endpoint says, only that its program has the endpoint's type in
`Effect4.Syntax`'s type assignment. `typeOf` is a structural, total type
assignment and not a soundness result; the progress and host-type receipts
belong to the AST relation lane's A2 and A3, and this packet inherits whatever
they establish and adds nothing.

No claim about the middleware, the request decoding, the response encoding, or
the `Context`/`Layer` values a deployment must provide: the requirement row is
a set of `ServiceKey`s, and turning it into a `Layer` is `surface-deploy`'s
`provides` and a later wave's work.

No claim that a fitting handler is the *right* handler. `fits` is a type
check, not a specification: two handlers with the same `EffTy` are
interchangeable to it, and one of them may be wrong.

No claim about the third type parameter of the emitted constant (finding 3),
and no claim about handler options (`uninterruptible`), which
`HttpApiBuilder.ts:620` accepts and this carrier does not model.
