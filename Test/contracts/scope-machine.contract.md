# Scope-close request/response machine

This packet freezes an independently stepping interpreter of the existing
sequential `Scope.closeExitsM` fold. The separate builder owns
`Effect4/Runtime/ScopeMachine.lean`. A close retains its original exit, writes
the closed scope before exposing a callback request, captures every actual
response, and can pause between requests without completing or losing work.

The source policy is `effect@4.0.0-rc.112`, upstream commit
`2600f62f4532026928454dcea8d1c48557b3f942`. The pinned
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts` SHA-256 is
`0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0`.
`scopeCloseUnsafe` and `scopeCloseFinalizers`
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3779-3828`) close state
first, retain the same callback exit, and distinguish zero, one and multiple
captured exits. Existing Scope, Exit and Cause declarations remain unchanged.

## Owned data and boundary

The namespace is `Effect4.ScopeMachine`. `κ`, `φ`, `ε`, `δ`, `ι`, and `α`
range independently within `Type u`; the body value `β` ranges over `Type v`.
The machine retains both universe parameters, as the existing Scope does.

| Declaration | Disposition and exact content |
| --- | --- |
| `Phase (φ : Type u)` | New execution-control data: `ready`, `waiting (finalizer : φ)`, `complete`, in that order. |
| `State κ φ β ε δ ι α` | New residual evaluator state. Fields, in order: `scope : Scope κ φ β ε δ ι α`; `original : Exit β ε δ ι α`; `pending : List φ`; `captured : List (φ × Exit Unit ε δ ι α)`; `phase : Phase φ`. |
| `request?` | Derived view of the waiting phase, returning `Option (Nat × φ × Exit β ε δ ι α)`. The ordinal is `captured.length`. Other phases return `none`. |
| `result?` | Derived completed-result view. Other phases return `none`. |
| `journal` | Derived ordered list of all reasons from captured exits, retaining duplicates and annotations. It is not a reconstruction from the restored final cause. |
| `restore?` | Derived completed view, applying existing `Exit.restoreAfterFinalizer original` to the completed cleanup result. Other phases return `none`. |

`Phase` and `State` derive `DecidableEq`. They contain no service function,
closure, `Expr`, source graph, decoder, precomputed whole-run result or host
object. `φ` remains a nominal request payload; the battery instantiates it
with an operation identity and a wire value. The captured request/exit pairs
are the canonical ordered journal. Do not store a second independently
mutable failure list or introduce another Scope, Exit, Cause or Program.

The module imports only `Effect4.Runtime.Scope`. It does not import Flow,
the region runner, TypeScript lowering, or the generic frame machine. The
caller retains its outer continuation; this component returns cleanup data
and the derived restored exit. Registration is still owned by Scope, and
the caller supplies a scope whose registrations already exist.

This is the existing sequential `closeExitsM` interpreter for either retained
strategy label. Every transition preserves `scope.strategy`. It does not
implement or claim parallel callback scheduling. The general monadic
`Scope.closeExitsM` stays unchanged; the executable convenience driver in this
packet is specialized to explicit stateful callbacks.

## Frozen operations

Exact constructor/function ascriptions and the ten theorem statements are
in `Effect4Test/Runtime/ScopeMachineContract.lean`.

`start scope original` first saves `scope.closeOrder`, then retains
`scope.closeState original`, the supplied original exit, that pending list,
no captured receipts, and phase `ready`. An already closed scope keeps its
stored exit and has no pending requests. `start` invokes no callback.

`advance state` has four equations. A ready state with `f :: rest` becomes
waiting for `f` with pending `rest`; all other fields are unchanged. A ready
state with no pending request becomes complete. Waiting and complete states
are unchanged. Exposing a request does not execute it or fabricate its reply.

`respond state ordinal exit` returns `some` updated state only when the state
is waiting and `ordinal = state.captured.length`. It appends the waiting
operation and supplied exit to `captured` and changes phase to ready. It
changes no other field. Wrong phase, stale/duplicate ordinals, and future
ordinals return `none`; the original state remains available unchanged.
Ordinals identify requests within this close instance. Routing a response to
the correct close instance belongs to the caller.

`result?` in the complete phase folds the captured exits by the exact existing
Scope policy: no exits gives `Exit.void`; one gives that exit unchanged; two
or more use `Exit.asVoidAll`. In particular, a singleton failure with an empty
cause stays failure, while multiple empty-cause failures merge to void. A
ready state with no pending requests is still unfinished until advanced.

For `σ : Type u`, the convenience driver has the exact shape:

```lean
runState
  (handler : φ → Exit β ε δ ι α → StateT σ Id (Exit Unit ε δ ι α))
  (budget : Nat) (machine : State κ φ β ε δ ι α) (world : σ) :
  State κ φ β ε δ ι α × σ
```

The product order is machine first, service state second. Explicitly returning
this pair preserves the independent `β` universe; a single monomorphic monad
cannot simultaneously hold the lower-universe release exit and the
higher-universe machine without a lift. The request/response interface itself
is independent of a monad and can be driven by an external asynchronous caller.

At budget zero, the driver returns both inputs unchanged. At a positive
budget, ready performs one `advance`; waiting executes exactly its exposed
handler request, accepts that response and retains the returned service state;
complete returns unchanged. Ready and waiting each consume one microstep.
The handler is an external interpreter argument, never stored in State. It
answers one request at a time, not a completed-run oracle.

`bound scope = 2 * scope.closeOrder.length + 1`. Each callback requires a
request step and a response step, followed by one completion step. This is
machine budget, not region/source fuel. A paused close retains its waiting
request, pending operations, captured failures and service state.

## Required local proofs

| Public theorem | Required judgment |
| --- | --- |
| `request_uses_original` | Every exposed request carries the stored original exit. |
| `respond_rejects_wrong_id` | A response whose ordinal differs from the captured length is rejected. |
| `respond_rejects_wrong_phase` | Ready and complete states reject responses regardless of ordinal or exit. |
| `runState_zero` | Zero budget preserves the entire machine and service state. |
| `runState_add` | Running `first + later` microsteps equals running `first`, then `later` from both returned components. |
| `runState_scope` | Every budget preserves the input machine's retained scope. |
| `runState_prefix` | Every prefix from start has the same closed scope and original exit; completed operation identities followed by the waiting operation, if any, followed by pending operations equal the initial close order; captured replies and the actual service state agree with executing exactly those completed operations against the original exit. A complete phase has no pending operations. |
| `runState_complete` | At `bound`, the complete returned machine and final service state equal the result of existing `Scope.closeExitsM`, with operation identities zipped to the actual captured exits, no pending work, and the unchanged closed scope/original exit. |
| `runState_result` | For every pure callback, scope, original exit and initial state, the completed result is exactly existing `Scope.closeResult`. |
| `runState_restore` | For every stateful callback, scope, original exit and initial state, the restored view and final service state equal existing `closeExitsM` followed by the exact zero/one/many fold and existing `restoreAfterFinalizer`. |

The builder may use a private reachable-prefix invariant. It must retain
actual operation identities and their partition into captured, waiting and
pending work, the fixed exit and the closed scope. A length-only or nonempty
invariant does not satisfy this contract. Do not discharge the bridge by
calling `closeExitsM` inside `runState` or by replaying a source runner.

The complete-state and prefix equations keep service state produced before a
failure and every response, including repeated failures. No successful-release,
nonempty-cause, empty-failure, infallible-service or positive-budget premise is
allowed. The public statement types are frozen; proof difficulties do not
authorize altering their referents or observations.

## Independent attacks and assurance

The existing stable attacks apply: `E4-RUN-CE-001` state before callbacks,
`002` LIFO, `003` repeated close, `008` failure capture, `009` zero/one/many,
`E4-TARGET-CE-019` fixed same-scope exit, and `020` live suspended work. The
battery keeps nonempty controls and checks stale, duplicate, future and
wrong-phase replies; two failing releases; state changes before failure;
pauses before requests, while waiting, after each response and before
completion; duplicate reasons; singleton empty failure; and repeated close.
These are finite controls, separate from the universal local theorems.

The assurance route is the existing Scope proof graph and the local Scope
side of the D4 semantics connection. The coordinator owns graph wiring and
status. This packet closes no general region compilation/prefix relation,
generic arbitrary-program finalizer evaluation, frame-machine relation,
TypeScript admission, host bridge, interruption or parallel scheduling edge.
The previous region/frame counterexamples remain unchanged.

Allowed transitive axioms are `propext` and `Quot.sound`. No `sorryAx`,
`Classical.choice`, `native_decide`, new axiom, unsafe escape, or changed
existing owner is accepted. The separate builder preserves this packet.

## Verification

```text
lake env lean Effect4Test/Runtime/ScopeMachineContract.lean
lake env lean Effect4Test/Runtime/ScopeMachineAxiomReport.lean
```

Before implementation, the missing production import is recorded separately
from declaration-red evidence. Scratch controls drop that import and the new
surface/behavior sections; all existing-meaning controls must pass. A planted
wrong expected policy must reach and fail the corresponding control, followed
by a passing restored control. A separate declaration-red copy checks the
exact absent API/theorem names. Signature-shell checking validates future
consumer types without claiming that absent operations execute or that their
theorems are proved. Scratch files remain outside the repository.

### Freeze receipt, 2026-09-03

The coordinator reviewed and approved the public data, operation signatures,
exact pair and budget order, prefix identity/state equation, independent body
value universe, and all future behavior expectations before this freeze.
The inspected repository base was
`f7cd8a18a93e35b846d84c926cf67e14b02db0cb`, on Lean `v4.33.1`.

Existing semantic references were unchanged during the packet:

| Owner | SHA-256 |
| --- | --- |
| `Effect4/Runtime/Scope.lean` | `b54b62b214b3f3e2f764000305c3f2dacdc8d6ce5771444d6c7400d3d982a9d5` |
| `Effect4/Semantics/Exit.lean` | `a4a4c024ad54a8ab6e52acc1493183349bb532e668af0ed7c2512fa134161383` |
| `Effect4/Semantics/Cause.lean` | `fc7d008f2955a5ea812717a77e2f3e3d187980c924fc0cb25d5014644c7f7196` |

Scratch preparation and logs are in `/tmp/effect4-scope-machine-breaker`.
`prepare.py` derives the isolated copies from the exact packet source.

| Narrow check | Observed result |
| --- | --- |
| `lake env lean /tmp/effect4-scope-machine-breaker/Controls.lean` | Exit 0; all 27 existing-owner controls pass. The restored control passes again after the three mutants. |
| `lake env lean /tmp/effect4-scope-machine-breaker/ThreadedExitMutant.lean` | Exit 1 at exactly the changed candidate's fixed-original-exit assertion. |
| `lake env lean /tmp/effect4-scope-machine-breaker/AbortMutant.lean` | Exit 1 at exactly the changed candidate's complete-response assertion. |
| `lake env lean /tmp/effect4-scope-machine-breaker/SingletonMutant.lean` | Exit 1 at exactly the changed candidate's singleton empty-failure assertion. |
| `lake env lean /tmp/effect4-scope-machine-breaker/DeclarationRed.lean` | Exit 1 with exactly 21 absent public type/function/theorem identifiers; no control, parse or expected-type error. |
| `lake env lean /tmp/effect4-scope-machine-breaker/AxiomsRed.lean` | Exit 1 with exactly the ten absent public theorem constants. |
| `lake env lean /tmp/effect4-scope-machine-breaker/SignatureShell.lean` | Exit 0; the proposed data shapes, 19 operation/theorem signatures, exact consumer ascriptions, concrete target equality instance, and 72 future behavior expressions elaborate. |
| Both repository verification commands above | Exit 1 because `ScopeMachine.olean` is absent. This import failure is recorded separately from the declaration-red checks. |

The signature shell uses abstract assumptions only under `/tmp`, marks the
dependent scratch consumers noncomputable, and replaces future guards with
type/decidability checks. It supplies no production implementation, executes
none of the 72 future machine observations, and proves none of the ten owed
theorems. No shell assumption or noncomputable escape appears in this packet.
The actual future guards remain unchanged executable requirements for the
builder. No production file, existing contract, root import, generated
projection or host artifact was changed; no package build or host gate ran.
