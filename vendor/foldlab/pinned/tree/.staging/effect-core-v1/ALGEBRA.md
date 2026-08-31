# Effect Core v1 — proposed algebra and semantics

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

Claim gate: none

Depends on: `PLAN.md`

Representation constraints are imported from `EXHIBITS-REVIEW.md`; per-type
implementation and cutover edges are owned by `TYPE-CLOSURE.md`. The scratch
exhibit declarations are not public declarations in this algebra.

The evidence-backed §17 rulings freeze conditions 10, 11, 15, 16, 18, 19,
20, and only the classifier half of condition 17 as constraints on a later
Pass B signature. Condition 14 remains open pending a neutral protocol
operation identity and its admission bridge to `Sig.Op`; renderer injectivity,
the second half of condition 17, also remains open. These rulings discharge no
theorem in this PRE-GRADE packet.

Every `EC1-*` name in this document is a **PROPOSED TERM** unless its line is
explicitly labeled **PROPOSED RULING**, **PENDING THEOREM**, or **PENDING
FALSIFIER**. Mathematical notation describes requested declarations; it is not
Lean code and establishes no claim.

## 1. Term ledger

| ID | Status | Proposed term | Purpose |
| --- | --- | --- | --- |
| `EC1-A01` | PROPOSED TERM | `ValueTy` | Closed universe of first-order value type codes. |
| `EC1-A02` | PROPOSED TERM | `Value` | Intrinsically typed semantic values indexed by `ValueTy`. |
| `EC1-A03` | PROPOSED TERM | `ErrorRow` | Canonical finite tagged sum of typed failures. |
| `EC1-A04` | PROPOSED TERM | `RequirementRow` | Canonical finite map from service keys to interfaces. |
| `EC1-A05` | PROPOSED TERM | `AER` | Result type, typed-error row, and service-requirement row. |
| `EC1-A06` | PROPOSED TERM | `Alphabet` | Smaller project-authored, closed, versioned table of operation descriptors selected from the public-surface mapping. |
| `EC1-A07` | PROPOSED TERM | `OpDesc` | Request, answer, typed-error, service, resumption, and observation metadata for one operation. |
| `EC1-A08` | PROPOSED TERM | `PureExpr` | Total, terminating first-order pure expression, outside the effect graph. |
| `EC1-A09` | PROPOSED TERM | `PureAtom` | Named total pure function with a Lean model and separately pinned host body. |
| `EC1-A10` | PROPOSED TERM | `ArgMap` | Typed vector of pure expressions used to cross a graph edge. |
| `EC1-A11` | PROPOSED TERM | `RawProgram` | Fully serializable graph candidate that retains invalid states. |
| `EC1-A12` | PROPOSED TERM | `ProgramWF` | Inductive well-formedness judgment over a raw program. |
| `EC1-A13` | PROPOSED TERM | `CheckedProgram A E R` | Raw program paired with checked evidence and synthesized `A/E/R`. |
| `EC1-A14` | PROPOSED TERM | `Block` | Typed parameters, owning region, existing `PProg` sequential body, and one effect/control terminator. |
| `EC1-A15` | PROPOSED TERM | `Term` | Closed sum of all admitted effect/control suspension forms. |
| `EC1-A16` | PROPOSED TERM | `Resume` | One-shot successor code point plus typed answer argument map. |
| `EC1-A17` | PROPOSED TERM | `Region` | Named lexical/dynamic boundary for scopes, handlers, masks, and ownership. |
| `EC1-A18` | PROPOSED TERM | `Flow A E R` | Checked graph together with one entry code point and declared exits. |
| `EC1-A19` | PROPOSED TERM | `FlowAlg` | First-order composition operations over `Flow`. |
| `EC1-A20` | PROPOSED TERM | `CauseTree E` | Ordered project-owned typed failure, defect, interruption, sequential-cause, or parallel-cause tree. |
| `EC1-A21` | PROPOSED TERM | `Exit E A` | Success with `A` or failure with `CauseTree E`. |
| `EC1-A22` | PROPOSED TERM | `DirectHandler` | Total typed operation-clause table over one alphabet version. |
| `EC1-A23` | PROPOSED TERM | `HandlerEnv` | Direct service-key-to-handler map, with explicit named parent delegation only. |
| `EC1-A24` | PROPOSED TERM | `ScopeFrame` | Finalizers, child fibers, handler delta, mask, and pending exit for a live scope. |
| `EC1-A25` | PROPOSED TERM | `FiberState` | Code point, typed environment, call stack, scope stack, status, and interruption flag. |
| `EC1-A26` | PROPOSED TERM | `Configuration` | Whole reference-machine state: world, fibers, scopes, handlers, scheduler, and trace. |
| `EC1-A27` | PROPOSED TERM | `Step` | Labeled small-step relation. |
| `EC1-A28` | PROPOSED TERM | `execStep` / `execN` | Deterministic runner from scheduler state/policy in `Configuration` and one compatible typed decision tape. |
| `EC1-A29` | PROPOSED TERM | `FinApprox` | Finite observation tree with halted leaves, scheduler branches, and external-request frontiers. |
| `EC1-A30` | PROPOSED TERM | `Runs` / `Denotes` | Full program meaning as labeled relational reachability propositions. |
| `EC1-A31` | PROPOSED TERM | `ObservationMask` | Declared projection selecting the observations relevant to an equivalence claim. |
| `EC1-A32` | PROPOSED TERM | `ForeignEffect` | Registered effect atom with types, handler model, frame, receipt, and host pin. |
| `EC1-A33` | PROPOSED TERM | `TsCore` | Small typed target IR for generated Effect TypeScript. |
| `EC1-A34` | PROPOSED TERM | `AcceptedTs` | Source bytes accepted by TypeScript, Effect tsgo diagnostics, and the structural decoder. |
| `EC1-A35` | PROPOSED TERM | `CasEmbedding` | Injection/projection seam that retains canonical `PProg` identity. |
| `EC1-A36` | PROPOSED TERM | `PublicSurface` | Mechanically closed rc.112 module/export/member/overload ledger. |
| `EC1-A37` | PROPOSED TERM | `SurfaceDisposition` | Exactly one of the seven source-to-model dispositions for each public row. |
| `EC1-A38` | PROPOSED TERM | `CauseReasons E` | rc.112-compatible flat, stably de-duplicated reason sequence. |
| `EC1-A39` | PROPOSED TERM | `quotientCause` | Explicit lossy map from ordered `CauseTree` to `CauseReasons`. |
| `EC1-A40` | PROPOSED TERM | `CasAdmissible` | Decidable predicate selecting raw `PProg` values that can form a well-typed Core entry. |
| `EC1-A41` | PROPOSED TERM | `CheckedPProg` | Subtype `{ p : PProg // CasAdmissible p }`; the domain of total CAS injection. |
| `EC1-A42` | PROPOSED TERM | `CasImage` | Checked graph proven to be the canonical normalized image of one `CheckedPProg`, not every graph with equivalent CAS behavior. |

## 2. Closed type and operation universes

### 2.1 Values

`EC1-A01 ValueTy` is a versioned tagged sum with at least:

```text
unit | bool | u8 | u32 | nat | int | text | bytes | addr32
product fields | sum alternatives | list element | option element
schema schemaId | service serviceId
cause errorRow | exit errorRow resultTy
fiber region lifetime resultTy errorRow
resource region resourceKind | foreign foreignTypeId
```

Recursive application data is referenced through a declared schema or CAS
address; the runtime value universe does not admit a host object or function.
`EC1-A02 Value τ` is the semantic interpretation of one type code. A raw value
stores its type tag and payload separately so wrong tags, missing fields,
out-of-range numbers, invalid addresses, and region forgery remain expressible
as checker inputs.

`ValueTy` is not a replacement for the shipped
`Cas.Schema.El : Ast -> Type`. On the overlapping inhabited structural
fragment, a partial code map `toAst?` and an equivalence
`Value τ ≃ Cas.Schema.El ast` make `El` the meaning owner. `El`'s currently
empty declaration, enum, tuple, reference, suspension, and undiscriminated-
union arms remain explicit insufficiencies; the Core does not pretend they are
inhabited. Effect-specific cause, exit, fiber, and resource handles have no
current `Ast` image and therefore remain a separately justified extension with
their own constructor/checker/semantics/codec proof rows.

Checked `EC1-A03 ErrorRow` and `EC1-A04 RequirementRow` values are sorted,
duplicate-free finite maps. Raw rows retain duplicate keys so the checker can
reject them. Row union, difference, lookup, and inclusion are decidable and
canonical after admission. Any theorem equating permutation/row equality with
normalized bytes carries `NodupKeys` (or a stronger checked-row premise);
last-wins normalization on duplicate raw keys is not permutation invariant.
Error alternatives carry a stable tag and payload type. Service requirements
carry a stable service key and interface version.

On the protected CAS sublanguage, refusal-kind classification reuses the
existing `Refusal.Clause` and `RefusalMap`; Effect Core does not mint a second
CAS refusal enum. That map is a classifier/bridge for existing failures, not
the source of an exact TypeScript `E`. Exact `E` is synthesized from checked
`OpDesc.errorRow` values and overload-derived catch/provision transforms.

`EC1-A05 AER := (A : ValueTy, E : ErrorRow, R : RequirementRow)` is a static
type, not a runtime trace summary:

- `A` is the success value at the entry's normal exit;
- `E` contains exactly the typed failure alternatives that may escape the
  checked graph after direct handlers are applied; and
- `R` contains exactly the services that an enclosing environment must supply.

Defects and interruption inhabit `CauseTree E` but do not enlarge `E`.

### 2.2 Closed alphabet

The current Lean-side candidate for `EC1-A06 Alphabet` is content with a
version, an existing semantic `Cas.Lang.Sig`, a finite canonical enumeration
of that signature's `Sig.Op`, and a sorted dependent table of `EC1-A07 OpDesc`
records. `OpDesc op` records metadata for the existing operation and proves
that `answerTy` denotes `Sig.Ans op`:

```text
OpDesc =
  semanticOp        op : alphabet.sig.Op
  opId              stable operation identifier
  requestTy         request payload type
  answerTy          successful answer type
  errorRow          typed failures produced by the operation
  requirementRow    possibly-empty services required from the caller
  handlerRoute      builtin builtinHandlerId | service serviceKey
  resumption        zero | one | many
  cancellation      interruptible | masked | handlerDecides
  observation       public | receiptOnly | hidden
  capabilityClass   finite declared capability identifier
```

**PROPOSED RULING `EC1-R17` — one-shot v1.** The checker admits only `zero` and
`one` resumptions in v1. `many` remains an encoded refusal with a stable
diagnostic, not an untracked implementation gap. Scoped and higher-order
behavior is expressed through named body regions, not multi-shot host
continuations.

The alphabet contains built-in CAS operations, typed failure/runtime tracing
operations selected for v1, and a finite list of registered foreign effects.
`requirementRow` is empty for a builtin operation and may contain one or more
service identifiers for an environment-supplied operation. Handler routing is
therefore distinct from the public `R` projection: selecting a builtin direct
handler does not invent a service requirement. Adding an operation changes the
alphabet version and reopens all totality and code-generation tables.

`Alphabet.toSig` returns this existing semantic signature; it does not create a
replacement handler language. Extension is `Sig.sum`/`⊕ₛ`, with metadata
reindexed over the left and right injections. The shipped `CasSig`, `RootSig`,
`StoreSig`, `WordSig`, and `WordedSig` identities and their CAS non-disturbance
and preservation theorems remain the extension-law anchors. D13 reification
grades live in `OpDesc`/surface links, never as a field added to `Sig`.

**OPEN FREEZE CONDITION 14.** This Lean-side shape is not yet the full public
operation-identity design. Before it can freeze, the packet must define a
neutral protocol operation identity and an explicit admission bridge from each
Lean-modeled identity to its existing `Sig.Op`/`Sig.Ans`, while leaving
host-obligation identities representable without pretending they already have
a Lean `Sig.Op`. The shipped `Sig.sum` and Root/Word laws constrain that bridge;
they do not by themselves settle it.

### 2.3 Public-surface mapping input

`EC1-A36 PublicSurface` and `EC1-A37 SurfaceDisposition` are first-order input
types consumed by the authored `Alphabet`; they do not define source closure or
source dispositions here. `REIFICATION-CHECKLIST.md` owns their recursive
rc.112 census, row schema, seven values, and totality gate. This algebra uses
only checked mapping rows and keeps the authored operation table smaller than
the public-source universe.

## 3. Pure code stays outside `Flow`

`EC1-A08 PureExpr Γ τ` is a total first-order expression from typed inputs `Γ`
to `τ`. Its proposed constructors are literals, tuple/record construction and
projection, sum injection and case, equality and ordering on admitted scalar
types, finite collection operations with structurally smaller recursion, and a
call to an `EC1-A09 PureAtom`.

A `PureAtom Γ τ` contains:

1. a stable identifier and type;
2. a total Lean meaning `Value Γ -> Value τ`;
3. a separately identified TypeScript implementation;
4. an explicit statement that it reads and writes no effect world; and
5. a conformance obligation between the host body and the Lean meaning.

If a host operation reads time, randomness, process state, a mutable cell, the
network, or any ambient service, it is not pure and must be `ForeignEffect`.
There is no “trust me” pure escape.

The pure fragment also has an inductive `PureDenotes env e v` judgment.
`evalPure` is accepted only with a two-way adequacy theorem against that
judgment and a structural termination argument. The tautology that one Lean
function returns one result is not a proof obligation.

`EC1-A10 ArgMap Γ Δ` is a vector containing one `PureExpr Γ τ` for every
destination parameter `τ` in `Δ`. Branch guards and return values are also
pure expressions. Thus effect-free calculation is never represented by a
`Prog` constructor, while its typed data dependencies remain reified.

## 4. Raw and checked program boundary

### 4.1 Raw carrier

`EC1-A11 RawProgram` contains only serializable first-order data:

```text
alphabetVersion   declared closed alphabet
publicSurface     frozen rc.112 ledger identity and mapping schema version
declaredAER       claimed result/error/requirements
pureTable         named PureExpr and PureAtom declarations
foreignTable      named ForeignEffect declarations
handlerTable      named direct-handler graph declarations
codeTable         named code definitions and their interfaces
regionTable       region ownership and policies
blockTable        finite BlockId -> RawBlock map
entry             CodeId and initial BlockId
presentation      format version and source-span map
```

Raw identifiers are ordinary bounded numbers or canonical names. Duplicate
identifiers, dangling references, forged region tokens, invalid rows, bad
types, illegal back edges, host-function payloads, and incomplete handlers are
deliberately representable.

### 4.2 Blocks and terminators

`EC1-A14 Block Γ` owns a region, accepts typed parameters `Γ`, runs one
existing `PProg` sequential body through its existing admission/embedding, and
ends in exactly one `EC1-A15 Term Γ`. The graph adds parameters, region, and
terminator around `PProg`; it does not introduce a second straight-line body
carrier or another canonical CAS spelling. A terminator is one of:

```text
close result
jump target args
call code args exits
perform op request onAnswer
raise typedError
die defect
branch guard ifTrue ifFalse
scope policy body exits
provide handler body exits
onExit finalizer next
fork lifetime child onFiber
await fiber onExit
join fiber onSuccess onCause
requestInterrupt fiber next
interruptAwait fiber next
yield next
race policy children exits
mask mode body exits
```

`ForeignEffect` is reached through `perform` using its registered operation ID;
there is no second foreign-call semantics. `acquireRelease` and the familiar
Effect combinators are checked elaborations into `scope`, `perform`, `onExit`,
and explicit exits rather than additional primitive meanings.

Every successor is an `EC1-A16 Resume`: a destination block plus an `ArgMap`
whose source context includes the typed answer when the terminator produces
one. A resume token is consumed once. No field has a function type, and no
stored constructor contains `Answer op -> Flow`.

The block body reuses `PProg` answer indexing and its exact CAS semantics.
General effect operations remain explicit terminators; sequencing such
terminators creates additional blocks. `PProg` remains the body and canonical
CAS content owner rather than being copied into a new line/table type.

Cycles are ordinary references to earlier blocks. Recursive calls name a
`CodeId`; every captured value is an explicit call argument. This is closure
conversion and defunctionalization at the content boundary.

### 4.3 Well-formedness

`EC1-A12 ProgramWF raw` is the conjunction of separately named inductive or
decidable judgments:

1. `IdsWF`: every table is duplicate-free and every reference resolves;
2. `TypesWF`: block parameters, argument maps, operations, exits, and declared
   code interfaces agree exactly;
3. `RowsWF`: all rows are canonical and every escaped typed failure is in `E`;
4. `RegionsWF`: region nesting is acyclic, tokens do not escape their owner,
   and every scoped body has complete exit routing;
5. `HandlersWF`: the selected direct environment has exactly one typed clause
   for every reachable operation or a named parent delegation;
6. `ResumeWF`: every one-shot resume token has one syntactic owner and no
   duplicate consumption path within a single transition;
7. `FibersWF`: handles carry their result/error/region/lifetime indices, and
   scoped handles cannot outlive their supervisor;
8. `ResourcesWF`: resource tokens cannot escape their scope and release bodies
   have the declared input and exit types;
9. `ForeignWF`: every foreign ID resolves to a registry entry whose types,
   frame, receipt codec, and observation class are present;
10. `EntryWF`: the entry accepts exactly its declared input and every normal
    return has result type `A`;
11. `AERWF`: synthesized `A/E/R` normalizes to the declared triple; and
12. `PresentationWF`: normalization does not change reference meaning.

`EC1-A13 CheckedProgram A E R` stores an erased raw value, normalized lookup
tables, and evidence of `ProgramWF`. The only public constructor is a checker:

```text
check : RawProgram -> Except Diagnostic (Sigma CheckedProgram)
erase : CheckedProgram A E R -> RawProgram
```

The checker is canonically ordered and fail-fast. Its diagnostic identifies
the first failing table row, expected/actual type, and violated clause. It does
not promise to enumerate every distinct clause that condemns the same raw
program. Admission performs no I/O and does not consult TypeScript or the
Effect language service; those tools gate source bytes, not graph truth.

## 5. The `Flow` algebra

`EC1-A18 Flow A E R` is a checked program slice with one entry and named
normal/cause exits. `EC1-A19 FlowAlg` supplies graph-building operations whose
results remain first-order:

```text
close    : PureExpr Γ A -> Flow A empty empty
seq      : Flow A E1 R1 -> ContRef A (Flow B E2 R2)
           -> Flow B (E1 union E2) (R1 union R2)
choose   : PureExpr Γ bool -> Flow A E1 R1 -> Flow A E2 R2
           -> Flow A (E1 union E2) (R1 union R2)
catch    : Flow A E1 R1 -> CatchRef Handled B E2 R2
           -> Flow (unionTy A B) ((E1 minus Handled) union E2)
                   (R1 union R2)
scope    : ScopePolicy -> Flow A E R -> Flow A E R
ensure   : Flow A E1 R1 -> FinalizerRef E2 R2
           -> Flow A (E1 union E2) (R1 union R2)
provide  : DirectHandler H -> Flow A E (R union H.provides)
           -> Flow A (E union H.errors) ((R minus H.provides) union H.requires)
par      : Flow A E1 R1 -> Flow B E2 R2
           -> Flow (A product B) (E1 union E2) (R1 union R2)
race     : RacePolicy -> NonEmpty (Flow A Ei Ri)
           -> Flow A (union Ei) (union Ri)
feedback : CodeRef I A E R -> Flow A E R
```

`ContRef`, `HandlerRef`, and `FinalizerRef` are code IDs plus explicit capture
arguments, never meta-language functions. `close` is only the terminal bridge
from a pure value into an effect flow; all prior pure work remains in
`PureExpr`.

`Handled` is an overload-derived subrow of `E1`; exhaustive `catch` and
`catchCause` use the whole eligible row, while tag/reason/filter forms retain
the unhandled alternatives. `B` is not forced to equal `A`: rc.112 recovery
overloads expose the normalized source union `A | B`. A source-facing
`ensuring` expansion requires an empty typed finalizer-error row, matching its
selected overload; the more general `ensure` node is used only by source forms,
such as `acquireUseRelease`, whose canonical overload permits release errors.

The intended laws use normalized graph equality when presentation is the
subject and observation-indexed semantic equivalence otherwise. In
particular:

- `seq` has left/right identity and associativity up to alpha-normalization;
- pure argument mapping has identity and composition laws;
- `catch (close x) h` is equivalent to `close x`, injected into the normalized
  result union;
- `catch (raise e) h` follows the selected typed handler arm;
- `ensure` runs after success, typed failure, defect, and interruption;
- `provide` is direct table replacement at a named service key;
- loop unfolding consumes at least one transition before recurring; and
- `par` and `race` have no unconditional commutativity law under ordered trace
  observations. Any commutativity theorem must name an independence relation
  and an observation quotient.

The applicative/selective/monadic labels are classifications of graph shape,
not instances placed on the general carrier. L-A embeds in branch-free,
cycle-free `Flow`; L-S embeds in effect-answer-dependent guarded regions; the
general checked graph has monadic control without hiding functions.

## 6. Direct handlers

`EC1-A22 DirectHandler` is a total typed table indexed by alphabet version and
handler route. Each operation clause is either:

- a primitive reference-machine transition;
- a checked `CodeId` whose parameters are the request and handler state; or
- explicit delegation to one named parent handler.

The result is `Exit op.errorRow op.answerTy` plus a new handler/world state and
zero or more public events. A clause cannot call an untyped callback or resume
the operation continuation itself. The reference machine alone consumes the
one-shot resume after the clause returns.

`EC1-A23 HandlerEnv` maps every required service key to exactly one handler ID.
`provide` creates a region-local map delta and restores the parent map on every
exit. Dispatch is:

```text
op.handlerRoute = builtin id -> BuiltinHandlers.lookup id
op.handlerRoute = service key -> HandlerEnv.lookup key
selected handler -> DirectHandler.clause(op)
```

There is no nearest-handler search by runtime type, implicit fallthrough, or
open effect row. Named parent delegation is visible in content and checked for
cycles. Static service requirements come only from `op.requirementRow`, never
from the mere existence of a builtin handler route.

The CAS entry in the closed alphabet delegates to the existing
`referenceHandler`; its direct semantics is not restated.

Every graph-backed clause elaborates to the existing `Cas.Lang.Handler` in a
target monad carrying enough state/error/machine context to observe a child
outcome before deciding recovery or cleanup. Named body, handler, finalizer,
and scope children are `BlockId`s, so ordinary `Sig` and `Handler` suffice.
The scoped handler targets that adequate machine directly. Signature families
with the same target compose with existing `Handler.sum`. `Handler.through`
is reserved for a genuine tower whose upper handler has type
`Handler S (Prog T)` and whose lower handler has type `Handler T M`; it does
not retarget a scoped handler already aimed at the machine. There is no
`HHandler`. The proved
`no_handler_into_ScopeM_catches` counterexample excludes
`ReaderT Env (Prog CasSig)` as that target: its child refusal cannot be
recovered. `scopeHandlerR` witnesses catch recovery only; because its error
branch carries no word, it is inadequate for ensuring.
The frozen information contract is that state survives failure. The minimum
CAS witness has target
`ReaderT Env (ExceptT Refusal (StateT Word Id))`. The scratch `scopeHandler`,
`scopeHandlerR`, `scopeHandlerW`, and their helper carriers are evidence for
this boundary, not promoted catch, ensuring, scope, provision, failure, or
machine semantics.

## 7. Failure, scopes, and resources

`EC1-A20 CauseTree E` has the proposed constructors:

```text
fail (e : E)
die (defect : Defect)
interrupt (fiber : FiberId)
then (earlier later : CauseTree E)
both (left right : CauseTree E)
```

`EC1-A21 Exit E A := success A | failure (CauseTree E)`. Typed `catch`
handles selected `fail` leaves and retains all unhandled branches; a cause
handler must opt into defects or interruption explicitly. Sequential finalizer
failures combine with the pending cause using ordered `then`; concurrent child
failures combine using ordered `both` in canonical child order.

rc.112 does not expose this tree. Its public `Cause<E>` is a possibly-empty
`ReadonlyArray<Reason<E>>`, where a reason is `Fail`, `Die`, or `Interrupt`,
and `Cause.combine` stably unions and de-duplicates reasons by value equality.
`EC1-A38 CauseReasons E` models that public representation. The total quotient
`EC1-A39 quotientCause` is:

```text
quotientCause empty         = []
quotientCause (fail e)      = dedupStable [Fail e]
quotientCause (die d)       = dedupStable [Die d]
quotientCause (interrupt f) = dedupStable [Interrupt f]
quotientCause (then x y)    = dedupStable (quotientCause x ++ quotientCause y)
quotientCause (both x y)    = dedupStable (quotientCause x ++ quotientCause y)
```

The quotient deliberately forgets whether an internal node was `then` or
`both`; it may also forget repeated equal reasons. Full model observations may
retain ordered `CauseTree` topology. Any conformance or lowering claim through
the stock rc.112 runtime must instead select the `effectReasonQuotient` mask.
A future project-owned adapter may preserve full topology only by emitting and
checking its own topology trace; that is a project-owned replacement, not a
claim about stock `Cause`.

`EC1-A24 ScopeFrame` records:

- owning region and parent scope;
- LIFO list of registered finalizer code IDs plus captured typed values;
- owned child fiber IDs and their lifetime policy;
- handler-environment delta;
- prior interruption mask;
- pending body `Exit`; and
- finalization phase and already-run set.

Entering `scope` pushes one frame. `onExit` atomically registers a finalizer
before control advances. Resource acquisition is elaborated as:

```text
scope {
  resource <- perform acquire
  onExit (release resource)
  body resource
}
```

If acquisition fails, no release is registered. If registration completes,
release runs exactly once on every scope exit. Finalizers run LIFO and masked
by default; a finalizer may explicitly restore interruptibility. The parent
does not resume until owned scoped children and all finalizers halt. A daemon
fiber transfers ownership to the root supervisor and appears in the final
host obligation; it does not silently disappear.

`ensure` and registered finalization are reference-machine exit rules, not
ordinary `Prog.bind`. Existing `interpretRef_bind` is refusal-strict, and the
proved `ensuring_never_finalises_a_refusal` witness shows that sequencing a
finalizer with `bind` skips it on refusal. The adequate target/machine must
observe both success and failure before running cleanup.

## 8. Fibers, scheduling, race, and cancellation

`EC1-A25 FiberState` contains the current code point and environment, call
stack, scope stack, status, pending request, result type, error row, parent,
lifetime, interruption flag, and current mask.

The proposed statuses are `ready`, `running`, `suspended request`, `joining`,
`interrupting`, `finalizing`, and `halted exit`. A configuration has finitely
many fibers at every finite step.

`fork` creates a child owned according to:

- `scoped`: child must halt or be interrupted and finalized before the
  enclosing scope exits;
- `inherited`: child is supervised by the parent fiber's owner; or
- `daemon`: ownership moves to the root host supervisor and is reported.

`await` always succeeds with the child's whole `Exit`. `join` returns the
child's success value and propagates its complete failure cause into the
joining fiber, matching rc.112's distinct public operations.
`requestInterrupt` sets the target flag and continues without waiting.
`interruptAwait` sets the flag and suspends the caller until the target has
halted after cleanup, matching public `Fiber.interrupt`. At an interruptible
boundary the target begins scope unwinding; inside a mask the flag remains
pending. `yield` is an explicit scheduling point.

`race` starts all children, accepts the first scheduler-enabled exit selected
by the next typed `Decision`, interrupts every loser, waits for loser
finalization, then resumes the winner continuation. A race cannot leak a
resource or scoped fiber merely because a winner was available.

Scheduler policy and state live in `Configuration` and determine which ready
fibers and race winners are enabled. `execStep` receives no second schedule
input: its typed `Decision` selects one enabled choice, and `DecisionTape`
supplies those selections over time. Fairness is a predicate on compatible
infinite decision streams and their scheduler projections, used only by named
liveness theorems. Safety, preservation, cleanup, and finite-prefix theorems
make no fairness assumption.

## 9. Reference-machine semantics

`EC1-A26 Configuration` contains:

```text
program          one CheckedProgram
world            handler-owned abstract state
fibers            finite FiberId map
scheduler         policy and state, including the finite ready queue
scopes            finite ScopeId map
handlers          direct HandlerEnv values by region
rootSupervisor    daemon ownership and host obligations
trace             reverse list of labeled observations
freshSupply       deterministic IDs derived from execution history
```

`EC1-A27 Step : Configuration -> Label -> Configuration -> Prop` has one rule
per terminator plus administrative rules for call/return, handler completion,
scope unwinding, finalizer progression, scheduling, join wake-up, and
interruption delivery. Labels distinguish:

```text
tau | opRequest | opAnswer | typedFailure | defect | interruption
scopeEnter | scopeExit | resourceRegistered | resourceReleased
fiberFork | fiberJoin | fiberInterrupt | raceWinner
foreignReceipt | publicEvent | halt
```

Every rule states its unchanged frame explicitly: blocks and alphabet never
change; a fiber-local step changes no unrelated fiber; a handler clause may
change only its declared world frame; a scope step changes only owned
resources/children and its ancestors' wait state.

`EC1-A28 execStep` consumes one explicit `Decision` whose scheduler fields are
valid only when enabled by `c.scheduler`:

- ready fiber choice;
- operation response or suspension decision permitted by the selected direct
  handler;
- race tie choice; and
- foreign receipt matching the registry contract.

It returns `advanced`, `needDecision`, `halted`, or a checked internal
invariant violation. `execN n tape c` performs at most `n` semantic steps.
Fuel exhaustion returns `running` with the current configuration; it is not a
failure and is the only finite runner representation of possible divergence.
Likewise, an external-answer frontier and a scheduler-choice frontier are live
control states. None is a typed failure, `CauseTree`, or CAS `Refusal`.

## 10. Relational meaning and its executable/finite views

### 10.1 Executable face

For a fixed initial `Configuration`—including scheduler policy/state—and one
compatible complete `DecisionTape`, `execN` is deterministic. Replaying those
same inputs yields identical normalized observations and final state.

This path determinism does not imply that the full relational meaning is a
partial function. The kernel-checked `Denotes` uniqueness and big-step
coherence exhibit applies only to stable non-frontier outcomes in its
deterministic CAS/block subfragment. It does not identify pre-completion fuel
labels: different exhausted prefixes may carry different incidental refusal
text and still converge to the same later stable result.
For a selected deterministic unfolding, coherence is proved through
`interpretRef` or the corresponding lawful handler interpretation. Fixed-fuel
`run` has no general bind/composition law; its relationship is a separate
step/fuel adequacy theorem, never the proof of big-step coherence.

### 10.2 Relational face

`EC1-A30 Runs c tr c' : Prop` is labeled reflexive transitive closure of
`Step`; `Denotes p i tr c' : Prop` starts that relation at
`initialConfig p i`. These propositions quantify over every typed external
answer allowed by a handler contract and every choice enabled by the scheduler
stored in the evolving configuration. May properties are existential over
runs; must properties are universal over maximal runs. Divergence is an
infinite compatible chain of finite `Runs` witnesses, not an unguarded
recursive evaluator or a public behavior value.

### 10.3 Finite-approximation face

`EC1-A29 FinApprox n c` is finite data. Its leaves are:

- `halt exit worldProjection observations`;
- `live configurationSummary` at depth zero;
- `request op requestValue resumeToken` for an external answer frontier; or
- a finite `scheduler` node over the currently enabled fiber choices.

`live`, `request`, and `scheduler` are frontiers, not failed leaves. Truncation
may replace deeper structure by a frontier but never by `Refusal` or
`CauseTree`. The statement “finite” means that each produced tree has a finite
node support and size; the type of all trees may have infinitely many
inhabitants because values and requests may be infinite types.

External answer spaces may be infinite, so a request frontier does not
enumerate answers. Supplying one checked answer produces the next finite
approximation. Scheduler branching is finite because the current fiber map is
finite.

`approx n c : FinApprox n c` is derived observation data computed from the
relational step rules. `truncate m` removes observations beyond depth `m`, and
coherence is a theorem about those derived values:

```text
m <= n -> truncate m (approx n c) = approx m c
```

Adequacy states that `approx n c` contains exactly the depth-`n` observations
of `Runs` from `c`. `FinApprox` is not the full meaning, a projective-family
carrier, or a finite probe promoted to a universal proof. May/must reasoning
ranges over `Denotes`; executable-path equality is available only after fixing
the initial configuration and complete compatible decision tape, while
outcome uniqueness remains restricted to the stable non-frontier CAS/block
specialization.

No public `Behavior`, `Denotation`, or disguised coherent-family carrier is
introduced. For a mask `O`, define the relational predicate
`Observed O p i x` by existence of `tr,c'` with `Denotes p i tr c'` whose
masked observation is `x`. Then
`SemEq O p q := forall i x, Observed O p i x <-> Observed O q i x`.

`EC1-A31 ObservationMask` selects the result, cause classes, world projection,
public events, resource/fiber lifecycle events, foreign receipts, and daemon
obligations visible to a claim. Semantic equivalence is equality of masked
relational observations. The mask is an explicit theorem parameter; no theorem may
silently drop scheduling, finalizer, or foreign observations.

Cause observation has two named choices. `fullCauseTree` retains ordered
`then`/`both` topology. `effectReasonQuotient` applies `quotientCause` and
observes only rc.112-compatible de-duplicated reasons. No stock-runtime G4
statement may select `fullCauseTree`.

The required semantic triangle is:

```text
execN with DecisionTape -------- path inclusion -------> Runs / Denotes : Prop
       |                                                |
       | normalized finite observation                 | prefix extraction
       v                                                v
                         FinApprox
```

Each arrow is a PENDING theorem in `PROOF-DAG.md`.

## 11. Foreign atoms

`EC1-A32 ForeignEffect` is an alphabet entry plus:

```text
foreignId        stable, versioned identity
request/answer   ValueTy codes
errors           ErrorRow
requirements     RequirementRow
capabilities     declared finite set
worldFrame       named read/write projection
model            direct relational handler clause
receiptCodec     checked request/result/world-delta evidence
replayKey        canonical receipt key
hostPin          implementation source and build identity
observation      public, receipt-only, or hidden
```

A foreign effect may suspend and later answer, fail, defect, or be interrupted.
It cannot receive the continuation, mutate outside its declared frame in the
model, or invent a service. Runtime conformance is conditional on the host pin
and receipts; the Lean model remains meaningful even when no host exists.

Foreign pure atoms use `PureAtom`, not `ForeignEffect`, and must be total and
world-independent. Any mutation test showing otherwise reclassifies the atom
as effectful.

## 12. CAS is a protected sublanguage

`EC1-A35 CasEmbedding` has five faces:

1. `admitCas : PProg -> Option CheckedPProg`, where `CheckedPProg` carries
   `CasAdmissible` and empty or dangling tables are rejected;
2. `injectCas : CheckedPProg -> CheckedProgram addr32 RefusalRow
   CasRequirement` for semantic reasoning;
3. `toPProg : CheckedProgram -> Option PProg`, a sound recognizer for the
   canonical injected normal form;
4. `projectCas : CasImage -> PProg`, the total restriction of that recognizer
   to its proved structural image; and
5. canonical serialization that stores the existing `PProg` content or its
   address, never a second independently canonical core-graph encoding.

`CasAdmissible` is an independently stated decidable syntactic predicate. It
includes a real entry/result and closed answer-index dataflow in addition to
the existing per-line `PLine.WF`; per-line well-formedness alone is vacuous on
the empty table and does not close dangling `.ans` indices. Raw `PProg` remains
fully representable and keeps its existing refusal semantics outside this
checked injection boundary. `admitCas_iff` must prove, rather than define by
fiat, that the executable admission checker decides this predicate.

`toPProg` is not a function of denotation. It may return `none` for a graph
with an unreachable tail or a relocated entry even when that graph is
observationally equal to an injected table. A successful recognition is sound
for the canonical form; it does not license a semantic projection from all
CAS-only graphs. `CasImage` records the stronger structural premise needed by
the total `projectCas` restriction.

The injection maps `put` and `load` to the corresponding closed CAS operation
descriptors and uses the existing direct reference handler. It adds no scope,
fiber, foreign, or extra observation. Under the CAS observation mask, the
existing status and word are the entire observation.

CAS refusal kinds are related through the complete existing `Refusal.Clause`
and `RefusalMap` theorem family: model and host totality, the declared host-only
row, disjoint host images, and unique wires are routed rather than restated.
The exact target error row still comes from the injected
`OpDesc.errorRow` and checker, not from `PProg.envelope`. Write addresses and
world deltas may depend on the supplied address function `H`; an `H`-free
envelope cannot make them exact. The CAS observation must also say whether the
partial word on refusal is visible: the existing `ObsEq`-style mask hides it,
while a stronger run mask records it explicitly.

The required boundary laws are exact:

```text
(admitCas raw).isSome iff CasAdmissible raw
toPProg (injectCas p) = some p.val
toPProg g = some q -> g is the canonical injected normal form of q
projectCas (asCasImage (injectCas p)) = p.val
runCore (injectCas p) = runP p.val
canonCore (injectCas p) = canonCas p.val
classify (injectCas p) refines PProg.envelope p.val
```

Five injection/image laws quantify over `p : CheckedPProg`; admission and
general recognizer soundness quantify over raw inputs. All seven are PENDING; until
they exist, Effect Core is not allowed to replace
or re-encode a canonical CAS program.

The authenticated-computation seam also transports the existing
`whole_run_security` and `whole_run_correctness` results from
`Cas/Lang/Auth.lean`. The security bridge stays at the existing hash-lattice
Level 0: it assumes no injectivity of `H` and preserves the explicit collision
witness in the adversarial branch. A weaker receipt-only replay equation does
not discharge this obligation.

The CAS specification-logic specialization also reuses existing `WPre`,
`WPost`, `wlp`, `wp`, `Triple`, and `PartialTriple`. The EffHOL-style modality
is `wlp` on this sublanguage, and existing `wp_iff_wlp_and_total` supplies the
total-correctness decomposition. This packet introduces no duplicate modality;
any later full-core logic is either an explicit restriction or a bridge to
these owners.

EffHOL Mod-E is the new `EC1-T130` obligation, to be derived by specializing
the shipped `wpAux_append`; the estate does not ship `wlp_append`. `EC1-T130`
must require a nonempty prefix and interpret the suffix with the answer history
produced by that prefix. A restarted table-only suffix rule is false even with
nonemptiness, so no unconditional sequence modality is added. The scratch
`wlp_append` proof is evidence only and is not promoted.

## 13. Generated TypeScript boundary

`EC1-A33 TsCore A E R` is a typed, first-order target IR containing only the
pinned generation vocabulary: `Effect` success/failure and sequencing,
service access/provision, scoped acquire/release, ensuring/catch/cause,
loop/recursion through named declarations, distinct fiber await/join and
interrupt-request/interrupt-and-await operations, yield/mask/race, and
registered foreign calls. Every target node has a Lean `TargetRuns` relational
meaning and names the canonical public surface row and overload which licenses
its spelling.

The lowering path is:

```text
CheckedProgram A E R
  -> TsCore A E R
  -> rendered TypeScript bytes
  -> TypeScript 7 + @effect/tsgo diagnostics
  -> structural decode / source-to-graph relation
  -> pinned compiler and hosted execution lanes
```

`lower` may introduce names and administrative scopes but may not introduce a
new effect, service requirement, typed error, unregistered foreign call, or
unscoped fiber. Its type transform is the normalized transform stored on the
selected public overload row. Stock rc.112 lowering applies `quotientCause`;
therefore its relational preservation theorem is stated only under an
observation mask no stronger than `effectReasonQuotient`. `render` is
deterministic. A parser or
validator must recover the target structure needed for per-run validation.
Because `render` is a Lean function, repeat-call determinism alone is
tautological and earns no theorem. The substantive obligations are canonical
output bytes, decode/render round trip, and injectivity on normalized admitted
`TsCore`; distinct normalized targets may not collapse to the same bytes.
Renderer injectivity is the still-open half of freeze condition 17: it remains
a proposed obligation, not a frozen representation ruling or inherited fact.

`EC1-A34 AcceptedTs` is only a source/tooling judgment:

```text
AcceptedTs bytes target :=
  TypeScript7 accepts bytes
  AND @effect/tsgo reports no configured error or warning
  AND structuralDecode bytes = target
  AND rerender target = canonicalize bytes
```

The required harness is the TS7 successor path already present in
`library/effects`: exact `typescript@7.0.2`, exact `@effect/tsgo@0.38.0`, the
`@effect/language-service` plugin name, and the repository's patch script.
The former standalone language-service package/repository is prior-art only
for this lane; TS7 execution goes through `@effect/tsgo`.

TypeScript and Effect-language diagnostics are not denotational authority.
They do not construct `ProgramWF`, choose a handler meaning, or prove
preservation. They are required negative and positive acceptance evidence at
the source boundary. A source-to-graph bridge must still relate structurally
decoded, accepted bytes to a `CheckedProgram` through a Lean-defined relation.

Code actions are treated as candidate canonicalizers. A configured code action
is admitted only if applying it twice is byte-idempotent after formatting and
if both the pre/post source decode to semantically equivalent checked graphs.
Negative mutations must trigger the expected stable diagnostic class or fail
structural decoding; a clean diagnostic run alone never admits a graph.

Semantic preservation is split deliberately:

1. prove `Observed O p i x <-> TargetObserved O (lower p) (lowerInitial i) x`
   in the Semantic Model, using `effectReasonQuotient` for stock rc.112;
2. validate rendered bytes decode back to the same `TsCore`;
3. run exact TypeScript and Effect tsgo diagnostic gates;
4. separately establish G5 compilation preservation for a pinned compiler;
5. separately establish G6 observations for a named engine and host.

Neither steps 4 nor 5 can promote a stock rc.112 result to full ordered
`CauseTree` topology. Such a claim requires a separately generated and
validated project-owned topology-preserving adapter.

Nothing in this packet establishes any of those five steps.
