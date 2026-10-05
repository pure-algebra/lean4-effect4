# Mask second note: representation and typed-state review

Recommendation: accept the three representation directions, after the corrections below.
The saved choice can remain first-order data.
No general closure representation or parent activation is needed.

Evidence: source inspection at `c3263529a0edeb35c9aa89c10cf62ba9978b9c4d`.
Scope: `mask-second-note.md` F3, F4, F7 to F10 and proposals 1, 2 and 5.
No Lean, generator, runtime probe or repository mutation ran.
The note's existing runtime receipts remain finite target evidence.

## 1. Correct the body's address

F3 compiles the false arm at `p.child 1`.
The body is the constructor's only node child, so its address is `p.child 0`.
`Term` arguments do not count as node children.

Sources:

- `Node` in `src/Effect4/Program/Node.lean` states this convention.
- `Node.child` in `src/Effect4/Program/NodeLenses.lean` addresses `provideService`'s body at zero, despite its preceding key and term.
- `compileEff`, `resolve` and `Point.child` in `src/Effect4/Program/Compile.lean` consume those addresses.

A pure success can hide the mistake.
A bind body installs a continuation containing the wrong address.
Its later lookup reaches `badShape`, whose cause is `Defect.badName`.
This is a source-derived failure of the sketch, not an executed counterexample.

Repair: use child zero in compilation, `actionAt`, denotation and the corresponding typing clause.
Control: restore both token values around a bind that reads an outer capture and then performs another operation.
Check the actual compiled path, not only the handwritten TypeScript form.

## 2. Reserve the type and extend membership

F3's cost, "one arm of Val.hasTy", understates the change.
The existing membership rule admits an external allocation at any unreserved handle target.
Such a value is an external handle, not the Boolean that the proposed restore evaluator reads.

Sources:

- `internalHandleTargets`, `externalHandleTarget`, `Val.hasTy` in `src/Effect4/Program/Typed.lean`.
- `HandleFits`, `Fits`, `FlatFits`, `fits_flatFits` in `src/Effect4/Laws/Program/Typed/Membership.lean`.
- `flatCarrierAlg`, `rowChecks` in `src/Effect4/Program/SigApp.lean`.
- `findInternalHandle` in `src/Effect4/Program/Columns.lean`.
- `externalValue` in `src/Effect4/Program/Compile.lean`.

Without reservation, a host row can name the new target and introduce an allocated external handle.
Typing then accepts its use as a restore value, but the proposed evaluator rejects its shape.

Repair: reserve the exact target and make membership at it mean precisely an encoded saved Boolean.
Connect `Val.hasTy`, `Fits`, normalization, widening, world extension and inhabitance at that target.
Reserve it in host answer admission and external allocation.

There is also an admitted service case.
`flatCarrierAlg` presently admits every handle target except `Ty.contextTarget`.
Therefore a service can carry the proposed token without another checker change.
Either extend `FlatFits` and the context membership connection, or explicitly refuse this carrier in the initial profile.
Passing through Ref, Deferred, products and captured environments must retain the same token meaning.
No new allocation or owning scope is required for the Boolean representation.

## 3. State the mask law at boundaries

F7's first two universal statements are false for the existing typed language.
A body may explicitly enter `interruptible` outside any restore site.
A restored body may explicitly enter `uninterruptible` inside the restore site.
Both are accepted today.

Sources:

- `Checker.check` in `src/Effect4/Program/Checker.lean` admits both region constructors.
- `FrameFiber.uninterruptible` and `FrameFiber.interruptibleRegion` in `src/Effect4/Machine/Frames.lean` implement those overrides.
- `uninterruptible_arm` and `interruptible_arm` in `src/Effect4/Laws/Program/Typed/Denotation.lean` type them.

Repair the statements before creating their planned goal.
At mask entry, set the flag false.
At restore entry, true selects interruptible execution; false leaves the current flag unchanged.
Nested regions retain their existing rules.
At each completed region exit, restore the region's previous flag and apply the pending-cause rule.
No invariant says that all subsequent body steps retain the entry flag.

Controls: an explicit interruptible region without restore, and an explicit uninterruptible region inside restore.
Include an escaped false token applied under an interruptible caller; identity must leave that caller interruptible.

## 4. Accept passing the token as data with the complete proof path

Proposal 5 needs the owner amendment already identified by F4.
After that amendment, capture and storage do not require an activation-lifetime check.
The token selects identity or the global interruptible operation at its later invocation.
It must not read its parent's current flag or install cleanup in the parent's stack.
The existing `uninterruptibleMask` implementation in both vendored releases supports this interpretation.

F10 should include the following placed steps before implementation starts.
These are proposals, not landed goals.

| Proposed step | Placement and consumer | Premises and observation | Exclusions and immediate prerequisite |
| --- | --- | --- | --- |
| Saved-token membership and introduction | `store-typing`, R4; step of `fits-mono` and the getter's typed answer | Reserved target; encoded Boolean; typed stores and environments; later worlds retain membership | No host function equality or progress. Fix the target reservation and membership cases first. |
| Getter and restore typed execution | `residual-program-typing`, R4; `scoped-body-substitution-boundary`, then M5/M6 | Checked node, `EnvTyped`, correct child address, typed stack; no `badName`; typed returned value or cause | No target agreement. Add the semantic operation, certificate, pre/post and command clause first. |
| Region-boundary restoration | `scope-lifetime-finalization`, R11; `saved-mask-restoration`, consumed by the Queue wrapper and protected permit | Named entry and exit boundaries; both bits; nested regions; all completed exits; pending cause | No progress, fairness or cancellation-no-consumption promise. Correct F7's statements first. |
| Token transport through storage and fork | `store-typing` and `residual-program-typing`, R4; helper of the preceding two claims | Typed Ref/Deferred contents, typed captured environment, fixed saved bit; restoration acts on the invoking fiber | No generic retained-function claim. Complete membership and existing storage/capture connectors first. |

The second step reaches more than the executable checker.
`FiberOp` lives in `src/Effect4/Laws/Program/Sched.lean`.
`denoteFiberAction` lives in `src/Effect4/Laws/Program/DenoteR.lean`.
`FiberCert`, `fiberPre` and `fiberPost` live in `src/Effect4/Laws/Program/Typed/Residual.lean`.
The getter needs its answer relation and a preserving command clause beside `clause_getContext` in `Typed/Commands/Clauses/Answer.lean`.
The restore can reuse the existing mask operation, with the corrected body address.
These additions should connect to the existing M5/M6 consumers, without another program representation.

The three proposals are suitable directions after these contract corrections.
Their proof and generated-module acceptance remain open; the handwritten target probes do not close those obligations.

## Literal admission and the fold draft

`Term` has no type-ascription constructor in `Machine/Term.lean`.
`litArgTy` and `argTy` in `Program/Typing/Rules.lean` infer `bool` for every Boolean literal.
`Checker.check` preserves that answer type at `succeed`.
A record annotation still checks subtyping.
Therefore the proposed membership arm alone does not let a Boolean literal type as a saved token.
This inspection finds no source-literal forgery.

A distinct token image remains preferable for runtime separation.
It can carry one Boolean without carrying code or an allocation identity.
It distinguishes token values from ordinary Booleans after widening to `unknown`.
Its admission must require the canonical image, and its printer must select the corresponding closed function.
A tag alone does not prove provenance or restrict host reply admission.
The two closed choices are not security capabilities; any stronger introduction restriction needs its own exact claim.

The unfinished `fold-design/FoldModel.lean` has one relevant acceptance condition.
Its `sameHandle` evaluator accepts only raw `Store.Val.handle` values with matching kind bytes.
A generic rule over every `Ty.handle` would wrongly admit the proposed Boolean token and the existing encoded context.
Restrict the initial identity domain explicitly; the Queue's Deferred request identities suffice.
Neither that domain nor its law follows from sharing the type constructor `.handle`.

No new binder defect appears in the draft.
It appends accumulator then element, and its weakening shifts both levels through nested folds.
The corresponding insertion law must retain the tested premise `cut ≤ env.length`.
This reading does not assess its unfinished typing or proofs.

## Published fold follow-up at c49f2ba1

The committed fold note resolves the earlier identity-domain condition.
F4 admits only two `refOf` arguments or two `deferredOf` arguments, at any payload types.
It does not admit mask tokens or encoded contexts.
Do not report the unfinished-model concern as a defect in this published contract.

F1 and F6 state the two fold binders and their position inside an operation's term.
No new defect appears in this bounded reading.
The target connector must establish key equality exactly when the corresponding host objects have identical identity.
A stable mapping alone establishes only one direction.

This commit changes no decision row.
Its mask amendment adds `Fits` to the cost estimate.
It does not yet state target reservation, service membership or host-allocation exclusion.
The earlier acceptance conditions therefore remain, with the simple omission of `Fits` itself resolved.
