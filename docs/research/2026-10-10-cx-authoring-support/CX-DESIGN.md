# CX design recommendations

## The selected direction

Support option (e): a reference may cross lexical owners only when its expanded target reads no incoming program parameter.
The owner selects this direction in Claude's repository session at `2026-10-10T14:31:02.543Z`.
The owner also selects per-call layers as the following capability.
The tracked authority at reviewed HEAD does not yet contain that amendment.
This packet supplies design support; the coordinator records the ruling when landing it.

Two addresses share a lexical owner when they belong to the same definition body or the same main program.
Their parameter declarations alone do not identify that owner.
`scopeParams` in `src/Effect4/Laws/Program/Typed/Scope.lean` currently returns declarations, not an owner identity.
The equal-declaration control in [CXControls.lean](CXControls.lean) distinguishes these policies.

Keep option (a)'s controls as evidence of the restriction it would impose.
The closed-layer example in [LayerContextControls.lean](LayerContextControls.lean) needs no caller parameter.
Option (e) should keep it while refusing the retained failure and equal-declaration dynamic-scope controls.
A source search finding no current caller does not establish backward compatibility for external stored programs.

A target is closed here only with respect to incoming program parameters.
It can still require services, call a host, allocate state, fail, or register cleanup.
Do not label it pure, globally constant, or safe to merge by content.

### Derive the parameter dependency once

Read the expanded target with the existing generated fold family.
Include invocation arguments, forks, loop bodies, finalizers, statements, and programs inside nested layers.
A raw reference contains no parameter node, so scanning its surface is insufficient.
Use one dependency result for source admission, the checker agreement law, and the editor's explanation.

`readsAlg` and `cata_layer_congr_on` in `src/Effect4/Laws/Program/Signature.lean` already express agreement on a subtree's reads.
`check_alg_agreeOn` specializes that structure to the checker under a signature extension.
Extend or specialize that connection for signatures differing only in program parameters.
Do not copy the checker's constructor cases into a separate closure checker.

A closed target may invoke a definition whose own body uses its own parameters.
The invocation establishes that new context; its supplied arguments must ignore the incoming context.
A plain call admits only a definition with no program parameters.
See `Signature.withDefs` in `src/Effect4/Program/Definitions.lean`.
Thus incoming-parameter independence does not require expanding every called body.
The surrounding definition block and all its references must still pass program admission.

### The proof interface needs one additional connection

Checker independence does not establish the current `LayerPointTyped` predicate after a cross-owner redirect.
`StackTyped` requires every declaration at the target's lexical owner, including unused parameters.
A closed target can therefore fail that proof premise despite never inspecting the incoming stack.
This is a proof-interface gap, separate from the retained runtime counterexample.

Introduce a shared closed-subtree typing mode for points and captured argument sites, or an equally precise active-context relation.
Its base signature types the expanded subtree, and its dependency witness excludes incoming parameter reads.
It keeps the runtime stack as data without asserting that unrelated incoming entries inhabit unused target declarations.
The lexical mode retains today's full stack obligation for code that can read parameters.

Transport the witness through children, capture, fork, loop, finalizer, invocation arguments, and reference expansion.
An invocation changes to the callee's checked lexical context.
A parameter return uses its argument site's captured mode, values, and parent stack.
Do not repair the mismatch by erasing captures or weakening every point's stack predicate.

### Source admission and explanation

`Eff.layerRefsWF` in `src/Effect4/Program/Refs.lean` currently checks target order, kind, and containment.
Strengthen that existing predicate with same-owner or closed-expanded-target source admission.
For equal owners, derive equal parameter declarations and reuse `layerPointTyped_redirect`.
For different owners, use checker independence and the closed-subtree typing connection.

Unlike option (a), option (e) does not make every cross-scope branch contradictory.
`crossScopeRef_builds` still needs a positive proof for permitted closed targets.
Its current hypothesis must carry the stronger formation rule through `SourceWF.refs`.
Changing only the public program admission wrapper leaves the old planned statement false.

The written statement may stay, but its accepted domain narrows through that predicate.
Record the amendment beside the retained counterexample and the owner ruling.
Do not claim a proof of the previously false proposition over its old domain.

The source admission explanation must identify the reference site and target owner.
The current `referencesIllFormed` answer at the root loses this useful information.
Have one reference-check result drive both the Boolean predicate and the located explanation.
Its extra diagnostic must not introduce a second acceptance rule.

### One shared scope reader

Share lexical ownership and parameter lookup through a small core reader.
Keep its laws in `Effect4.Laws`.
The core reader cannot import `Laws/Program/Typed/Scope.lean`.

Proposed placement is a leaf beside `src/Effect4/Program/Refs.lean`.
It reads the existing root definition block and an address.
It returns a derived view: owner, body base, and parameter declarations.
It stores no additional program tree and no runtime type environment.

`Part.bodyAt` and `Eff.partAt` in `src/Effect4/Program/Typing/Parts.lean` already implement the relevant body-spine interpretation.
Connect their results to the shared reader before moving their callers.
Keep invalid addresses and declaration/body mismatches explicit.
Do not force `Refs.lean` to import the typing graph and introduce an import cycle.

Consumers are source admission, typed points, definition-body focus, and the editor's parameter display.
This consolidates one source of scope information instead of introducing another checker.

### Proof boundary

M7 remains a claim on `M7Fragment` in `src/Effect4/Laws/Program/Typed/Assembly.lean`.
Its premises include a lawful checked source, an empty row table, an empty requirement row, and an answer-free tape.
It does not become a guarantee for every admitted host session.
`M7NoHalt` excludes the machine's stuck state. It does not establish termination or host progress.
The measured dependency results are in [cx-audit.log](cx-audit.log).

## Keep memo identity separate

The nested-invocation control declares one definition and contains no layer reference.
Its outer invocation supplies a program returning `1`; its inner invocation supplies a program returning `2`.
The ordinary run returns `1` because the inner build reuses the outer build at the same source path.
Explicit freshness and a local memo map each return `2` in this finite control.

Both strict visibility and closed-target source admission accept this example.
Its values fit the same declared type, so it establishes no additional typing failure.
It shows that source visibility and construction identity are different decisions.

`Point` argument sites retain captures, but an invocation allocates no layer identity.
See `suspendBodyAt` in `src/Effect4/Program/Compile.lean`.
`memoize_typed` in `src/Effect4/Laws/Program/Typed/LayerArm.lean` uses the point's path for memo lookup and allocation.

Pinned Effect constructs a layer object on each constructor call.
`fromBuildUnsafe`, `fromBuildMemo`, and `MemoMapImpl.get` provide the source evidence in `vendor/effect-4.0.0-rc.112/src/Layer.ts`.
No Effect execution was run for this packet.
`printDef` in `src/Effect4/Codegen/Print.lean` already refuses layers inside definitions because these identities differ.
This packet identifies no newly broken supported TypeScript printer claim.

Follow the selected direction: layers constructed inside a reusable definition receive identity for that invocation.
Retain deliberate sharing of separately declared dependencies.
A lexical owner and a runtime invocation identity must remain distinct data.
Record the precise representation and DB-12/DI-71 amendment before implementing that slice.

Do not key a layer by argument equality or an argument hash.
Equal arguments need not imply shared allocation or shared cleanup.
Do not automatically make the entire invocation fresh.
That can also disable intended sharing of dependencies supplied from outside it.

Keep the current printing refusal until the ownership relation has an agreement theorem.
The existing `.fresh` operation remains an explicit restricted control, not the general ownership proof.
`fresh_never_shares` in `src/Effect4/Laws/Program/LayerSharing.lean` requires map-routed operations.
Its scope excludes an independently selected ambient provision map.

## CX3: certify construction before raw expansion

Prioritize the CX3 design for the module-authoring goal.
Use the existing captured-program execution for the first certificate.
Raw program syntax expansion is a separate transformation with additional premises.

`Def.of`, `Params`, and `Defined` in `src/Effect4/Program/Authoring/Defs.lean` already avoid repeating an ordinary operation.
Extend that interface and `eff_module` in `src/Effect4/Program/Authoring/Module.lean`.
Do not add a parallel module builder or a second stored context syntax.

One descriptor should retain ordinary request arguments, program-parameter declarations, and the body's declared columns.
Derive these products from it:

- the `DefDecl` and its `ParamDecl` list;
- names and types shown for each program parameter;
- argument children of `Eff.invoke` and parameter calls in its body;
- arity checks and located refusals;
- print/read metadata when HO-3 admits the program form.

The certificate belongs to shared authoring operations and their composition.
An author using those operations should receive it by composition.
An arbitrary Lean `Src` function can inspect supplied syntax, so one application to a generic hole does not certify it.
Retain an explicit certificate boundary for such builders.

### Three operations, three contracts

| Operation | Existing or proposed contract | Important boundary |
| --- | --- | --- |
| Fill a Sketch address | Existing checked replacement at that focus's signature, environment, and exact type | One occurrence, with the surrounding context already fixed |
| Instantiate a program parameter | CX3: supplied programs admitted at declared bounds, executed with captured caller values and caller parameters | Potentially many uses and different supplied requests |
| Inline a call as raw syntax | Restricted transformation after capture, declared bounds, and identity are handled | Changes where syntax stands and how inference sees it |

`Sketch.sigAt` and `focusAt` in `src/Effect4/Program/Sketch.lean` already support editing inside definition bodies.
That feature need not wait for CX3.

### Checked control: a capture crosses a closed layer edge

The caller binds `41` and passes a program that reads that value.
The definition runs the program inside a layer and returns the service value.
The existing call is admitted and returns `41`.
Raw insertion of the variable into that layer is refused because the layer's value environment is empty.

See `captured` and `rawCaptured` in [CX3Controls.lean](CX3Controls.lean).
This follows the distinct roles of value environments and program-parameter captures.
Binder shifting alone cannot move a value into an environment that the language deliberately closes.

The first CX3 contract should interpret supplied programs through existing sites and environments.
A later raw expansion must materialize captures lawfully or refuse that case.
It must also keep the caller's parameter scope inside inserted clients.

### Checked control: a narrower answer changes allocation typing

A parameter declares `list nat`, and its body allocates a reference from the returned list.
An empty list fits the parameter, so the invocation is admitted at `refOf (list nat)`.
Raw insertion makes allocation infer `refOf (list never)`.
That reference type is not below the declared reference type because reference columns are invariant.

The checked value ascription from `src/Effect4/Program/Authoring/Ascribe.lean` restores this finite allocation's declared answer.
It adds no constructor or unchecked cast.
See `referenceCall`, `rawReferenceBody`, and `ascribedReferenceBody` in [CX3Controls.lean](CX3Controls.lean).

Thus declared argument bounds alone do not justify unrestricted raw re-inference after filling.
Keep the declared parameter result at each use, or prove the restricted context accepts the narrower inference.
Also state error-column and requirement transport. The successful value-ascription control establishes neither generally.

## CX4: transfer behavior under a named observation

Use CX3's certified interpretation in the unfolding statement.
Name the related environments, decisions, and budgets.
An invocation adds administrative suspensions, so equal numeric fuel is not the default contract.

Keep unfinished computations as frontiers.
Keep state produced before failure available to cleanup.
Do not infer continuation equality from equal pending requests and stores.
A waiting observation describes a present stop, not every future reply's result.

Start with a fragment that excludes disputed layer construction identity.
Transfer an existing Pool or Semaphore law only after matching its observation and premises.
A module's typing certificate does not itself transfer its behavioral laws.

## S1 remains an independent line

S1 introduces the meaning of sequential scopes and resource cleanup.
It follows the host-meaning packet's Q11/Q12 and consumes L4's precise waiting observation.
It need not wait for CX3 or the layer identity decision when its fragment excludes definitions and layers.

Its meaning must retain the original exit, changed stores, captures, registration identities, interruptibility masks, and cleanup progress.
A scope marked closed may still have cleanup running or waiting.
The local close theorems do not already establish whole-session resource agreement.

Give CX3 the first design slot for authoring reuse.
S1 can receive an independent design review in parallel.
Neither should reopen another program representation or silently widen L4's fragment.
