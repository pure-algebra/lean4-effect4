# Context region entry checkpoint

The physical restoration repair remains a proposal in a temporary compiler copy.
Its finite cuts use the old runtime pin, not the integrated R2 runtime.
The production compiler and reference denotation stay unchanged.
The full M5 Denotation migration remains open.

Base: `0cbb2cf91`, branch `codex/symbolic-native-fold`.

## Placement

Concept: residual-program-typing; requirements R4 and R9.
Role: preservation dependency of `typed-state-reachable`.
Consumer: the existing ambient source induction and its closed M5 and Assembly claims.
Rows 117 and 349 and the approved success/failure service guarantees bound this work.
The original closed claim headers and unit contracts stay unchanged.

Concept: scope-lifetime-finalization; requirement R11.
Role: control for the approved context provider's shared region bracket.
Consumer: the provider source arm and the existing StackRegionRun/MaskBracket instance.
The physical context observation differs from context-write event agreement.
No public `Run.HistoryOf` derivation or outside implementation comparison is established here.

## Checked entry corrections

`ambientFiberPre` for `.scoped` uses `bodyRequires root.signature cert` inside the available row.
The actual source scoped operation creates and installs the Scope service for its child.
`.forkScoped` retains its full `cert.requires` inclusion.
The unit preconditions stay unchanged.

`ambient_suspendR_typed` and `ambient_constructR_typed` use the existing program arrow.
They retain the failure entry bound, future world and actual completed view.
The latter retains the existing completed-fiber exit membership premise.
Neither helper adds a program representation or evaluator.

Eight existing source arms pass together in a private source snapshot.
They are suspend, select, scoped, gen, iterate, uninterruptible, interruptible and catchCause.
Each uses the actual child certificate and required-row inclusion.
Each success/failure branch selects its actual guaranteed row.
Suspend and select use the callback's actual completed view.
CatchCause transports the caught cause and its handler child through the future world.

`SourceRegionMigration.wip.patch` retains their current source changes and the single Terms extraction.
The extraction keeps the existing declaration names and removes them from Denotation.
`SourceRegionArms.snapshot.lean` retains the exact checked private source snapshot.
The snapshot is checked evidence, not an exported second theorem family.
The complete Denotation module and its direct consumers still need migration and checking.

## Retained physical restoration control

`ProviderBracketCut.lean` checks the unchanged native compiler through the existing driver.
Its ordinary provider source passes source admission.
At command-prefix fuels six and seven, interruption records only the installed context write.
At fuel eight, interruption additionally records restoration of the previous context.
The reader uses context-write events because finished-fiber clearing resets its stored context.
These prefixes have no public history derivation in this receipt.

The raw budget source produces a yield at this interval.
Its reserved `maxOps` service has no declared native source carrier.
The checker and admission refuse it.
This raw witness is not an admitted source counterexample.

## Paired compiler and reference equations

The existing compiler equation for a non-identity update is:

```lean
updateThenK root update body (Val.context previous) =
  .onSuccess (.withFiber (.setCtx next)) (.bodyThen body previous)
contAOf root (.bodyThen body previous) value =
  .onExit (regionCode root body) (.restoreCtx previous) false
```

The proposed compiler equation is:

```lean
updateThenK root update body (Val.context previous) =
  .onExit (.onSuccess (.withFiber (.setCtx next)) (.bodyThen body previous))
    (.restoreCtx previous) false
contAOf root (.bodyThen body previous) value = regionCode root body
```

Both equations retain the existing context decoder, identity branch and bad-shape branch.
Here `next = Ctx.withServices (update.apply previous.services)`.
The candidate checks these equations and finite runs after applying only its retained temporary patch.
It uses the existing evaluator and driver.
It adds no IR, action constructor or private execution pass.

The corresponding old reference body is:

```lean
(guardR .onSuccess (fiberValR (.setContext next) rfl)).bind
  (seqR fun _ => onExitR body fun _ => fiberValR (.setContext previous) rfl)
```

The proposed reference body is:

```lean
onExitR
  ((guardR .onSuccess (fiberValR (.setContext next) rfl)).bind (seqR fun _ => body))
  (fun _ => fiberValR (.setContext previous) rfl)
```

The reference repair is proposed, not applied or proved in this checkpoint.
The pin's `internal/effect.ts` updateContext callback writes the context and returns the restoring frame in one callback.
The proposed ordering installs the frame before the native setter executes.
Interruption before that setter may therefore issue an extra restoring write.
This receipt makes no event-count or full runtime agreement claim.

The candidate checks pre-write cuts four, five and six, post-write cut seven and fuel eight.
Cut four has no context writes.
Cuts five and six write the previous context without installing the new service.
Cuts seven and eight record the installed service followed by the previous context.
Source admission is checked separately from these finite command prefixes.

## Affected statement inventory before production

| Path | Required migration |
| --- | --- |
| `src/Effect4/Program/Compile.lean` | `updateThenK`, the `contAOf` bodyThen arm and its existing name payload |
| `src/Effect4/Laws/Program/DenoteR.lean` | `updateContextR` restoring-frame order |
| `src/Effect4/Laws/Program/Agreement.lean` | `contAOf_bodyThen`, `updateThenK_context` and dependent agreement equations |
| `src/Effect4/Laws/Program/Intro/Region.lean` | the existing update/body continuation CodeMeans producer |
| `src/Effect4/Laws/Program/Typed/Context.lean` | the existing provider ambient reference proof |
| `src/Effect4/Laws/Program/Handles/Alphabet.lean` | existing bodyThen support if its payload changes |
| `src/Effect4/Laws/Program/Handles/Layer.lean` | `updateThenK_keys` |
| `src/Effect4/Laws/Program/Handles/Hooks.lean` | existing bodyThen and updateThen producer cases |
| `src/Effect4/Laws/Program/NativeCallbacks.lean` | existing native callback source transport |
| `src/Effect4/Laws/Program/SourceOpportunityCallbacks.lean` | existing callback source weights |
| `src/Effect4/Laws/Program/Guard/RaceSites.lean` | existing compiler producer equation |
| `src/Effect4/Laws/Program/ReleaseCustody/Evaluation.lean` | existing update continuation credit bound |

The existing bodyThen continuation carries the program/body region already.
No suitable existing pure region continuation avoids its previous-context payload.
Production may remove that field from bodyThen instead of retaining an unused duplicate.
That constructor-domain migration reaches its support and weight patterns.
The previous context then lives once in the restoring finalizer.
The temporary candidate keeps the existing constructor signature to isolate the order repair.
No production mutation follows from this finite probe alone.

## Checks and open work

One direct Lean process runs at a time with one thread and warnings as errors.
A copy-on-write artifact overlay avoids a broad dependency cascade.
The candidate overlay replaces only Compile before running its retained finite probe.
The ordinary overlay checks Residual, Context and the eight source arms in dependency order.
Full Denotation, Assembly preservation and public provider history remain open.
No behavior gate or whole-library build runs in this proof/research checkpoint.

Residual passes in 12.19 seconds.
Context passes in 5.78 seconds.
Scheduler passes in 23.97 seconds.
The eight source arms pass in 8.53 seconds.
The unchanged provider control passes in 14.57 seconds.
The combined original-artifact audit passes in 97.51 seconds under concurrent host pressure.
It reports 1,053 declarations within `[propext, Quot.sound]`, zero planned goals and zero modulo declarations.
The audit imports Scheduler, Terms, the eight source arms and the unchanged provider control.
It audits Contracts, Residual, Seq, Context, Scheduler, Terms and both retained evidence modules.

The temporary candidate compiler passes in 14.14 seconds.
The candidate's final symbolic equations and finite controls pass in 5.54 seconds.
Its first survey fails only on an obsolete direct RunFiber stack projection.
The corrected survey uses the physical context projection and passes in 4.61 seconds.
A separate candidate-artifact audit waits for the coordinator's build slot.
The candidate remains proposed research evidence.

Logs: `/private/tmp/context-region-{scheduler,audit}.log`, `/private/tmp/context-source-region-arms.log`, `/private/tmp/context-provider-baseline.log`.
Candidate logs: `/private/tmp/provider-candidate-{compile,survey,check}.log`.
Apply `ProviderBracketCandidate.patch` to a temporary compiler source copy before checking its candidate evidence.
Compile that copy into a copy-on-write artifact overlay.
Use the existing driver and the actual `evaluatorFor` instance from that temporary output.
The baseline evidence uses the unchanged compiler in a separate overlay.
No old compiler laws from the baseline serve as candidate agreement evidence.

## Runtime pin boundary

The finite baseline and candidate use this worktree's existing checked runtime artifacts.
The Fibers source last changes at `d6ac567a1` in this branch.
Its SHA-256 is `79985b80f758c7c29af6c9b54f34afb826a5da1fac4c01dd6ed8b5378ab9220c`.
The artifact overlay copies that worktree's Fibers output, dated October 11 at 00:56.
All finite fuel numbers in this receipt apply only at that old runtime pin.

The coordinator's `6eb40cccd` checkpoint has the later R2 and machine-field changes.
Its Fibers source SHA-256 is `090844e028492f04809d292eff691628ec8ac01dfd67b6d12050e67cb56f97fa`.
This receipt does not certify that checkpoint's provider behavior.
The compiler ordering equations still show the separate setter and restoring-frame construction.
Their structural gap motivates the proposed repair but establishes no current-root execution result.
Rerun the controls against the integrated context/R2/field checkpoint before production compiler changes.
The candidate's separate audit and that rerun wait for the coordinator's build slot.
