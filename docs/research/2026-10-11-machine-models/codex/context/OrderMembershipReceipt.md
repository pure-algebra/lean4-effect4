# Context order and membership checkpoint

The source/type proofs compile and pass the axiom audit.
The full typed getter still needs ambient service coverage in its existing relation.
This checkpoint does not claim that key presence proves service-value membership.

Base: `95ae53aa3` on `codex/symbolic-native-fold`.
The commit containing this receipt supplies the head.
The source constructor checkpoint remains `0dcebf98c`.
The ratified source ruling is decisions row 349, option A.

## Placement

Concept: `subtyping-algebra` and `initial-algebras-folds`.
Question: `sub-antisymm-canonical`, typed membership preservation, and `annotate-table`.
Proof role: the generated payload rules serve `TypeAlgebra`, `Admits` and `Typed.Membership`.
The source typing cases serve the existing checker and annotation agreement claims.
Requirements: R14 and R4.
Reach: canonical context key rows, declared service carriers, and the existing source denotation route.
No execution progress, whole-machine preservation or outside target agreement follows.

## Changes

`Ty.sameHead` retains exact payload equality.
The existing View producer adds the declared context payload order.
`payload-orders.json` names the row relation and its checked companion laws.
The manifest records the new input.
The generated Type view alone gains this payload family.

Three decomposition helpers add a payload-rule-false premise.
They are `sub_eq_false_of_not_sameHead`, `sub_eq_args`, and `sub_eq_leafRule_of_not_sameHead`.
The old helpers covered ordinary child comparison but omitted ordered payloads.
The outward subtype order, canonical antisymmetry and membership weakening claims retain their statements.
No frozen contract pins the changed helper case lists in the searched contract/register paths.

`Fits` at `contextOf` requires coverage, service declarations, matching values and live handles.
`fits_map` now requires equality of service tables.
Its former backward-only premise allowed a promised service declaration to disappear.
`fits_restrict` adds retention of the world's service declarations.
The weaker internal `ServicesFit` transport remains available where its local premise suffices.
World order and `Grows` already retain service-table equality.

The fresh membership helpers add actual service realizability.
Each service has a declared carrier, a fitting value and live handles.
`Grows.services` transports that premise.
The existential `inhabited_iff_fits` statement remains unchanged.
Its witness world declares unit services and supplies actual unit values.
That witness proves existential membership, not an admitted source world or execution progress.

Source typing, checker agreement, annotation and replacement gain the approved constructor cases.
The provider child retains the variable environment and binds no value.
Annotation visits that child, as it visits a service provider's child.
The parent still refuses an invalid provider term.
The provider's denotation and compiler agreement reuse the existing context update and restoration route.
`Val.context?_keys` moves unchanged from `Handles.Layer` to `Handles.Alphabet` for shared reuse.
No new machine-helper census or program carrier lands.

## Verification

`LEAN_NUM_THREADS=3 lake env lean --run tools/Effect4Gen/Driver.lean --group TyView`
regenerates the declared Type view through the existing producer.

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typing.Restrict Effect4.Laws.Program.Typed.Admission Effect4.Laws.Program.Intro Effect4.Codegen.Templates`
passes with 478 jobs.
The final changed Restrict module builds in 17 seconds.
Earlier checks report Membership in 5 seconds and Admission in 1.5 seconds.
The changed annotation and replacement modules build in 25 and 12 seconds.
The child-environment splice dependency builds in 34 seconds.
These are module timings, not a total runtime claim.

`LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/OrderMembershipAudit.lean`
reports 8,920 declarations within `[propext, Quot.sound]`.
It reports zero declarations modulo planned goals and zero planned goals.
The audit names all 32 changed source modules.

`MembershipBoundary.lean` checks the unchanged existential inhabitance reader.
It retains missing-service and dropping-service controls.
It retains the empty native context boundary for a promised nonempty row.
`ValueBoundary.lean` retains the separate presence-only shape check and closed-source refusals.
`git diff --check` reports no errors.
No behaviour gates run in this slice.

## Remaining work

`Typed.Residual.fiberPre` fixes the native getter certificate at coarse `Ty.context`.
Its postcondition cannot establish a promised nonempty `contextOf` row from an empty context.
`RunFiberOk` currently supplies typed live services without promised-key coverage.
The next slice extends that existing ambient relation and getter certificate.
Its source consumer is the new context reader arm in `Typed.Denotation`.
The provider arm must transport the supplied coverage through the existing context region.
The shared StackRegion/MaskBracket instance remains the restoration proof owner.

The central owner keeps the two-line `Codegen.Types` refusal patch outside this commit.
Its narrow build passes in 862 milliseconds.
A signature-aware target projection, caller threading and target migrations remain open.
TypeScript ingest, LCNF, OCaml and outside behaviour gates remain deferred.
Root imports, Makefile derived-input hooks and registries remain coordinator-owned.

## Changed files

- `src/Effect4/Codegen/Templates.lean`
- `src/Effect4/Laws/Program/Admits.lean`
- `src/Effect4/Laws/Program/Agreement.lean`
- `src/Effect4/Laws/Program/Bounds.lean`
- `src/Effect4/Laws/Program/Definitions.lean`
- `src/Effect4/Laws/Program/DenoteB.lean`
- `src/Effect4/Laws/Program/DenoteR.lean`
- `src/Effect4/Laws/Program/Eliminators.lean`
- `src/Effect4/Laws/Program/Handles/Alphabet.lean`
- `src/Effect4/Laws/Program/Handles/Compile.lean`
- `src/Effect4/Laws/Program/Handles/Layer.lean`
- `src/Effect4/Laws/Program/Intro.lean`
- `src/Effect4/Laws/Program/Intro/Identity.lean`
- `src/Effect4/Laws/Program/Intro/Scope.lean`
- `src/Effect4/Laws/Program/Polarity.lean`
- `src/Effect4/Laws/Program/Signature.lean`
- `src/Effect4/Laws/Program/Template.lean`
- `src/Effect4/Laws/Program/TyView.lean`
- `src/Effect4/Laws/Program/TypeAlgebra.lean`
- `src/Effect4/Laws/Program/Typed/Admission.lean`
- `src/Effect4/Laws/Program/Typed/Membership.lean`
- `src/Effect4/Laws/Program/Typing/Annotate.lean`
- `src/Effect4/Laws/Program/Typing/CheckInversion.lean`
- `src/Effect4/Laws/Program/Typing/CheckSound.lean`
- `src/Effect4/Laws/Program/Typing/HasTy.lean`
- `src/Effect4/Laws/Program/Typing/Replace.lean`
- `src/Effect4/Laws/Program/Typing/Restrict.lean`
- `src/Effect4/Laws/Program/Typing/Splice.lean`
- `src/Effect4/Program/Ty.lean`
- `src/Effect4/Program/TyClasses.lean`
- `src/Effect4/Program/Typing/Annotate.lean`
- `src/Effect4/Program/Typing/Focus.lean`
- `tools/Effect4Gen/View.lean`
- `tools/Effect4Gen/guards/tyview.lean`
- `tools/Effect4Gen/manifest.json`
- `tools/Effect4Gen/payload-orders.json`
