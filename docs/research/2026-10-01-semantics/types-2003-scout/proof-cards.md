# Gemini's next three proof cards

These are proposed statements, not completed theorems. They refine D2's group-4 plan at Gemini
`a8cc886697e173e28a7cf67eca0f49566164b0d8`, without changing the existing M5/M6/M7 order.
Use the current definitions when writing exact Lean signatures; the prose below is not an
alternative source of theorem statements. Paths and lines name that pinned checkout.

## 1. Reference read: expose and transport the declared type

**Result to establish.** First, membership in `NativeOp.refTy` exposes a cell key with
`RefDeclared w key .nat`. Then a reference declared at nat types the residual `refGet`
program returning its answer as a successful result with answer nat and error never.

**Existing premises and helpers.** `Equiv` and `RefDeclared` are owned by
`src/Effect4/Laws/Program/Typed/Membership.lean:33` and `:36`. Membership carries a declaration
at some type equivalent to nat by normalized subtyping, not necessarily syntactically nat.
`storePre` and `storePost` are at `src/Effect4/Laws/Program/Typed/Residual.lean:54` and `:94`;
`TypedProg.store` is at `:269`. Its continuation uses `leHost`, whose underlying world order
extends the reference table. The same pattern is used by `storePre_mono` at `:621`.
`fits_subN` (`Membership.lean:1262`) and `strongExit_success`
(`src/Effect4/Laws/Program/Typed/Admission.lean:173`) finish the reply.

**Argument.** Invert the handle membership in Membership. Retain the existentially declared
type and both subtyping directions. At each later world, preserve that declaration; identify
the reply postcondition's declaration by equality of the lookup. Transport the answer from its
declared type to nat, and use the residual pure-success constructor.

**Consumer.** The refGet branch of proposed `syncRow_typed`, then `syncPerform_arm`.
Do not include actual reference-store execution in this M5 card.

**Controls to retain at adoption.** A nat-declared cell passes. An undeclared cell and a
bool-declared cell fail admission. A type that normalizes to nat but is not written literally
as nat passes. Stop if the proof requires treating normalized equivalence as raw syntax equality.

**Theory link.** This is local store-typing/inversion and future-world continuation reasoning.
Ballarin's assumption discipline (`TYPES-B1`) helps factor it; Adams's logical-framework
conservativity (`TYPES-A1`) does not prove its world transport.

## 2. Service read: complete one whole denotation arm

**Result to establish.** Proposed `service_arm` types a positive-fuel `.service key` node at
its admitted point. Keep the exact node lookup, `PointTyped root w p ty`, and
`w.serviceTy = root.sig.serviceTy`.

**Existing premises and helpers.** Reuse `PointTyped.at_node`, `Eff.expandIn_of_round`,
`serviceTy_leHost`, and `getContext_typed` in
`src/Effect4/Laws/Program/Typed/Denotation.lean:698`, `:188`, `:248`, `:1047`;
checker inversion at `src/Effect4/Laws/Program/Typing/CheckInversion.lean:210`;
`seq_typed` at `src/Effect4/Laws/Program/Typed/Seq.lean:153`;
`fits_context_inv`, `ServicesFit`, and `flatFits_fits` in Membership at `:1467`, `:86`, `:270`.
The denotation's two lookup outcomes are at `src/Effect4/Laws/Program/DenoteR.lean:1062`.

**Argument.** Read the context through its typed protocol. When the service is present, its
membership follows from `ServicesFit`, and source/world table agreement identifies the expected
type. When absent, keep the currently admitted `missingService` defect; this does not produce
a successful service value or prove the dependency is present.

**Consumer.** The M5 constructor dispatch. Keep `provideService` and its restoration proof for
its own card; do not bundle that extra case into this one.

**Controls.** Present binding returns an admitted value; missing binding follows the documented
defect branch. Retain the service-table mismatch counterexample CE-022 when testing whether
agreement can be omitted. Stop if completion requires adding service presence or changing defect
admission. That would amend the judgment, not finish this proof.

**Theory link.** Reuse the current context-requirement and protocol semantics. `TYPES-B1` explains
why the agreement premise travels with the derived arm. It is not an independent result about
coeffects or host service availability.

## 3. Exit: finish the available non-inline connector

**Result to establish.** Proposed `exit_nonInline_arm` types positive-fuel `.exit b` with the
exact node lookup and point typing, the service-table tie, the lower-fuel child hypothesis
`ChildDenotes root f b (p.path ++ [0])`, and
`inlineYield b (p.child 0) = none`. Write the final signature against the actual point/fuel fields.

**Existing premises and helpers.** `expandIn_exit`, `pointTyped_child`, `ChildDenotes` and
`child_fuel_eq` in Denotation at `:127`, `:261`, `:826`, `:831`; checker inversion at
CheckInversion `:126`; the branch at DenoteR `:859`; `allGuard_typed` at Seq `:139`;
reified-exit membership in Membership `:178` and `ExitOk` in Admission `:32`.

**Argument.** The no-inline premise selects the ordinary guarded child denotation. Apply the
child hypothesis at its actual path and fuel. Reify either admitted child exit as a successful
exit value through `allGuard_typed` and the membership law.

**Consumer.** Proposed full `exit_arm`. The helper alone does not cover the inline branch.
`inlineYield_typed` is still owed; its perform cases depend on group-4 decoding progress
(DenoteR `:503`). A compiling non-inline helper must not close the full-arm or M5 goal.

**Controls.** Non-inline success and admitted failure both yield successful encoded exit values.
An inline body cannot satisfy the helper's no-inline premise. Keep this as a genuine branch
lemma, not a weakened replacement for the original claim.

**Theory link.** `TYPES-W1` motivates retaining this useful intermediate step while clearly
showing the missing justification for the other branch. It supplies no Effect4 exit theorem.

## Two tasks to remove from the proposed backlog

- **Term evaluation existence already has a theorem.** `evalTerm_progress`
  (`Denotation.lean:517`) assumes native atom typing and `FitsAll`; it concludes a returned value
  and its membership. `evalTerm_progress_env` (`:573`) adapts it to a source and `EnvTyped`.
  Gemini's new `termFits` at `Assembly.lean:1089` closes the separately stated adapter obligation.
  The earlier tentative existence gap is withdrawn; cite these three distinct interfaces.
- **The load connector's marker premise already has a helper.**
  `loadsTyped_of_denotesTyped` (`Assembly.lean:1201`) takes both denotation typing and `noMarker`.
  `raceRegistrationR_typed` (`Commands/Finish.lean:26`) proves no marker from `TypedProg`.
  Reuse the root typing construction in `Assembly.lean:1205–1216` after introducing the load
  premises, then apply that helper. `Finish` imports `Bookkeeping`, which imports `Assembly`:
  importing Finish back into Assembly would create a cycle. Place a later assembly adapter
  after both modules, or relocate this small lower-level fact with its callers and narrow checks.
  This is a placement/assembly issue; no new semantic axiom or load requirement is indicated.

## Verification at implementation

Each implemented slice uses its current pinned source, existing trust policy, named narrow
module/dependent checks, positive/refusing controls and printed axiom footprints. Publish its
short explanation alongside the exact generated statement and its actual consumer. Update a
ledger status only for the original proposition that was closed. This scouting pass did not run
these proposed proof controls or claim the three proposed signatures compile.
