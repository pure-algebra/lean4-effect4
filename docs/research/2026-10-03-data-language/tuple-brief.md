# Tuple construction and static projection

Base: `f0b108db`, branch `codex/data-admission`.
The coordinator authorized this slice under decisions rows 159, 195 and 197.
The tracked maps-tuples brief at `d69a28da` fixes the contract.
This note places obligations before implementation; it reports no checked result.

## Contract and finishing criteria

Construction is the variadic, const-generic native atom `tuple`.
Its checked answer is `Ty.normalize (.tuple argumentTypes)`.
Evaluation returns `Val.list values` at every arity.
Append only `Term.tupleAt target index`; retain its exact natural index as data.
Its type rule normalizes the target, projects tuples and products, distributes over unions, and joins the answers.
Every remaining normalized tuple alternative must contain the requested position.
Explicit bottom answers bottom; lists, unknown types and out-of-range alternatives refuse.
The rule does not decide general inhabitance, so a tuple containing a bottom column can still refuse an out-of-range index.
Evaluation projects only a plain list frame, not a list-view snapshot.
Authoring resolves names with the existing `TermSrc` discipline.
No general row argument-spreading convention changes.

Done means both membership families prove actual evaluation and the existing progress and handle-containment consumers cover construction and projection with their old statements and premises.
Focused controls distinguish tuple arities, union bounds, literal columns, snapshots and list types.
The coordinator owns target expressions, generated outputs and integration gates.
Their completion is reported separately from this seat's checked source and proof evidence.

## Proof placement

| Obligation | Concept and required property | Claim and immediate consumer | Reach and limits | Requirement |
| --- | --- | --- | --- | --- |
| Tuple construction | Store Typing & Value Membership; typed evaluation | Helper of `denote-typed`; `NativeAtom.Sound`, `Typed.AtomFits`, `atom_progress` | Accepted arbitrary argument list with fitted values; produces the normalized exact tuple. No scheduler or host progress. | M5, R3 |
| Tuple projection and indexed membership | Store Typing & Value Membership; typed evaluation | Helper of `denote-typed`; `evalTerm_hasTy`, `evalTerm_isSome`, `evalTerm_progress` | Target admitted by the normalized projection rule; same world; exact bounds at every union alternative. No widening from lists or unknown. | M5, R3 |
| Raw handle containment | Residual Program Typing; typed straight meaning | Helper of `straight-meaning-typed`; `RawHandles.evalTerm_handles`, then `Denote.evalTerm_validIn`, `sound`, `meaning_typed` | Every successful raw evaluation, without a typing premise. No allocation, finalization or direct M7 conclusion. | R3 |
| Decoded key containment | Scope Lifetime & Finalization; reachable keys | Existing `nativeAtom_keys` and `evalTerm_keys` consumers used by Hooks/Layer | Successful raw evaluation retains only keys in inputs. This is separate from raw handles and cross-table validity. | R4 |
| Scope, weakening and signature congruence | Residual Program Typing; checker stability | Helpers of `denote-typed`; existing `argTy_weaken`, `argTy_ext` and scope consumers | Existing hypotheses and statements retained. Index is immutable metadata; only the child term is traversed. | M5, R1/R3 |
| Located typing refusal | Residual Program Typing; admission agrees with checker | Existing checker/refusal agreement; `Checker.explain` consumers | Diagnose only after `argTy` or `causeTy` fails; retain first failed child and separate cause path. No independent acceptance checker. | M5, R1/R3 |

Tuple construction reuses `ItemsFit`, `fits_tuple`, `fits_tuple_pair` and `fits_normalize`.
Projection helpers are introduced only for the named coarse/world consumers.
The structural target claim `collection-term-print-read` belongs to the coordinator's target slice.
Its existing scope-only premise must remain unchanged for every raw natural index.

## Files and stages

1. Source checkpoint: `Machine/Term.lean`, `Program/Eff.lean`, `Test/Program/TupleTerms.lean`.
   Append stored term constructors and atom rows; check these modules before requesting generated companions.
2. Checker and authoring: `Program/NativeAtom.lean`, `Program/Tuple.lean`, `Program/Typing/Rules.lean`, `Program/Typing/TermRefusal.lean`, `Program/Typing/Blame.lean`, `Program/Checker.lean` and `Program/Authoring/Tuples.lean`.
   Update `Program/Formation.lean` only if its generated traversal needs a case.
   Add focused tuple typing, handle, authoring and refusal fixtures.
   The diagnostic fold returns a record/tuple sum; old `locate` wrappers keep their record-only result types.
   Tuple packets retain an exact index, term path, reason and separate cause path.
   The rule `Tuple.project` remains the only projection acceptance owner.
3. Proof consumers: `Laws/Program/Typed.lean`, `Laws/Program/Typed/Membership.lean`, `Laws/Program/Typed/Denotation.lean`, `Laws/Program/Handles/Term.lean`, `Laws/Program/Signature.lean` and `Laws/Program/Authoring/Tuples.lean`.
   Add only the `Tuple.project` connector line to `Laws/Program/Folds/Ty.lean`.
   Update `Laws/Program/MeaningSound.lean` only if needed.
   A dedicated tuple value helper module belongs here only if it serves both proof families.
4. The coordinator regenerates AtomInventory, Fold, canonical Program, PreludeAtoms and reached mirror/binder outputs; owns all root imports, manifest entries, target files, decisions and case census.

Do not edit Codegen record/read/proof files, Schema files, root imports, generated files, manifests, the decision register or lake configuration.
Keep the preexisting `FormationContract.lean` draft unchanged and unstaged.
No stored tuple-construction constructor, second value representation, generalized substitution library or row-spreading API belongs to this slice.

## Verification commands

Use the shared Lean lane only after the coordinator grants it.
The source stage runs `LEAN_NUM_THREADS=3 lake build Effect4.Machine.Term Effect4.Program.Eff` and `lake env lean -DwarningAsError=true Test/Program/TupleTerms.lean`.
Later checks name the changed checker, authoring, proof modules and direct consumers only.
Focused fixtures query the new helpers and unchanged public theorem headers with `#print axioms`.
Accept only the existing ceiling `[propext, Quot.sound]`.
Each checkpoint runs `git diff --check` and commits explicit paths.
The receipt records exact commands, source/generated dependencies, axiom output, unchanged statements, open integration work and finite evidence.
No full sweep or push is authorized by this seat's brief.
