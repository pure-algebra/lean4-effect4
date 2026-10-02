# Ten-concept registry audit

The full registry is not ready to emit unchanged: fifteen selected declarations have incorrect qualified names, several citations name unrelated audit rows, and some roles/cuts misstate their purpose. Duplicate IDs, relation vocabulary, default module file existence, register IDs and decision-row existence pass the bounded source checks.

Snapshot `2026-10-02T02:18:37.282786+00:00`; main `d7b9cb113d6014f9439fb846bb79713ca73294e9`; parent worktree `cf71edc697948714ca491accf23d92aabe508329`. This is source reading, not a Lean environment or build result. Active implementation omissions below mean pending work, not failure.

Inventory: 10 concepts, 47 claims; pointer counts `{'witness': 39, 'absent': 4, 'goal': 3, 'refutedBy': 1}`. No duplicate concept/claim IDs or module defaults; every named default module has a source file.

## REG-1: Fifteen declaration names do not name their source declarations

Class: concrete runtime-resolution blocker.

The registry repeatedly uses module paths as declaration namespaces, and omits Env.Context, Provision or CloseIter namespace components. A fail-closed producer will refuse these entries. Existing source declarations supply the corrections below; this was checked by namespace/declaration source reading, not by loading Lean.

Minimal fix: Replace these fifteen pointers exactly as listed; let the producer validate the resulting environment references. Do not add aliases to make the incorrect names work.

Evidence: `docs/research/2026-10-01-semantics/gemini/registry-content.lean:219–240`; `docs/research/2026-10-01-semantics/gemini/registry-content.lean:282–303`; `docs/research/2026-10-01-semantics/gemini/registry-content.lean:353–388`; `docs/research/2026-10-01-semantics/gemini/registry-content.lean:408–412`.


| Registry line | Incorrect pointer | Correct pointer | Declaration source |
| --- | --- | --- | --- |
| 222 | `Effect4.Machine.Scope.close_idempotent` | `Effect4.Scope.close_idempotent` | `src/Effect4/Machine/Scope.lean:950` |
| 228 | `Effect4.Machine.Scope.close_twice` | `Effect4.Scope.close_twice` | `src/Effect4/Machine/Scope.lean:960` |
| 231 | `Effect4.Machine.Scope.closeOrder_eq` | `Effect4.Scope.closeOrder_eq` | `src/Effect4/Machine/Scope.lean:978` |
| 237 | `Effect4.Machine.Scope.close_reentrant_add` | `Effect4.Scope.close_reentrant_add` | `src/Effect4/Machine/Scope.lean:969` |
| 240 | `Test.Program.ProtocolPosts.closeSeq_protocol` | `Test.Program.ProtocolPosts.CloseIter.closeSeq_protocol` | `Test/Program/ProtocolPosts.lean:970` |
| 285 | `Effect4.Laws.Schema.Codec.decode_iff` | `Effect4.Schema.decode_iff` | `src/Effect4/Laws/Schema/Codec.lean:1052` |
| 291 | `Effect4.Laws.Schema.Codec.decode_encode` | `Effect4.Schema.decode_encode` | `src/Effect4/Laws/Schema/Codec.lean:1065` |
| 355 | `Effect4.Machine.satisfies_empty` | `Effect4.Machine.Env.Context.satisfies_empty` | `src/Effect4/Machine/Context.lean:149` |
| 361 | `Effect4.Machine.satisfies_single` | `Effect4.Machine.Env.Context.satisfies_single` | `src/Effect4/Machine/Context.lean:153` |
| 364 | `Effect4.Machine.satisfies_union` | `Effect4.Machine.Env.Context.satisfies_union` | `src/Effect4/Machine/Context.lean:164` |
| 367 | `Effect4.Machine.satisfies_weaken` | `Effect4.Machine.Env.Context.satisfies_weaken` | `src/Effect4/Machine/Context.lean:176` |
| 370 | `Effect4.Program.LayerTy.provide_discharges` | `Effect4.Program.Provision.LayerTy.provide_discharges` | `src/Effect4/Program/Provision.lean:87` |
| 376 | `Effect4.Program.LayerTy.provide_closed` | `Effect4.Program.Provision.LayerTy.provide_closed` | `src/Effect4/Program/Provision.lean:99` |
| 387 | `Effect4.Laws.Api.HostSession.reply_commute` | `Effect4.Api.HostSession.reply_commute` | `src/Effect4/Laws/Api/HostSession.lean:112` |
| 410 | `Effect4.Program.RuntimeR.run_eq_ref` | `Effect4.Program.Sched.run_eq_ref` | `src/Effect4/Laws/Program/RuntimeR.lean:211` |

## REG-2: Literature locators include unrelated and missing audit rows

Class: concrete citation defect / literature-validation blocker.

LynchVaandrager1995 is assigned audit P38 three times, but P38 is the TypeScript handbook. Leroy2009 is assigned P32, which is Rendel–Ostermann. PetricekOrchardMycroft2014 points to P43, while the audit paper table ends at P39; the verified coeffects row is C8. The same errors remain in the latest draft. Existing relation tokens themselves are valid, but a bibliographic row certifying title/venue does not establish an adapted result or definition in a claim.

Minimal fix: Use verified C4 for Lynch–Vaandrager, C10 for Leroy, C8 for 2014 coeffects; preserve each row's exact verification scope. Resolve work strings to the existing source index and record its source hash as the brief requires. Downgrade unsupported definitionUsed/adaptedResult claims to analogy or omit the link until a supporting passage is read; do not treat bibliographic existence as an adaptation proof.

Evidence: `docs/research/2026-10-01-semantics/gemini/registry-content.lean:252–263`; `docs/research/2026-10-01-semantics/gemini/registry-content.lean:353–357`; `docs/research/2026-10-01-semantics/gemini/registry-content.lean:381–418`; `docs/research/2026-10-01-semantics/citations-audit.md:344–351`; `docs/research/2026-10-01-semantics/citations-audit.md:360–366`; `docs/research/2026-10-01-semantics/gemini/semantics-v1.md:692–699`; `docs/research/2026-10-01-semantics/seat-B/brief-gemini-implementation.md:140–146`.

## REG-3: Canonical-forms labels contradict the adopted applicability guide

Class: concrete role-label defect, not a typing defect.

decode-encode, of-schema-schema, subn-refl, normalize-idem and satisfies-empty are all marked canonicalForms. They state codec retraction, reflexivity, normalization idempotence or empty-row satisfaction, rather than a value-shape theorem for a named typing judgment. The draft explicitly says codec retraction is a separate claim.

Minimal fix: Keep precise titles and assign the broad existing compatibility/fundamentalProperty role when appropriate. Reserve canonicalForms for actual shape statements such as membership inversion, or mark that standard role absent/not applicable with a reason. Do not inflate canonical-forms coverage with unrelated facts.

Evidence: `docs/research/2026-10-01-semantics/gemini/registry-content.lean:289–326`; `docs/research/2026-10-01-semantics/gemini/registry-content.lean:353–357`; `docs/research/2026-10-01-semantics/gemini/semantics-v1.md:107–118`; `src/Effect4/Laws/Schema/Codec.lean:1064–1067`; `src/Effect4/Machine/Context.lean:148–154`.

## REG-4: Planned record features are encoded as exclusions

Class: concrete applicability-model defect.

The registry adds cuts at rows 165 and 119 for positional record layouts and record/app constructors. The current spec explicitly says planned constructors at rows 119 and 165 are absent feature claims, not cuts. The data-wave design is ruled/planned, while the current Ty has no record constructor. Treating the feature as a cut removes future work from the obligation inventory.

Minimal fix: Remove those two cut entries; represent required record formation/layout work as absent claims tied to their decisions rows. Keep current no-record source facts in prose with the pending design link. Do not imply the named record layout is implemented today.

Evidence: `docs/research/2026-10-01-semantics/gemini/registry-content.lean:463–483`; `docs/research/2026-10-01-semantics/seat-B/spec-v3.md:325–328`; `docs/core/decisions.md:212–212`; `docs/research/2026-10-01-semantics/gemini/semantics-v1.md:485–488`.

## REG-5: The proposed tool registry imports runtime/Laws/Test roots directly

Class: concrete drop-in integration conflict; harmless if only data is extracted.

registry-content.lean imports Effect4, Effect4.Laws and two Test modules. The spec keeps the authored Tools registry import-Lean-only, with roots as Name data dynamically loaded by the driver. The file also redeclares every model type, so its contents cannot be appended verbatim to an existing registry module.

Minimal fix: Adopt the registry value and corrected first-order records in the parent-owned Tools module, keeping only import Lean. Preserve the three roots in Registry.roots for dynamic loading. Do not import Test into the Tools library or duplicate the model types.

Evidence: `docs/research/2026-10-01-semantics/gemini/registry-content.lean:1–5`; `docs/research/2026-10-01-semantics/gemini/registry-content.lean:25–84`; `docs/research/2026-10-01-semantics/seat-B/spec-v3.md:69–76`.


## Remaining original plan items

- **C1–C5: implement and wire the minimal report slice** — pending/in progress with parent; absence in snapshot is not a failure. Attribute/census and guarded fixture; root and trust-gate anchors; Lean-only registry, library and two thin drivers; close_typed/seq_typed tags; report JSON/Markdown; Effect Schema, refusal controls, pinned fixture, script/Makefile/generated-group wiring.

- **C6: integrate the ten-concept registry and make it pass the producer** — pending, concrete corrections listed above. Resolve every selected name, register id, source key and locator; derive printed statements/status/counts; compare the regenerated outputs and keep a receipt. CE-030 already exists, so the old missing-register-row blocker is resolved.

- **Required-obligation inventory and applicability coverage** — pending content completeness check. The current value has 47 claims, only 4 absent and 3 goal pointers. This is a finite selected inventory, not proof that all standard applicable roles/lemma lists have been accounted for. Compare it with the original lemma census, identify omitted required claims explicitly, and retain non-applicability reasons under cuts. Do not add arbitrary filler roles to make a rectangular table.

- **Draft source reconciliation, generated status ownership and authority promotion** — pending coordinator review/promotion; meaning sections and glossary exist as drafts. Replace handwritten theorem signatures/statuses with environment-derived statements and generated-table references; reconcile stale companions or label history; source-check glossary and definitions proposals, then promote docs/core/semantics.md and add authority links from system map, decisions and STATE. The current draft already adopts the authored-evidence boundary and stored-Eff/semantic-RProgram distinction.

- **Bibliography and literature receipt** — proposal exists; rendering and verified mapping pending. Generate one bibliography entry per referenced source key from existing source metadata. Avoid a second authored status/bibliography owner. Verify each locator and relation, keep partial verification/owner-copy bounds. A proposal alone does not show the producer renders the bibliography.

- **Checks and landing receipts** — pending runtime evidence, parent owns compiler lane. Narrow builds and import-extension/refusal controls; pinned tsgo 7 and decode controls; deterministic two-run bytes; check-semantics with committed outputs; base/head/files/commands/axiom/open-obligation receipt. Whole battery/trust gate/check-full remain owner-sweep work unless separately authorized.


The draft has already incorporated the first review's stored-syntax distinction, authored-evidence boundary, invariant/progress distinction and finite-fairness explanation. Those are resolved improvements; the remaining issues above concern the adopted registry and final ownership/verification.


Every finding and remaining-plan requirement has exact excerpts and SHA-256 hashes in `registry-audit.json`. No active tree was edited and no compiler was run.
