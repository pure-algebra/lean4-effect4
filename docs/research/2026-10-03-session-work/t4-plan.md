# Accepted successful replies to prepared value membership

Base: `4dfa15dacfb235d51bc2dece726a3e11959bb691` on `codex/session-work`. The coordinator approved this bounded continuation on 2026-10-03. Fence: `src/Effect4/Laws/Api/HostSession.lean`, `Test/Api/HostSessionContract.lean`, and this research directory. No runtime, root import, central registry or decision changes.

## Contract and consumer

A proof-only `PreparedSuccess s reply decision` records the actual keyed association selected by the session, the reply call ID, the returned answer decision, its currently parked external row/request, and the successful code actually returned by `prepareAsyncAnswer (interpOf program table)`. For the returned row, `shapeDecides row.answer = true` entails `Fits w result row.answer` for every world w. The shape premise is on the selected row, not every table entry.

`preflight_success_prepared_fits` establishes that contract from successful session preflight, a successful completion, and a non-stuck machine. Its proof composes `preflight_envelope`, the envelope's actual `admit` result, `external_prepared_answer_typed`, and `fits_of_hasTy_shapeDecides`. `submit_success_prepared_fits` consumes an actual successful receipt phase through `submit_conditions`. It keeps the preflight decision and prepared-success witness together.

## Placement before proof work

1. Concept 9, host boundary, serving its required `typed-replay-session` property and meeting concept 1 membership. This is a proposed `session-success-prepared-membership` contributor to T4, not the full host-answer claim.
2. Local ProofGraph goal `PreparedWanted.preflight_success_prepared_fits` in `Laws/Api/HostSession.lean` is declared before proof. Its consumer is `submit_success_prepared_fits`, exercised by a concrete accepted Scalar reply fixture.
3. Reach is exact actual preflight and receipt on any session with a non-stuck machine, only `.ofExit (.success value)` completions. Prepared typing uses the actual returned store's allocation table in the existing theorem, then shape-decided membership at any world. The returned witness keeps selected association, row and parked request explicit. Decisions 97–99, 117, 138–139 and 152 bound the claim.
4. No `AnswerOk`, `ExitOk`, token-world declaration, typed residual state, whole-session typing or T4 closure follows. Shape-decided types exclude handles, fibers, cells, deferred values, `unknown` and nested exits. Failures require an independent defect exclusion: actual admission accepts reserved defects that `ExitOk` excludes. No runtime profile is changed; a finite discriminator is retained in the research audit.
5. This serves R12 and the executable-admission boundary feeding M6. M5–M7's ghost admission premises are not silently discharged. Existing AnswerSchema decoding lemmas are reused conceptually rather than duplicated: this bridge concerns session acceptance and actual preparation, not Schema decoding.

## Done

The session laws and direct Run consumer build; the existing HostSession contract battery builds with a real successful prepared-membership example and refusal controls; the new laws stay within `[propext, Quot.sound]`; the reserved-failure discriminator is checked; the diff is clean. No full sweep and no main-worktree build.
