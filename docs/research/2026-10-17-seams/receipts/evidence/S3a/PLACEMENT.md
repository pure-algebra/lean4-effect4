# S3a placement before proof

This placement precedes the source and proof drafts.
The actual source drafts now implement the named consumers under overlay/src.
The theory proposal extends host-session-protocol with the tool-transition property in interfaces.md version 2 §7.
The canonical action fold serves both accepted replay and request handling.
It is not a second program interpreter or another document representation.

| Obligation | Concept/property | Registry question and role | Reach and hypotheses | Exclusions | Consumer/requirement |
| --- | --- | --- | --- | --- | --- |
| serve_appends | host-session-protocol; tool transitions | proposed tool-serve-appends, characterization | certified Oracle, sealed State, any accepted Action; accepted no-op/mixed AddOutcome/refused run phase included | no native closure or IO claim | ST4 apply_commits_once, transcript persistence; R6/R13 |
| serve_refuses | same | proposed tool-serve-refuses, preservation | certified Oracle, sealed State, any refused Request; complete State equality | no rollback of external effects or native mutation | ST4 apply_refuses; R6 |
| serve_query | same | proposed tool-serve-query, preservation | every Query, dry and discover included; complete State equality | no effectful host query execution | wire queries and ST4 read-only load; R6 |
| serve_transparent | same; Oracle transparency | proposed tool-serve-transparent, compatibility | full planned function equality serve o = serve uncached, including Checked.trace | no modeled runtime costs or arbitrary native callback | memo transparency loop and request handling; R6 |
| transcript_replays | same; accepted-action replay | proposed tool-transcript-replays, characterization | every sealed State; uncached canonical replay from Raw.empty equals its Raw | no replay of another host's effects, no IO restart theorem | ST4 load_own; R6/R13 |
| play refusal inertness | same; helper of tool-serve-refuses | helper, no separate top-level claim | finite list of Run.Event, unresolved selector at index; temporary live prefix discarded | refused phases inside successful events do not refuse action | serve_refuses and loop5 rollback; R6 |
| serve_answers | same; semantic replies | S3b-owned proposed tool-serve-answers | generated RespondsTo pairing for request/reply | no JSON decoder exactness by this statement | S3b wire owner; R6 |

The exact statements serve_appends/serve_refuses/serve_query already elaborate in the version-2 probe.
Keep their complete observations when placing the concrete State instance.
The registered pointer must be the same planned goal later replaced in place, if a proof remains open.
Any planned goal stays in Laws; the Effect4 core root reaches none.
The coordinator owns semantics.md, Registry.lean, and root imports for these placements.

## Superseded scout ruling: transparency observation

The coordinator confirms semantic State/Reply equality as the transparency observation.
A memo-hit control must retain unequal trace/cost while the semantic answer stays equal.
That red control rejects full Checked equality as an overstatement.
The State/Reply observation retains run phases, accepted log, document/fill/session identity, and every exposed semantic field.
The exact planned serve_answers/serve_appends/serve_query/serve_refuses statements remain unchanged.
The literal shorthand serve o = serve uncached in the interface table needs this explicit observation when registered.

## Coordinator ruling: suggestion refusal

Append Tool.Refusal.suggest (why : FeedRefusal) as the minimal accurate protocol correction.
The existing DocRefusal.feed requires a commit-item index; suggestPage supplies none.
Using that wrapper would manufacture an item index and misstate the source failure.
Retain this indexed-wrapper counterexample beside the below-root noFocus control.
Add a positive typed-root suggestion control with its genuine candidate module key.
Add a Tool-level noFocus query refusal control with complete State equality.
S3b must include the new constructor in generated codecs and unknown-tag refusal controls.
Preserve every previously declared protocol tag; no existing tag is renumbered.

## Source correction: semantic traces do not record cost

The earlier unequal-Checked-trace red-control instruction cannot hold in the current S0/V1 model.
Oracle.eq_uncached proves oracle equality; Oracle.transparent quantifies every function of an oracle.
Checked.Trace is List (CheckInput × Verdict), without cache-hit or cost metadata.
The same computation therefore has equal Checked.trace under certified oracles.
V1's owner confirms this and deliberately removes fromCache flags.
The coordinator receives this correction before any impossible red control is implemented.
Retain semantic State/Reply as the protocol observation and every exposed semantic field.
Any checker-invocation or runtime-work difference needs separate finite host instrumentation.
No Checked.trace inequality, runtime-work theorem, or performance bound is claimed here.

## Final coordinator ruling: preserve full planned transparency

The earlier proposal to narrow serve_transparent to State/Reply equality is withdrawn.
The current Oracle.eq_uncached and Oracle.transparent support the full planned statement serve o = serve uncached.
This equality retains the complete Checked result, including its semantic query/verdict trace.
State, Reply, run phases, accepted history, identities, and every exposed semantic field stay intact.
Operational cost is absent from Checked.Trace and from this equality's observation.
No unequal-trace Lean control is implemented. Separate finite host diagnostics may count work.

Source declaration evidence, production and V1 Check.lean:

```lean
structure Oracle where
  ask : CheckInput → Verdict
  agrees : ∀ i, ask i = run i

theorem Oracle.eq_uncached (o : Oracle) : o = Oracle.uncached

theorem Oracle.transparent {α : Sort _} (f : Oracle → α) (o : Oracle) :
  f o = f Oracle.uncached

abbrev Trace := List (CheckInput × Verdict)
```

Specialize Oracle.transparent with f := fun o => serve o for the planned full function equality.
The exact planned serve_answers/serve_appends/serve_query/serve_refuses statements remain unchanged.

## Protocol package sealing

The coordinator requires whole Doc and State sealing at actual protocol export roots wherever reachable.
S1 adds no speculative native Doc export wrapper; roots.json currently exports no Doc/SourceDocument root.
S3a/S3b must supply the real protocol consumer, initial State factory, and serve roots.
The native positive uses that real consumer; hostile complete Doc/State representation clients must refuse compilation.
Preserve declared tags and add generated-codec/unknown-tag controls for Refusal.suggest.
The S4 api_gen Built public-alias seal remains separately mandatory.

A hostile representation fixture must contain every runtime field from the fresh inferred interface.
Retain a positive unsealed-interface compilation control when establishing that the later refusal is package abstraction.
The S4 incomplete-Built fixture shows why a missing-field error alone proves no seal.
No unsafe cast or manufactured proof callback belongs in these ordinary typed clients.

## Candidate evidence correction

The planned Candidate.fit cannot represent CheckCache.Evidence.differentEnv.
The actual Candidate retains program, sourcePath, key, and the complete Evidence sum.
The owner accepts this correction before implementation.
The codec preserves the Evidence constructor tags and both lexical environments.
No checker ask, context key, or FeedRefusal is fabricated.
A finite control must use the actual suggestOne producer with distinct source and target environments.

## Preview and inspection corrections

The owner requires the existing preview computations and their actual observations.
PreviewAnswer retains Tree.Outcome tape state for settle and frames, and Tree.Path for explore.
The dispatcher calls the existing Preview and Kit definitions.
No Tree outcome is converted into a fabricated Live.View.

DocView.inspection retains path, expected program, context, focus, table entry, and located refusal.
The producer follows the frozen S1 inspect branch.
A missing address or nonprogram node refuses noProgram at the supplied address.
A whole-document query carries no inspection.
The owner approves place PlaceRefusal because query resolution has no commit-item index.
