# S3a source inventory

This inventory proposes no second state or interpreter.
It reads interfaces.md version 2, the elaborated interface probe, and the current owner drafts.
The coordinator owns landing order. S1/S2 APIs below remain unverified latest drafts.

## Named owners

| Surface | Exact owner API | Source |
| --- | --- | --- |
| Document identity | Program.DocId(name,generation); Program.Snap(doc,revision) | check_sol S1 SourceDocument draft |
| Document origin | Program.DocOrigin(id,app,sketch) | same |
| Open | Doc.open_ : DocOrigin → Check.Checked Doc | same |
| Snapshot checks | Doc.check : Doc → Snap → Except DocRefusal Unit, foreign then stale | same |
| Edit | Doc.step : Oracle → Doc → Snap → DocAction → Checked (Except DocRefusal (Doc × Receipt)) | same |
| Document projections | Doc.snap/id/revision/history/session; session.app/sketch/table | same |
| Edit address | Place.hole index or Place.at_ path expected; Place.resolve app sketch | same |
| Document action | commit items policy; draft Edit; revert entry | same |
| Atomic feed | SourceSession.feed oracle policy source edit | check_sol S1 SourceSession draft |
| Candidate key | SourceSession.partKey source path candidate : Option CheckInput | same |
| Fill state | FillSet.anchor : Snap; source : SourceSession; entries | check_sol S2 FillSet draft |
| Derived fills | FillSet.base/app/pending; pending uses base address order | same |
| New/reset fills | FillSet.open_ doc; no independent reset or current API | same |
| Fill batch | FillSet.add oracle fills submissions : Checked (FillSet × List AddOutcome) | same |
| Fill item | FillSet.addOne oracle fills path candidate | same |
| Publish | FillSet.publication : Except PublishRefusal DocAction; empty refusal, one keepExact commit | same |
| Run admission | Api.Built.ofSketch app sketch : Except AdmitRefusal Built | S4 temp draft |
| Run origin | Tool.Origin.snapshot Snap SigApp Sketch; standalone | S4 temp draft |
| Run commands | Live.open; Live.feed; Run.Event.commands | production plus S4 retirement draft |
| Saved run | LiveRecord.save/restore; full restore_save statement retained | production plus S4 connector draft |
| Preview | Run.Preview.admit and existing Tree/Kit operations | production Run/Preview.lean |
| Oracle | Check.Oracle; Checked pure'/bind'/ask/readVerdict | S0; V1 seals checker helpers under Internal |

Snap does not yet derive DecidableEq. Compare its DocId/revision fields if a Bool check is required.
DocRefusal is top-level Program.DocRefusal, never Doc.Refusal.
Its constructors are foreign, stale, empty, noEntry, place, and feed.
Receipt.steps is List Edit.Step. SourceSession has no expanded field.
The document application stays fixed across accepted actions.

## Protocol syntax inventory

Actions: open_, edit, fill, publish, reset, start, restore, play.
Queries: doc, history, fills, suggest, run, preview, dry, discover.
The exact constructors and answer/refusal payloads are in the version-2 interface probe.
RunId carries Nat n. RunForm is view, record, or journal.
There is no connection-selected method version inside semantic state.
Discover only reports supported versions; the driver owns version selection.

## Action and query dependencies

| Request | Existing owner calls and required order |
| --- | --- |
| open_ | allocate DocId from the semantic generation counter; Doc.open_; reset pending fills; retain prior runs |
| edit | require document; Doc.check/Doc.step at supplied Snap; install only accepted result |
| fill | require document; check document first; empty set anchors at current Doc; nonempty set requires exact anchor; FillSet.add outcomes stay inside accepted answer |
| publish | require document; check supplied Snap; require nonempty/current anchor; publication returns one DocAction; Doc.step once; reset fills only after success |
| reset | require document; discard pending entries; reset to FillSet.open_ of current Doc; acceptance is journaled even when already empty |
| start | require document; check Snap; Built.ofSketch at session.app alone; Live.open then feed start; retain immutable snapshot origin |
| restore | LiveRecord.restore; allocate run id; attach standalone origin; require no document |
| play | lookup run; fold Event.commands over a temporary Live; unresolved event refuses whole action; install only complete success |
| doc/history/fills | read current projections; require document as specified; retain state |
| suggest | validate document and Snap, resolve Place, use partKey plus the same keepExact feed certification as fills; retain state |
| run | lookup id; project view, LiveRecord, or ordered journal |
| preview | require document; use existing admitted Preview/Tree/Kit owner; no new evaluator |
| dry | evaluate the same action function from original raw state, return nested result, discard temporary state |
| discover | constant supported method versions, retain state |

Open/run retention and generation details must use the actual canonical Raw owner when implemented.
No shadow Tool state is introduced by this inventory.

## Legacy dispatcher retirement inventory for S3b

Tools.Session.State currently duplicates source, journal, app name, DocId, revision, generation, Live, cache, and fills.
Its helpers State.doc/withDoc/fillsFor/fillsStale duplicate document and fill ownership.
Its string-operation dispatch covers open/catalogue/receive/apply/liveView/save/load and document-specific operations.
The legacy replace/commit/fill/omit/draft/fork/view/undo/journal/sketch arms use old Doc APIs.
The legacy suggest arm uses CheckCache.suggest and List CheckCache.Entry.
Those are retirement inputs, not the semantic owner for S3a.
S3b must decode into Tool.Request, call Tool.serve, and encode Tool.Reply.
Keep source raw-read failures in the wire layer; semantic refusals remain Tool.Refusal values.

## S3b strict-profile input from ST3

The coordinator's ST3 preparation appends Store.Shape.value for raw existing Val output.
Its producer preserves reference edges. Generic JSON read at Shape.value refuses.
The strict JSON profile must classify Shape.value as unsupported, alongside the planned Option Unit refusal.
A catch-all must not admit it. Existing Shape constructor tags stay fixed.
ST3 owns Value regeneration. Canonical Val's syntax encoding is not this reference-preserving output codec.
The retained RawOutputControl supplies the distinction; no arbitrary raw-Val JSON inverse is claimed.
ST3 source at /private/tmp/seams-st3-scout/src remains uncompiled and is not imported here.

## Suggestion integration edge

SourceSession.partKey returns Option CheckInput, but the probe's Candidate.key is mandatory.
A resolved path can lack a typed focus; keepExact then refuses noFocus without a checker key.
Do not fabricate a module key to construct that candidate.
The actual S2 suggestion result must settle whether this is a query refusal or a revised optional key.
Tool.Refusal currently has no direct focus constructor. The protocol types remain unchanged here.

Owner correction: S2's actual CheckCache draft now builds a genuine candidate module key at the root.
Below the root, a missing partKey returns FeedRefusal.noFocus before Suggestion construction.
suggestOne returns Checked (Except FeedRefusal Suggestion); suggestPage propagates the refusal.
SuggestionKeyControls.lean retains distinct finite root-query and below-root-noFocus controls, pending fresh S1 artifacts.
The remaining protocol question is how S3a maps a page FeedRefusal into Tool.Refusal.
No frozen protocol constructor changes occur in this scout.

The actual page refusal carries no item index.
DocRefusal.feed's index belongs to DocAction commit items; reusing it would invent an index here.
The minimal proposed protocol correction appends Tool.Refusal.suggest (why : FeedRefusal).
Later feed refusals already remain inside Suggestion.evidence.feedRefused after a genuine key exists.
The coordinator authorizes the smallest explicit suggestion refusal when the existing wrapper cannot express this meaning.
Its Tool-level noFocus control must also show query state equality.

## Final transparency scope

The source's Oracle.eq_uncached supports the full planned serve o = serve uncached equality.
Checked.trace contains semantic queries and verdicts, so it also agrees for the same computation.
It contains no runtime cost or hit flags; V1's owner confirms that boundary.
Earlier scout advice to narrow the statement is explicitly withdrawn in PLACEMENT.md.

## Caller census files

legacy-callers.txt retains the named Tools.Session/State/answerLine references across source and tests.
legacy-callers.json records the measured matches and unique paths, including docstring-only references.
protocol-source-callers.txt extends the census to Tools.Query, fillPremises, omitPremises, valueFrom?, and Snapshot.
Opened namespaces require per-file review for unqualified calls; these named censuses do not claim otherwise.
S3a retires Tools.Query as the protocol source and routes its premises through Query.doc and Query.dry.
S3b migrates the Lean session driver, live driver, view builder, live view, and their controls.
Only after those callers move does Tools.Session.Snapshot disappear.
S3b's generated field decoder removes JsonBridge.valueFrom?'s hex-over-JSON precedence.
The same canonical Tool.Request/Reply owner serves both drivers and the view.

V1 trace correction: a logical root key is .module, while Checked.ask records its actual part dependencies.
The uncompiled root control now compares feed trace keys with the genuine Checked.ask .module trace keys.
It no longer expects a synthetic singleton module trace.
S2's owner separately checks Candidate.key = .module and the real dependency trace.
