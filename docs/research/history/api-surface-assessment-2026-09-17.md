# The application surface after the seats: the 2026-09-17 assessment (history)

Moved from `docs/core/api-surface.md` on 2026-10-03. Sections 2, 3, 4 and 6 of that document as
written on 2026-09-17: the constructs judged opaque and their replacements, the unifying laws, the
no-decision action list and the order after the decisions. Several items have since landed (for
example `Await` as a structure and the `FiberStatus`/`Observation` codecs); none of this is current
status. The live surface and the open decisions stay in `docs/core/api-surface.md`.

Owner's ask: "organize; determine what we need to refine and consolidate; unify some things with
proofs to make everything coherent; remove the opaque and awkward constructs; find out where the
decisions are that we really need to make." Inputs: the three seat receipts
(`2026-09-17-seat-{run,author,daemons}-receipt.md`), scout C (`2026-09-17-mcp-surface-scout-C.md`),
scout D (`2026-09-17-schema-interop-scout-D.md`), and the integration section of the ledger
(`2026-09-17-scout-findings-ledger.md`, "The seats integrated"). Tree: `refactor/phase1-phase3`
at `cfa40786`, `make check` green.

**Summary.** The surface is now four deep modules — `Author` (a `Module` to a `Built`), `Run`
(a `Built` opened, played, observed, replayed), `Supervision` (fork sites before, fiber statuses
after), and the older `Api` face (`check`, `Typed`, `Inspection`, print/read/bytes/schema) — with
nine headline laws at the axiom ceiling. Three things are wrong with it, and they are the same
thing seen three times: **the boundary does not say what it means.** A record is a nameless
tuple (`Await`, `Observation.fibers`, `rowNames`, every application's request), a handle's
published schema is not the value that crosses, and the row table travels by value in every
call. Everything else is either a mechanical fix with no decision content (§4, do now), a proof
that ties two existing pieces together (§3), or one of ten decisions (§5) — of which the first,
*how a record and a sum are named at the boundary*, is the language decision the rest hang on.

The additions in §1.1 describe the editing and session APIs added on 2026-10-03. The later
consolidation assessment retains its 2026-09-17 scope; current rulings live in
[decisions.md](decisions.md).

## 2. The opaque and awkward constructs, each with its replacement

Ordered by how much they distort what an agent sees.

1. **Nameless products at the boundary.** `Await` is `abbrev FiberId × Nat × NativeOp × Val`
   (`Program/Admit.lean:37`); `Run.lean` reads it as `await.2.2.1`, and it prints as
   `[[{"value":0},[0,[…]]]]` on the most-read response field (C §3.4). Same shape:
   `Observation.fibers : List (FiberId × FiberStatus)`, `Built.rowNames : List (String × Nat)`,
   `ForkSite.body`'s pair returns. **Replacement:** `Await` a structure `{ key : Key, op, request }`
   (`Key` already exists as `⟨fiber, token⟩`, `Api/Frontier.lean:12`); `fibers` a list of
   `{ fiber, status }`; `rowNames` a list of `{ spelling, position }`. Mechanical; the codecs are
   then generated with field names.
2. **Every application's request and answer is positional**, because `Ty` has no `Struct` and
   no `TaggedUnion`: a record lowers to `Arrays`, a sum to an `anyOf` of tagged tuples (D §6),
   and the estate holds two sum encodings at once (`eff.gen.ts` says `TaggedUnion`, `Ty.schema`
   says `anyOf`). **Replacement:** decision D-A (§5) — names carried by annotation on the
   `Representation`, then `Ty.record`/`Ty.variant` if that is not enough.
3. **A handle column lies.** The published schema is `Declaration{id: "KeyValueStore…"}`; the
   value `externalValue` accepts (`Compile.lean:1354-1365`) is a `nat` equal to the allocation
   counter — proved by a refused `Val.handle 9 0` beside an accepted `Val.nat 0` (D §7.2). And a
   live handle crosses as a *legal* `Val` case (C §3.4). **Replacement:** decision D-B — a host
   reviver mints the index (rc.112's own mechanism); a described handle is refused when it
   arrives from another process.
4. **The row table travels by value.** Every `Call` carries the `RowTable`: 89% of an answer's
   bytes, and `Command`'s advertised schema is 231 660 characters (C §2.5, §4). `Built.bytes`
   omits the table, so two builds against different tables have the same bytes (C D3).
   **Replacement:** decision D-C — `Built.digest` over `programBytes ++ tableBytes`
   (`Canonical RowTable` exists, `RunnerDerived.lean:856`), and the `Call`/`Header` carry the
   digest.
5. **`ofSchema` widens.** A `String` with `minLength`, a `brand`, a `title`, a declaration with a
   payload — all read back as bare `.string`/`.handle` and reprint without them (D §7.3). A gate
   that widens is not a gate. **Replacement:** every leaf arm refuses a non-empty `checks` and a
   non-`null` payload except the two checks the bridge mints; `ofSchema_schema` unaffected. No
   decision.
6. **`effDocument` keys a requirement on half a `ServiceKey`** (`Schema/Bridge.lean:167`,
   `k.name` without `k.service`), emitting duplicate reference keys naming no carrier (D §7.1).
   **Replacement:** key `k{name}_{service}` as the printer already spells it, and file the
   carrier's schema — which means `effDocument` takes the signature. No decision.
7. **D12 has no consumer.** `Api.schemaOf` had zero call sites (deleted 2026-10-01 under row 39; `EffTy.document` is the publisher); the printer emits no
   `Effect.Effect<A,E,R>` annotation for any program with a requirement (`Print.lean:70-79`
   answers `none`); no gate decodes an exit under its own schema (D §7.5). **Replacement:**
   decision D-D — the S-5 truth-lane gate first (the only consumer that can fail), then the
   printer's annotation.
8. **Two docstrings lie**: `Api.schemaDocument` and the module note (`Api.lean:60-61, :591`)
   promise `Schema.Struct({…})` text; what exists is the persisted `SchemaRepresentation` JSON,
   and no `Schema.*` combinator text exists anywhere (D §1). Fix the words now; the text itself
   is decision D-E.
9. **`gen`/`Stmt` has no authoring lift.** The statement family (`Stmt`, `Stmts`, 364 lines in
   24 files) is reachable from the reader only; an author re-expresses every loop with
   `iterate`/`select` (D §8.1). The owner ruled `gen` stays (2026-09-17). The consequence to
   confirm is decision D-I: the reader's image and the author's image differ by one constructor
   family that no author can write.
10. **The daemon words.** `daemonFork` / `daemonForkIn` with the `daemon p [in s]` syntax (scoped: written where `Effect4.Program.Authoring` is open, as `eff` is); no word
    for `forkScoped` (the ambient scope); the daemons seat's D4 asks for `fork` / `daemon p in s`
    / `detach p`, with no author-written flag at a pin. Decision D-G, small.
11. **A transcribed literal.** `raceEntrantOptions = ⟨true, true, .interruptible⟩` copies
    `Machine/Fibers.lean:941`, tied by `launchEntrant_forked`; the literal sits at 8 more Laws
    sites. Name it once in `Machine/Supervision.lean` when the machine is next edited (D-H, with
    the path on `RunEvent.forked`).
12. **The hand-written prelude.** `harness/truth/prelude.ts` is the only TypeScript every printed
    program imports, is a hand transcription by its own header, and carries no schema for its
    twenty atoms (D §5, D-8). Generate it from `NativeAtom.all` and `PrintLeaf.Head`. No decision.
13. **`Repr` is missing** on `Observation`, `FiberStatus`, `EffTy`, `NativeOp`, `ExitV`. Do not
    derive it (on a nested inductive it becomes `partial` and the trust gate refuses); generate one
    `head : T → String` per sum, as `TypeReason.head` already does (C D12). No decision.
14. **Two authoring verbs**: `Api.author` (a source, check only, to a `Typed`) and
    `Author.program` (a source, admitted, to a `Built`). Keep both verbs — *check* answers where
    a source is wrong, *build* makes it runnable — and tie them with a proof (§3.4) so neither is
    a second pipeline. No decision once the proof is in.
15. **`nativeSignatureWith`** sits in `Services.lean` as a declaration-site check only; threading
    it through the checker changes the certificate and the soundness statements. Decision D-I.

## 3. Unify with proofs: the laws that make the pieces one thing

Each is a small theorem over definitions that already exist; together they say that nothing at
the boundary is computed twice.

1. **The observation is a projection.** `observe_inspect : (s.observe).outcome = s.inspect.outcome
   ∧ (s.observe).exit = s.inspect.exit ∧ (s.observe).reasons = s.inspect.reasons` (by `rfl` once
   stated), and `observe_daemonsQuiet : (s.observe).daemonsQuiet = Api.daemonsQuiet s.machine`
   — then `daemonsQuiet_iff` gives `Supervised s.machine` from the boundary reading alone. This
   is the theorem that licenses "`Observation` crosses, `Inspection` does not".
2. **Build's certificate is check's.** `build_check : Author.build m = .ok b → Api.check b.program
   b.table = .ok b.typed`, from `admitted_unique` (run seat) and proof irrelevance. Closes §2.14:
   `author`/`check` and `build` are one pipeline with two verbs.
3. **The wire identity is sound.** After D-C: `digest_inj : b.digest = b'.digest → b.program =
   b'.program ∧ b.table = b'.table`, from the codecs' `ofVal_exact`. Without it, "replay from the
   journal against `buildRef`" is a promise the server cannot keep.
4. **The claim is the machine's.** Already there (`bindCall_at`, `at_of_requestOf`,
   `answer_accepted`); restate over the `Await` structure when §2.1 lands so the field names
   appear in the statements.
5. **The schema face is a retraction and nothing more.** `ofSchema_schema` (exists) plus, after
   §2.5, `ofSchema_refuses : r.checks ≠ [] → ofSchema r = none` at every leaf; after §2.6,
   `effDocument_keys_nodup`; after D §7.4's fix, `document_keys_nodup` for `ShapeDoc.document`.
6. **The static tree and the run agree at paths.** `supervision_static` proves the flag, not
   "at those paths", because `RunEvent.forked` carries no path (daemons receipt §7.1). One field
   on one constructor (D-H) closes it; until then the battery pins it by count.
7. **The face is definitional.** `Built.runSync = Typed.runSync ∘ typed`, `Built.print = …`,
   `Typed.requires` — all `rfl` now; no theorem needed, which is the point of §1's unification.

## 4. No decision content — do now, in this order

1. `Canonical FiberStatus`, `Canonical Observation`: two lines in the `Runner` group of
   `tools/Effect4Gen/manifest.json` and a regeneration (D §3; closes run receipt O-8).
2. `Await` as a structure (§2.1), `fibers` and `rowNames` named; the run laws restated (§3.4).
3. `ofSchema` refuses (§2.5); `effDocument` keys and carriers (§2.6); `ShapeDoc.document`
   deduplicates (D §7.4); the two docstrings (§2.8).
4. `observe_inspect`, `observe_daemonsQuiet`, `build_check` (§3.1–3.2).
5. `head` per reading sum from the generator (§2.13); the `Refusals` group (eight refusal types,
   C §3.3) so every refusal an agent can see has a codec.
6. The author seat's C1: `Env.mint` in `Sugar.bindWith`, `Sugar.andThen`, `Loops.iterateWith` and
   `tools/Effect4Gen/Forms.lean`, one regeneration (the red control is pinned).
7. The prelude generated (§2.12). CI repaired (broken since `78684a8`; it is the other reason the
   corpus pin went stale).

## 6. The order after the decisions

1. §4 now (no decisions), then the observation dogfood (D §9.3: `readKey` open/play/observe/cross,
   schema-closed) as the receipt that the run seat's work is whole.
2. D-C and D-F: `Built.digest`, the `ToolSpec` table, the Lean driver, the `Refusals` group — the
   first agent-facing surface, on the run protocol.
3. D-A, D-B, D-D, D-E: names at the boundary, the reviver table, the S-5 gate, the `Schema.*`
   text — then the ledger and the pool dogfoods, which are what those decisions are for.
4. D-G, D-H, D-I: the file moves, the machine edit, the two confirmations.
