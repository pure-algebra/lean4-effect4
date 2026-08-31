# Vocabulary — the user register of @foldlab/cas

The Lean model names every construct exhaustively because proof
obligations demand it. A person using the store needs about a dozen of
those names; the rest are protocol machinery that should stay invisible
until asked for. This document pins the split: the everyday register
(what the CLI and docs say unprompted) and the protocol register (what
surfaces only in `--json`, `inspect`, and reference material). The
internal glossary in
[docs/effect-replay/CONTEXT.md](../../docs/effect-replay/CONTEXT.md)
stays exhaustive on purpose; this is its user-facing projection.

Consumption contract: `--help` is the one surface for commands and
vocabulary together, because the two must stay coherent — a verb and
the words it speaks are one document. There is no separate vocabulary
verb and no startup card. Vocabulary is semantics, and in this
substrate semantics may alter while the grammar — the sorts, their
wire tags, the node structure — stays fixed. That is why help and
vocabulary flow toward store content rather than baked strings (the
CLI rider: help is a described document, loaded and rendered). This
file is the seed that content derives from — never a second, drifting
copy.

## The rule: vocabulary is consumer-gated

A term enters the everyday register only when a verb needs it — the
same admission discipline signatures follow. Until a verb summons a
term, it stays in the protocol register, absent from help. So the
tiering below is not a style judgment made term by term; it is the
current verb set, read off.

## The everyday register

| Word | Meaning | Model term behind it |
|---|---|---|
| store | the content-addressed data itself — a directory or a database file | `Store` (partial map, grows only, closed) over the store-root layout |
| address | the 64-hex identity of one piece of content; equal content means equal address | `Addr32` / `ContentId`, digest of the canonical bytes |
| kind | the form a thing takes: value, file, blob, schema | grammar sort (`Ty`) plus its wire tag — see collision 1 |
| value | the everyday unit: a typed JSON payload, put and got | `value` sort (0x01), canonical envelope |
| link | a typed edge to another address, declaring the kind it expects | `Ref` / `CasReference` (expected tag + address) |
| blob | large bytes, stored verified in chunks | `chunk` + `tree` + `manifest` sorts (0x08–0x0A), recipe 1 |
| file | a named file over a blob | `file` sort (0x0B) |
| schema | the shape a value claims, itself stored content with an address | `schema` sort (0x53), canonical schema plane |
| roots | the addresses published as entry points | `RootSig` — `publish` (fail-closed) / `listRoots` |
| program | a table of steps, itself content: put it, publish it, run it by address | `cont` sort (0x0F) over `step` (0x0E) — `Cas.Lang.PProg`, laid down by `encodeProg` |
| refused | a put that broke a store law; every refusal carries its clause name | the admission judgment, clause-named errors |
| verify | re-hash and re-decode everything reachable from a root | `Graph.verify` and the loader law |
| history | what was admitted, in order — a run's record, and the store's own (`cas history` reads it; the widening from a run's to a store's is versioned by decision 28) | the store word — see collision 5 |
| receipt | the store's persisted note that one admission happened: address, kind, size, when | a word-log entry (`wordLogEntrySchema`, generated) |
| mark | how far into the history a reader stands: a count, not a time | a zero-based word index — `WordE.since`'s argument, `--since <mark>` |
| in flight | how many store-touching calls a host runs at once — one bound PER PLANE, so a daemon with both planes saturated can be at twice it | `ServePolicy.maxInFlight`; stdio holds one gate, the daemon one per plane and says so at startup — `cas status` prints the number |
| doctor | the checkup: what this store is, and what the lab it sits in has proved so far | `cas doctor` — the runtime reader of the emitted ledgers |
| name | a human word on stored content — an annotation, never identity | `Annotation` at the pinned key `foldlab/name` (working tag 0x41) — `cas name` writes and publishes one, `cas show` reads it back |
| annotation | one thing said about one address, itself stored content; a name is the first kind | `Cas.Schema.Annotation` — the kind's own everyday word is emitted beside its tag (`AnnotationKindWord`), never written in the renderer |
| scheme | the address scheme content is stored and re-verified under; one exists today | `Cas.Grammar.schemeVersion` — the node's version byte, printed beside every kind |
| host | the process that serves a store to callers; `--host` is the address one binds | `cas serve` is the stdio host, `cas daemon` the HTTP one — see collision 6 |
| daemon | the long-lived host: one port, both wire planes, running until stopped | `cas daemon` |
| plane | one wire surface on a host's port; the daemon serves two | the abstraction over the two wire names — see collision 7 |
| heartbeat | the line a host prints on period, carrying its own numbers | `layerHeartbeat`, every 2 s, both hosts |
| stall | a beat that did not arrive: the host is blocked, and the silence is the evidence | the detected event; a late beat carries how late |
| origin | the web page a browser request came from; a daemon answers only the ones it was named | the `Origin` header, allowed with `--allow-origin` |

## The protocol register

| Term | One line | Abstracted by |
|---|---|---|
| node | the stored unit: version byte, kind tag, payload bytes, ordered refs | its kind: "a value", "a file" |
| payload | a node's opaque byte body | the rendered value |
| tag | the wire byte naming a kind (0x01, 0x53, …) | the kind's name |
| sort | the grammar's name for a node form | "kind"; never printed |
| word | a run's history: bindings in children-first admission order — the semantics carrier | "history" in human output |
| binding | one address-to-node pair in a word | — |
| marker | `{"$ref": k}`, the k-th reference positionally, inside canonical bytes | links resolve without it being visible |
| vector | a named, checked, replayable word — conformance evidence | `cas doctor` |
| entry | journal record / genesis (0x0C) | no verb yet; stays here until one lands |
| context | grouping node of typed edges with no payload (0x0D) | no verb yet; stays here until one lands |
| git | a git object as content, its SHA-1 derivable (0x47) | interop surface, opt-in |
| step / cont | F3 code points and program tables (tags 14/15, registry rows 14 and 15) | "program" — the run verb landed 2026-08-29, so the word is in the everyday register and these two are not |
| canonical | one spelling per content; the exact bytes the digest sees | invisible: it is why addresses work |
| form address | the address of a value's canonical representative under a named method | reference-level, new mint |
| signature, operation, handler, program, fuel, status | the store-language machinery | the CLI itself — its verbs are programs |
| cas-http/0, MCP over HTTP | the two wire surfaces a plane can be | "plane" — see collision 7 |
| `Host` header | the name a request claims it dialed, checked against the daemon's allowlist | "host": it is named as a header wherever it appears |
| logfmt, OTLP, Prometheus, CORS | borrowed names of external formats and mechanisms | nothing — a borrowed proper name is not estate vocabulary, and is spoken as itself |

## Collisions, resolved

1. Sort, kind, and tag are one thing in three registers: the grammar
   name (`sort`), the everyday word (kind), and the wire byte (`tag`).
   The proved round trip `Ty.ofTag_wireTag` licenses the collapse. The
   CLI says "kind"; `sort` never appears in output; the tag appears as
   hex in `--json`.
2. "Value" collides with itself. The value sort is the everyday
   meaning. The canonical envelope `{revision, value}` also has a field
   named `value`; that field belongs to the protocol register and shows
   up only when reading raw documents.
3. "Entry" and "context" are ratified sorts with no consumer verb, so
   the gating rule keeps them in the protocol register — undocumented
   in help until a journal or grouping verb exists. "Step" and "cont"
   were in that same position and left it on 2026-08-29: `cas run` and
   `cas put --program` are the verbs that summoned them, and what
   entered help is the abstraction — "program" — not the two tags. A
   `cont` node is never named in a rendered surface; it is "the
   program", and the address it sits at is "the program's address".
4. "Root" is three things. The everyday word "roots" means published
   entry points, and only that. The location of a store is "store",
   never "root", in every rendered surface. `Root α`, the typed handle
   the TypeScript value projection returns, is API vocabulary and does
   not appear in the CLI at all.
5. "Word" is the model's name for a history, and it stays the name in
   `--json` and in every claim (word equality is the conformance
   gate). Human output says "history": doctor's human line reads
   "identical admission history", and its `--json` line says word.

   The word now names two things, and the reading is widened rather
   than split. A RUN's word is what one `cas_run` admitted, and it
   travels in the reply. A STORE's word is what that store has ever
   admitted, persisted as receipts and read from a mark; `cas history`
   is the verb, and `--json` calls the document's list `word` for the
   same reason doctor's does. They are one term because they are one
   thing at different scopes — bindings in admission order — and the
   `store` in "store word" is the scope, never a second sense. What
   distinguishes them is what each carries: a run's word carries
   bindings, and a store's word is a projection that keeps the
   addresses and drops the nodes (`log ⋈ store` recovers them). So
   word equality remains the conformance gate over runs, and no
   receipts-plane claim inherits it.
6. "Host" is three things, and the register keeps them apart by how
   each is spelled. The everyday noun is the PROCESS that serves a
   store — "the stdio host", "the daemon". The daemon's bind ADDRESS
   is the second, and it is never a noun in prose: it is spelled
   `--host`, always as the flag. The HTTP `Host` HEADER is the third
   and stays protocol register; it appears only in `--allow-host`'s
   description and is named there as a header. No rendered surface
   uses the bare word for either of the last two.
7. "Plane" is the abstraction, and the two wire names are its tags —
   the same act as collision 3. `cas daemon` summoned a family of
   words, and what entered the everyday register is "plane", not
   `cas-http/0` and "MCP over HTTP", which stay protocol register and
   appear only where a caller must dial one of them by name
   (`daemon --help`'s long form, SERVING.md, the profile). "Heartbeat"
   and "stall" entered the same way and are their own words, because
   nothing abstracts them: the beat is the evidence and its absence is
   the event.
