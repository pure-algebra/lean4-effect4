# The one list — every open decision of 2026-09-17, deduplicated (2026-09-17)

Folded from: the consolidation note (D-A…D-J), the three seat receipts (daemons D1–D4, author
C1 and its three decisions, run §4–§5), scout C (D1–D12), scout D (D-1…D-8), scout E (E-1…E-10
and its eight slices), scout F (F-1…F-12 and the seven squares), the LCNF survey (§7, the LLVM
steer). Where two or more said the same thing under different names, one row; the sources are
listed so the reasoning can be found. **Owner** = a ruling is needed; **do** = no decision
content, scheduled. Recommendations are the coordinator's, after reading all six inputs.

## A. Types and schemas at the boundary

| # | decision | recommendation | sources | who |
| --- | --- | --- | --- | --- |
| 1 | **The canonical schema object.** (a) the Schema AST replaces `Representation`; (b) the AST is a second carrier whose `toRepresentation` fold lands in the pinned 22-tag one; (c) no AST carrier | **(b), after row 6 and row 11 land** — the pin and `fromJson` are about the persisted projection, so (a) discards the estate's only stamped schema claim; the AST is needed only for the three things the projection drops, and only one of them (a transformation) is something Lean owns better than rc.112. This reverses the coordinator's earlier position, on E's evidence | E-1, E §13; D §5; consolidation D-J | owner |
| 2 | **Names for records and sums.** (a) sugar only; (b) `Ty.record`/`Ty.variant`; (c) annotation-carried names | **(c) now, (b) before the first foreign consumer, as stages** — `select` reads the tagged tuple that `Arrays[Literal t, T]` already is, so annotations keep the eliminator working; a foreign `decodeUnknownSync` never reads an annotation, so the first consumer of a published record dates (b) | D-A, D-1, E-5, C §3.4 | owner |
| 3 | **`Ty` and the AST.** Design A (`Ty` embeds, proved) + `Ty.app name args` with `handle t = app t []`; or Design B (the checker over AST nodes) | **A with `Ty.app`** — B's cost is measured: `deriving DecidableEq` and `Repr` fail on `Representation`, and `Ty.key`'s injectivity (hence `normalize`, `sub`, both soundness statements) does not survive `Json` annotations in the key. `Ty.app` is five additions and one S1 wire tag | E-4, E §4, E-R3 | do (tag assignment recorded under S1) |
| 4 | **Checks with meaning.** (a) `Check.holds : Check → Val → Bool` over a closed id list; (b) store-reading; (c) none, agreement per boundary as a theorem | **(a) for the closed list + (c) for the external-handle counter** (`externalValue_iff_fits` beside `Admit.lean`) — the one check that matters at a real boundary is not a predicate on a value; (b) would put the store into every check | E-2, E §3, E §6; D §7.2 | owner |
| 5 | **D12's shape.** One theorem `decode ast v = some x ↔ fits ast v`; or the sound/total pair with `isValueAst` **plus** the S-5 harness gate (every recorded corpus exit decodes under its published `Schema.Exit`) | **the pair and the gate, as two claims** — the single theorem is false in the total direction (the S-3 amendment); the Lean theorem and the host gate are about different decoders. This is F's square C6 and D's D-5(b) | E-3, D-5, F C6, D-D | do |
| 6 | **`ofSchema` refuses what it cannot represent** (non-empty `checks`, non-`null` payload, except the two checks the bridge mints) | do first; `ofSchema_schema` unaffected; F's exactness (C3) begins here | D-3, F-6, consolidation §2.5 | do |
| 7 | **Handles at the boundary.** (a) publish `Number` + the counter check; (b) opaque declaration + a host reviver minting the index; (c) state the exclusion. And: a described handle arriving from another process is refused, admitted in-process | **(b), with the cross-process refusal** — rc.112's own mechanism, the same one the six `effect/schema/*` ids need for row 11; the schema accepts a live handle either way, so the refusal is the MCP face's, not a schema check | D-B, D-2, C-D8, E §6 | owner |
| 8 | **`effDocument` keys a requirement on half a `ServiceKey`; `ShapeDoc.document` repeats keys; two docstrings promise `Schema.Struct` text** | fix all three now (key `k{name}_{service}` and the carrier's schema, threading the signature; dedupe by key and refuse a repeated key with different bodies; say "the persisted `SchemaRepresentation` JSON") | D §7.1, §7.4, §1; consolidation §2.6, §2.8 | do |
| 9 | **`Api.schemaOf`.** A projection with no reader, no law, zero call sites | **give it C6's consumer (row 5) this wave, or delete it** — a published schema nobody decodes under is a claim, not a boundary | F-11(a), D §7.5 | owner |
| 10 | **One `Val → Json`.** Four independent images today | **`ShapeDoc.print` survives**, `Schema.encode` proved equal to it on the admitted domain, the harness's two `valJson`s deleted — the shape-directed image survives any change to `Ty` (row 2); the type-directed one does not | F-5, F C4, C §3.2 | owner |
| 11 | **Where `Schema.*` text comes from.** (a) a second emitter beside `printAlgebra`; (b) rc.112's `toCodeDocument` + a reviver table; (c) none | **(b)** — one owner for the spelling; the reviver table is row 7's work | D-E, D-6, E slice 5 | owner |
| 12 | **`Transform`'s category laws** (identity, associativity at the meaning) or rename the composition API so it does not read as a category | **prove them once `denote` is a fold (row 30)**; if too costly, rename — an unlawful composition API in the schema layer is how a second program language starts | F-8, F §4b | owner |
| 13 | **The schema/program rule.** Schema is a data language; every effectful slot is a hole filled by an `Eff` program with a typing certificate; `Ty`/AST never mention `Eff`; a foreign `Transformation` is a name with an AST-typed signature that any meaning-needing operation refuses | write it into the vocabulary (row 36) | F-7, F §4b; consolidation D-J | do |

## B. The run and the MCP surface

| # | decision | recommendation | sources | who |
| --- | --- | --- | --- | --- |
| 14 | **The table travels by digest.** `Built.digest` over `programBytes ++ tableBytes`; `(digest, Run.id)` the wire identity; `Call`/`Header` carry the digest | **yes, now** — 89% of an answer's bytes and a 231 KB advertised schema are the table by value; `Canonical RowTable` exists. Changes the wire shape of `Header`/`Call` (compat policy) | C-D3, C-D7, D-C | owner |
| 15 | **The MCP server.** Lean `--run` driver in `src/Tools` first, generated bun second; fourteen tools, `run.play` withheld; the server holds the journal, not the `Run`; no reactor over the wire; `ToolSpec` table inside the gate; the run protocol before R12's inspection protocol | **yes, as one choice** — only a Lean host gets `open_total` (a `Module` is a function, a certificate is a `Prop` record); `journal_replays` makes the cached `Run` an optimisation; four of R12's nine commands are buildable and five need a `Doc` that does not exist | C-D1, D2, D4, D9, D10, D11; D-F | owner |
| 16 | **`Await` becomes a structure** `{ key, op, request }`; `Observation.fibers` and `Built.rowNames` named | do — the most-read response field prints as nested arrays today; a projection in the MCP layer would be a second representation | C-D6, consolidation §2.1 | do |
| 17 | **Codecs for the reading types.** `Canonical FiberStatus` and `Canonical Observation` (two manifest lines, `Runner` group); a `Refusals` group for the eight refusal types; `head : T → String` per sum instead of `Repr` | do — no decision content; closes run receipt O-8 and the observation dogfood | D-7, C-D5, C-D12 | do |
| 18 | **`Built.digest` injective and `observe_inspect` / `observe_daemonsQuiet` / `build_check`** — the proofs that tie the faces | do with rows 14 and 16 | consolidation §3 | do |

## C. Authoring, daemons, and the older face

| # | decision | recommendation | sources | who |
| --- | --- | --- | --- | --- |
| 19 | **The three root modules and the daemon words.** `Effect4.Author` / `Run` / `Face` as the imports an agent writes, `Api.*` the deep source; `fork` / `daemon p in s` / `detach p`, no author-written flag at a pin | **yes, as a file-move wave after group A's first slice** | D-G, D-I2, daemons D4 | owner |
| 20 | **One machine edit.** A path on `RunEvent.forked` (closes `supervision_static` "at those paths"); the race-entrant options named once (a literal at 9 sites) | **yes, together, one rebuild** | D-H, daemons D3, consolidation §2.11 | owner |
| 21 | **`nativeSignatureWith`** stays a declaration-site check (`ServiceDef.Agrees`, `BuildRefusal.serviceCarrier`) rather than threading through the checker and the certificate | **keep** until an application needs a seventh carrier — threading changes `Built`, `HostSession.start`, `Run.open` and both soundness statements | D-I3, author receipt | owner |
| 22 | **`gen`/`Stmt`** stays a printer spelling with no authoring lift (authored programs never contain `Stmt`), or the statement family is retired from `Eff` | **confirm the first**; the owner ruled `gen` stays on 2026-09-17; the consequence is one constructor family no author can write | D-I, D §8.1 | owner |
| 23 | **`Api.author` beside `Author.program`** — two verbs, one pipeline, tied by `build_check` | do (row 18); no cut | D-I1 | do |
| 24 | **The minted-spelling fix** in `Sugar.bindWith`, `Sugar.andThen`, `Loops.iterateWith` and generated `Forms.lean`; one regeneration | do — the red control is pinned | author C1 | do |
| 25 | Settled, recorded: `FiberStatus.root` stays; the six `rfl` proofs stay `rfl`; the error column stays wide; the three named runs return the `Run`; `Observation` derives `DecidableEq` only | — | daemons D1, D2; D-4; run §5 | — |

## D. Lowering, TypeScript generation, vendoring

| # | decision | recommendation | sources | who |
| --- | --- | --- | --- | --- |
| 26 | **The rules for canonical TypeScript**, corrected by E. Every TypeScript artefact is a fold of a *committed table or free object* (`Eff` for programs; the row/`Entry` table for types, folded two ways — a Schema AST for values and a `TypeRef` for types, never one from the other; the LCNF closure for code); no artefact from the Lean environment (`TsGen`'s read retired) or from a hand transcription (`prelude.ts` generated); the emitter targets the TypeScript **syntax** AST; type generation is split — tables own types, LCNF owns semantics, sugar owns authoring | **adopt** — E's count (91 of 7,008 exports are AST-typed entries; `Effect`, `Layer`, `Stream`, `Ref`, `Deferred`, `Queue`, `Scope`, `Fiber`, `Exit` all 0) is why "TypeScript types from the Schema AST" cannot be the rule and "two parallel folds" can | D-J, E-6, E-7, E §10, F-11(b), D §5 | owner |
| 27 | **The LCNF per-module recipe** (roots → closure + case-site policy → emit → rung 2/3 differential → truth differential → `Entry` table) with *decision agreement on the observation* as the obligation, and the fact that **certificates do not cross** (`Prop` erasure); root order: codecs, the checker, the `Run` transitions, the authoring lifts | **adopt** | F-9, F §6, LCNF survey §5 | owner |
| 28 | **What "verified lowering" means.** (a) a full CompCert-shaped simulation between `Conform.Lcnf.Semantics` and `SemanticsTarget`; (b) rule coverage for the rungs (every translator rule has a red mutant) plus a simulation on the scalar fragment only | **(b)** — six mutants for a twelve-row walk plus a 50-row table is an under-covered control; the full proof is not the cheapest true claim | F-10, F C7 | owner |
| 29 | **The lowering architecture (the LLVM steer).** High tier (OCaml, TypeScript): target descriptions as data (`Profile`, `Lowering`) with decided laws; legalization (promote / expand / custom) as rewrite rules with obligations, seeded from `Conform/Rules.lean`; `SemanticsTarget.Expr` promoted from the rung-3 reader's image to the common currency every printer consumes. Low tier (WebAssembly, native): Lean's reference-counted IR into LLVM, no backend of ours | **adopt after row 31** — the TypeScript printer is the profile's first customer | LCNF survey §7; owner 2026-09-17 | owner |
| 30 | **`denote`, `effTy`, `compileEff` onto the fold** (the three exemptions of F's census). `denote` first, `effTy` second; `compileEff` carries `Point` with fuel and risks the ~1,900-line agreement proof | **`denote` and `effTy` this wave; decide whether `compileEff` stays exempt** | F-3, F C1 | owner (for `compileEff`) |
| 31 | **The rung-3 TypeScript reader before any emitter breadth** (`TypeScript.Expr → Target.Expr`, refusing by constructor name, the same 20,387 vectors, the six mutants red) | do, in this order — the only artefact that makes "the emitted TypeScript means what the Lean function means" a checked claim | E-10, E slice 7 | do |
| 32 | **Vendoring order.** The two package modules (byte-identical regeneration of the 8 existing rows) → `McpSchema`'s 78 harvested Schema ASTs → `Duration` → `Exit`/`Cause`/`Option`/`Result` → the handle modules → `Effect`/`Layer`/`Stream` last, with a published refusal list; scanner = tsgo in `harness/schema-host` (the oxc recognizer has no checker) | **adopt** — the first two steps produce falsifiable evidence with zero emitter work | E-9, E-8, E §11 | owner |
| 33 | Two additions to `lean4-typescript`: a type-parameter binder list on `ConstDecl`/`ProgDecl`; `TypeRef.intersection` if an `Entry` ever needs it (none of the 91 does) | do when row 26's emitter needs them | E-6 | do |

## E. Coherence gates and the vocabulary

| # | decision | recommendation | sources | who |
| --- | --- | --- | --- | --- |
| 34 | **The traversal census as a gate** (C1: every `Eff` traversal is `cataFam alg` for a declared algebra or a named exemption; ten algebras, six exemptions today) and **fusion generated** for `Eff` (C2) | do — one generated table and one generator change; the exemption list's length becomes the honest distance from the principle | F-1, F-2 | do |
| 35 | **Fragments by exclusion** (`Straight`, `Looped`, C5) and **exactness wherever a read exists** (C3: `ofSchema` first, the JSON codec second) | do — a new constructor silently leaves both fragments today | F-4, F-6 | do |
| 36 | **The vocabulary in `AGENTS.md`**: free object, algebra, fold, exact embedding (three laws), simulation, located refusal, monoid action; the rule that a new representation is admitted by naming its signature and the kind of each of its arrows; row 13's schema/program rule | do — "the owner asked where to *go*; there is nowhere to go, and the vocabulary is what makes that usable" | F-12, F-7 | do |
| 37 | **CI repaired** (broken since `78684a8`; the other reason the corpus pin went stale) | do | ledger | do |

## The order

1. **Now, no rulings needed** (rows 5, 6, 8, 13, 16, 17, 18, 23, 24, 34, 35, 36, 37; row 3): the
   schema fixes, the codecs, the `Await` structure, the tying proofs, the census and fusion, the
   vocabulary, CI. The observation dogfood (D §9.3) is the receipt that the run seat's work is
   whole once rows 16–18 land.
2. **Group B and the first of group A** (rows 14, 15, 2, 4, 7, 9, 10, 11): the digest, the Lean
   MCP driver over the `ToolSpec` table, names at the boundary, checks with meaning, handles, the
   consumer for `schemaOf`, one `Val → Json`, the reviver table — then the ledger and the pool
   dogfoods, which are what those rulings are for.
3. **Group D** (rows 26, 27, 28, 31, 32, 29, 30): the TypeScript rules, the recipe, rule coverage,
   the rung-3 reader, the vendoring order, then the profile/legalization/IR refactor with the
   TypeScript printer as its first customer; `denote` and `effTy` onto the fold along the way.
4. **Group C and the rest** (rows 1, 12, 19, 20, 21, 22): the AST as second carrier, the
   `Transform` laws, the file moves and daemon words, the machine edit, the two confirmations.
