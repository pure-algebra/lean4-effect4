# Coherence: the model, the seams, and the plan

Status: research note, the one entry for the coherence work of 2026-10-19. Base: `29f55957e` on
`refactor/phase1-phase3`. It folds in three earlier notes (`seams.md`, `one-service-many-backings.md`,
`vocabulary.md`), which it replaces, and it corrects them where a pressure test found them wrong.
It takes one more input: a second read by another session
(`docs/research/2026-10-19-second-read-authoring-release.md`). The owner adopted its author-first
order on 2026-10-19.

## 1. The one thing to know

There are two halves, and they are one construction. An author holds a document and changes it
by actions. A run holds a machine and changes it by commands. Each is a state reached by its
journal (K5). In a run, the host answers the program's questions and the tape answers the
runtime's choices. Every seam is one of these roles, declared once in Lean. Most drift is a role
written a second time by hand. The first release serves the author; the estate's steps follow it.

## 2. The run's half

```mermaid
flowchart LR
  subgraph RT["runtime: runs the program"]
    P["program: Eff over the row table"]
  end
  H["host: answers calls"]
  T["tape: answers choices"]
  J["journal: every call, reply and choice"]
  P -->|"call"| H
  H -->|"reply"| P
  T -->|"decisions"| RT
  P -.-> J
  H -.-> J
  T -.-> J
```

| Role | What it is | Lean | Effect TypeScript |
| --- | --- | --- | --- |
| program | Eff over the row table: it asks, it never does | `Eff` | a printed `Effect` with its requirements |
| row table | the operations a program may ask for | `RowTable`, declared by `eff_rows` | a service tag, one method per row |
| host | code that answers calls, in any language, anywhere | `Run.Reactor` | a layer that provides the service |
| runtime | what runs the program | the Lean machine | Effect's runtime |
| tape | the runtime's choices: which fiber runs, which reply applies first, when the clock moves | `NativeDecision`; the clock is the tape (`src/Effect4/Api/TestClock.lean`) | none: Effect's runtime chooses and records nothing |
| journal | every command of a run, in order | `Run.journal : List Command` (`src/Effect4/Run/Basic.lean`) | none |
| host session | the machine and its ledger of calls: bound, pending, applied, retired | `Api.HostSession.Session` | none |

A run's journal has four commands (`Command`, `src/Effect4/Api/Runner.lean`): `bind` a call,
`submit` a reply, `apply` one key's reply, and a `control` decision. The first three come from the
host side. The last, and the choice of key in `apply`, come from the tape.

## 3. The author's half

An author, a person or an agent, holds a few objects. The tree has each of them. The model above
left them out, and the second read named that gap.

| Object | What it is | Lean | Reached by its journal |
| --- | --- | --- | --- |
| sketch | a program with holes; a hole is a host row, so every fold reads a sketch as a program | `Sketch` (`src/Effect4/Program/Sketch.lean`) | — |
| document | a sketch with its source table, changed by actions | `Doc` (`src/Effect4/Program/Typing/SourceDocument.lean`) | its actions (`Doc.replayedState`) |
| fill set | the submissions that fill a sketch's holes | `FillSet` (`src/Effect4/Program/Typing/FillSet.lean`) | its submissions (`FillSet.constructed`) |
| workspace | the tool's state and the checker's memo | `Tool.Native.Workspace` (`src/Effect4/Tool/Native.lean`) | its accepted actions (`Tool.State.replayed`); stored as `WorkspaceEntry` chains |
| verdict | the checker, one `Except` fold, whose refusal is located | `Checker.check`, `Checker.explain` (`src/Effect4/Program/Checker.lean`) | — |

Three things follow:
- **One construction.** "A state reached by its journal" is written six times today (the audit's
  lc-1). A run and a workspace are two instances of it, over two alphabets: the run's commands
  and the tool's actions. The audit's M5 makes it one, `Replayed`.
- **One act, one spelling.** Filling a hole has two alphabets today: `DocAction` with a draft or a
  commit, and `FillSet`'s fill then publish. The slices plan's decision 9 asks for one field name
  per idea.
- **A concept to own it.** Row 414 (5) ruled typed editing the eleventh concept of
  `docs/core/semantics.md`. Its section is not written yet. Its prose is written now; its claims
  move when semantics generation resumes.

Agents write text, not JSON (adopted 2026-10-19). An agent writes Effect TypeScript in the printed
fragment. The reader turns it into `Eff` data, and JSON stays the wire.

## 4. The algebra under it

Each role is a construction the tree already has. `docs/core/semantics.md` concept 9 holds the
literature.

- **The row table is the application's part of the language signature, Σ_app.** A program is
  the free object over the language signature (K1).
- **A host is a comodel.** It answers the signature's operations from outside, with its own state.
  A reactor is a deterministic one (Plotkin and Power; Uustalu; Ahman and Bauer).
- **The tape is the relational meaning's decisions.** Full meaning is relational over tapes
  (AGENTS.md, representation rules).
- **The journal is the monoid action (K5).** `replay_unique` makes a run a function of its journal.
  The author's objects are instances of the same action.
- **The host protocol is the journal's host commands on the wire.** A call carries the operation
  and its request. A reply carries a completion at that row's answer or error type. Setzer and
  Hancock's dependent interface gives the shape: commands per state, responses per command.

The wire carries more than the algebra, and each extra field has one job (`Call`, `Reply`,
`Header`, `src/Effect4/Api/HostSession.lean`):
- correlation: `callId`, and `key`, the fiber and token of the waiting continuation;
- binding: `version`, `session`, `binding` and `table`, so a reply meets the run it belongs to.

One more thing follows from the algebra. A runtime that runs an application is a host for that
application's service. `TodoApp.add` is a call that the runtime answers, while `TodoRepo.insert` is
a call that the runtime makes. So one protocol serves every boundary, in either direction.

## 5. Where "effects as anything" stops

A host may implement any row, in any language. Four limits hold:
1. A reply carries data and fresh external handles only. An internal handle (a fiber, cell,
   deferred, scope or context) is refused at table admission (row 97).
2. A closure never crosses the host boundary (row 381 (3)).
3. A reply is applied at most once. Exactly-once external work is not promised (dictionary §3.7).
4. A retired call does no host cleanup (`RetiredCall`, `src/Effect4/Api/HostSession.lean`). The
   host is not told that its call was abandoned. Decision D5 rules abandon, after the release.

## 6. Runtimes and their agreement

| Runtime | Takes a tape | Keeps a journal | How it agrees with Lean |
| --- | --- | --- | --- |
| the Lean machine | yes | yes | it is the reference |
| the OCaml engine | yes | a tape, but no host session (`E4_host`) | the lowering is trusted (row 391); finite lanes compare runs |
| Lean compiled to C | yes | yes | the same source, another compiler; nothing builds it yet |
| Effect's runtime | no | no | printed programs checked against rc.112; the host calls recorded by an outside layer (`apps/todo/server.ts`) |

So two checks exist, of two strengths:
- Between runtimes that take a tape, replay one journal on another and compare. That is exact.
- With Effect's runtime, compare only the record of host calls and replies. Compare it on a
  fragment whose host calls do not depend on the schedule (row 361). Effect's choices stay unseen.

## 7. Rule S, the seams

**Rule S.** In every target, a file has one of three origins. It is generated from Lean, or it
implements a seam that Lean declares as data, or it is build tooling. A seam's body implements a
signature. It may call outside libraries, keep its own state, and fail with the declared failure.
It never decides an observation that Lean defines. A body kept for speed has a Lean definition
beside it and a control that runs both.

The rule is per target. It holds for OCaml and for TypeScript alike.

| Seam | Lean declares | Hand code writes | Today |
| --- | --- | --- | --- |
| carrier | a type row and its operation rows, with contracts | a row's body, or nothing when a package has it | `OCaml5.Lcnf.typeRows` and `builtins` hold; the engine's carriers sit in `ocaml/engine/externs.txt`, outside Lean, with no contracts |
| host | the row table (`eff_rows`) | one host per row table | TypeScript's service is printed from the table; OCaml's record is lowered from a typed interface written by hand (F3) |
| platform | an alphabet of the runtime's resources: files, locks, domains | one interpreter | no Lean declaration yet; `E4_file`, `E4_lock` and `E4_sched` are its bodies |
| shell | the method table (`tool_requests`) and the queries | the transport | `Kit_tool` holds; `Kit_serve` executes requests by hand |

Measured at `761fd13db`: 23,485 lines of hand OCaml outside the tests. 15,631 of them restate
meaning: the store, the run layer, the kit's logic and the clock. That is the drift rule S removes.
The command and the classification of each file are in the history of this folder (`seams.md`, at
`db6720577`).

A transcription's tests go with it. A seam's controls stay: the type checker holds a body to its
signature, and a row's control compares a body with the lowered definition.

## 8. What the pressure test found

The first sketch of this model was too simple in nine places.

| Id | Finding | Evidence | Response |
| --- | --- | --- | --- |
| F1 | A run has two outside inputs, not one: the host's replies and the tape's choices | `Command`; `Api.TestClock` | §2 shows both |
| F2 | The journal belongs to the run, not to the host session | `Run`, `Session` | the dictionary's host session entry is corrected |
| F3 | The to-do's typed host is a hand copy of `eff_rows`, in Lean: `Todo`, `SqlTag`, `Host`, row names as strings | `Test/Dogfood/Scenario/Todo/Typed.lean`; tied only by `#guard`s | `eff_rows` generates the typed interface (release item 7) |
| F4 | The host session is spelled once per runtime: Lean's `HostSession`; none in OCaml, where `E4_host` restates `driveFrom`; hand TypeScript in `harness/truth/session` | `ocaml/engine/e4_host.ml`; `keyed-recorder.ts`, `keyed-protocol.ts` | one Lean definition, lowered or printed (estate track) |
| F5 | Lowered code does no I/O, so a platform seam needs plans and readers | `E4_checkpoint`'s streaming closure (CP9) reads as it walks | a plan of operations for writes; a reader that asks for bytes; measured before the store moves |
| F6 | The engine's carrier table is outside Lean, with no contracts | `ocaml/engine/externs.txt`, 52 rows | it becomes type rows (the audit's M10) |
| F7 | Effect's runtime makes its choices unseen | §6 | cross-runtime checks compare host calls, on a schedule-independent fragment |
| F8 | The protocol carries correlation and binding fields beyond the algebra | §4 | named, each with its one job |
| F9 | The model had no place for the author's objects | the second read, §3.3 | §3 |

## 9. The plan

Two tracks, in this order. The release track comes first (the owner, 2026-10-19). The two tracks
replace four earlier orders: the audit's M1 to M11, `seams.md`'s S1 to S4,
`one-service-many-backings.md`'s B1 to B7, and this list's first version. Each item deletes what it
replaces.

Done: the vocabulary, in the dictionary (`5418973ea`, `c92fe3633`) and the workspace rename
(`a12b2bbd2`). Left: three deep-core comments and one `#guard`, with the next edit of their files.
Row 418 records this plan. Release item 1, `docs/STATE.md` as one page, is done. Item 2 is
done too: `docs/core/semantics.md` §2.11 holds the typed-editing concept, as prose.

### 9.1 The release track

The first release is Lean authoring, the TypeScript face, and the tool over MCP (`eff mcp`, in the
kit).

| # | Item | What it cuts or replaces | Size |
| --- | --- | --- | --- |
| 1 | **`docs/STATE.md` as one page, true at HEAD**: the faces, how each is used, this plan, the owner's open decisions | about 400 lines of the entry point | XS |
| 2 | **The author's half in the documents**: the typed-editing concept's prose (row 414 (5)) | nothing; it places the audit's lc-1, lc-2, lc-5 and lc-7 | S |
| 3 | **The TypeScript slice, ahead of E6**: `ts/eff` reads and writes the canonical tagged print; `toJson` writes what `open` reads; binders named by scope in `ts/eff/read.ts` and `src/Effect4/Codegen/Read.lean` | `V.json` and `OCaml5.Eff.V`'s conversions (part of M7); the `a0` rule | M |
| 4 | **Agent text in**: `open` and `fill` take Effect TypeScript text through the reader; `describe` serves the catalogue | nothing; it adds the face the ergonomics probe asked for | S |
| 5 | **The reply diet, and one field name per idea** (A4; the slices plan's decision 9) | the repeated bytes; one of the two fill alphabets | S |
| 6 | **One check, one observation, one command face** (row 414 (3); M8; A6, with R2's A7.1) | `Api.check`, `Api.explain`, `Run.Kit.check`, `Run.Kit.admit` and `Run.Preview.admit` as separate entries; `Run.observe`, `Run.work`, `machineViewOf`; `Kit_serve`'s execution | M |
| 7 | **The host seam from `eff_rows`**: the typed interface, the host record and its reactor; keys by name | `Todo/Typed.lean`, `REPO`, the README's hand keys | M |
| 8 | **M1, one located refusal** | nine records and a prefix rule | S |
| 9 | **M2, one profile judgment at ingress** | `E4_engine.check_answer`; the A1.1 defect on `eff`, which ships the tool; with R2's A5.2 | S to M |
| 10 | **A public-name manifest for Lean**: each name of the entry modules taught, internal or test-only; `Effect4.Author` re-exports the taught ones | `Program.Edit` and `Program.SketchWire` from the entry; the extra run and check entries, marked internal | S |

```mermaid
flowchart LR
  I1["1 STATE.md"] --> I4["4 agent text in"]
  I3["3 TypeScript slice"] --> I4
  I4 --> I5["5 reply diet"]
  I5 --> I6["6 one check, one view"]
  I8["8 M1 Located"] --> I6
  I9["9 M2 profile"] --> I6
  I7["7 eff_rows host seam"] --> I10["10 Lean names"]
  I6 --> I10
  I2["2 author's concept"] --> I10
  I10 --> R["first release"]
```

The TypeScript slice moving ahead of E6 changes the order that row 417 (5) set for the repair wave.

### 9.2 The estate track, after the first release

1. **The host protocol from the journal.** One Lean definition of the wire messages, lowered for
   OCaml and printed for TypeScript. `E4_host`'s copy and the hand keyed protocol go. D4 and D5 are
   ruled when it starts.
2. **The cross-runtime test.** The to-do service as one Effect layer per runtime, one script
   through each.
3. **Carriers.** E6; packages for SHA-256, CRC and hex; the byte kernel as a row with a control;
   M3 and M4.
4. **The run layer, lowered** (M10).
5. **The store over the platform seam** (M5's store part, M6, M11). D1 and S-1 are ruled when it
   starts.
6. **The rest of the Lean moves**: M7's fold for `Shape`, and M9. Then the exchange natively (the
   slices plan's X1) and MCP 2026-07-28 (X2).

The rest of the repair wave follows the release: R2's A4.1 and A9.1, and R3.

## 10. What the owner decides

| Id | Question | State | When |
| --- | --- | --- | --- |
| D2 | The public JSON's lists | open; recommended: arrays | before release item 3 |
| D3 | The native profile after E6 | open; recommended: the profile is a datum the run is checked against at ingress | before release item 9 |
| S-2 | Is the generated host interface public? | open; recommended: yes | before release item 7 |
| D1 | The log: harden it, or one commit construction | deferred past the first release (the owner, 2026-10-19) | estate item 5 |
| S-1 | Is the store's on-disk format meaning? | deferred with D1 | estate item 5 |
| D4 | The drive after a refused reply | deferred with the protocol; recommended: the OCaml rule, written once in Lean | estate item 1 |
| D5 | Abandon, and whether a host is told | deferred past the first release (the owner, 2026-10-19) | estate item 1 |
| — | What text an agent writes | adopted: Effect TypeScript in the printed fragment, through the reader | release item 4 |
| — | What the first release is | adopted: Lean authoring, the TypeScript face, the tool over MCP | §9.1 |

D1 to D5 are the audit's (`README.md` §7).

## 11. How we work while this churns

- **Frozen until the first release.** The store: R1's repairs stand, with no second log, no
  lowering and no format change. The bridge: no process-boundary protocol, and
  `apps/todo/server.ts` keeps its recorder. `Run.Tree`, preview and explore stay internal to the
  tool's `preview` query and `eff explore`; they are not taught.
- **Semantics generation is paused** (the owner, 2026-10-19). `make gen-semantics` does not run, and
  no claim moves between concepts. The workspace's laws stay in concept 9 until it resumes.
- **One document.** This note is the entry. Its inputs stay as evidence: `orientation.md`,
  `plan.md`, `lean-core.md`, `compiler-estate.md`, the audit's synthesis `README.md`, and the
  second read.

## 12. What this does not establish

- The comodel reading is the literature's frame for a host, not a theorem in the tree.
- No process-boundary protocol runs yet, and no lowered store is measured.
- The classification of hand files is a reading of their headers. A step reads the code before it
  deletes.
- The sizes of §9.1 are the second read's estimates.
