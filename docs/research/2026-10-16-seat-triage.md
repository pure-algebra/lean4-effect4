# 2026-10-16 Triage of the five seats: what lands now, what waits for D2, what goes to the backlog

Status: research note (history, not authority). Base: `81f9a4354` on `refactor/phase1-phase3`.
Role: the coordinator's review of the five seats of 2026-10-16. The owner asked for a review of
each seat, and asked that nothing merge unread. Each seat's receipt and note were read. The
code diffs of the OCaml, math and dogfood seats were read.

## The one thing to know first

Three pieces land now, each with its own gate: the OCaml estate's native hosts, the math seat's
`FitsIn` foundation, and the ingest fix. The dogfood showcases wait for D2. Each one builds a
`Built` by hand or imports `Program.AdmitIn`, and D2 changes both. The TypeScript and C seats
land as research notes. Their Lean slices go to the backlog.

## 1. The seats

| Seat | Branch, head | What it delivered | Verdict |
| --- | --- | --- | --- |
| OCaml and Rocq | `seat/ocaml-interop`, `d3bca195a` | the driver's stops `Raised` and `Outside_profile`; the module type `REPO` and native hosts; faster frame writers; a test lane 4 times faster; Rocq proofs of a pure to-do core | land now, after `make check-ocaml` |
| Math (D3) | `claude/math-d3`, `b3453c241` | `FitsIn` beside `Fits`: 4 proved laws, 5 planned goals, the landing plan | land the foundation now; the D3 landing goes after D2 |
| TypeScript types | `seat/ts-types`, `7bde6f0cf` | the named-types probe (26 cases), the declaration-block design, lean4-typescript v0.8.0 on a local branch | land the note and the probe; the repin waits for the owner's push |
| C interop | `claude/sad-williamson-6d3b65`, `abf5259ad` | the C face's design; a C11 frame codec that agrees with Lean's decoder on 144,978 inputs; a C host | land the note and the prototype as research |
| Dogfood | `claude/laughing-northcutt-cd0311`, `f51812cee` | five showcases; 17 friction points ranked; a fix of the ingest's dropped `if` body | land the ingest fix now; the showcases after D2 |

## 2. Findings of the review

1. **The OCaml seat's exception policy agrees with `AGENTS.md`.** A raise is no answer, so the
   call stays a live frontier. `AGENTS.md` keeps an unanswered choice a live frontier. Effect's
   `UnknownError` default differs. The coordinator takes the frontier default.
2. **Rocq does not enter the estate.** Rocq-of-ocaml reaches only pure OCaml, and it translates
   `Hashtbl.replace` as a pure call. The handlers worth proving are written in Lean and lowered by the LCNF
   route (row 405). The proofs stay in the seat's research folder, with the switch `rocq` (1.0 GiB).
3. **D1 left a duplicate arm.** `Val.hasTy` (`Program/Typed.lean`) and `Fits`
   (`Laws/Program/Typed/Membership.lean`) still read `app n _` as a host handle. Row 406 (1)
   makes `handle n` the only host handle, and admission refuses an undeclared `app n []`. So
   the `app` arm can read no member at an undeclared name. `FitsAt` copies the duplicate. The
   D3 landing removes it in all three.
4. **The dogfood seat's friction F1 and F12 are D2.** F1: a program built under named types
   has no session. F12: the session tool's `open` takes no types. D2 indexes `Built` and the
   session by `SigApp`, so `TreeRow.lean` becomes D2's acceptance showcase.
5. **The TypeScript seat found a printer gap.** Lean's guardedness passes `option`, `except`,
   `exitOf` and `map`, and tsgo refuses a cycle through their aliases (TS2456). The printer
   needs the deferring spelling on such a cycle, or the alias refuses.
6. **Two compiler builds run today.** The Schema lane runs `typescript` 7.0.2 with
   `effect-tsgo`; every other lane runs the pinned native preview. The seat's probe gives the
   same 21 diagnostics on both.

## 3. Land now

| Piece | Commits | Gate |
| --- | --- | --- |
| The OCaml estate's code, note and receipt | `b2f5cf07e`, `d3bca195a` | `make check-ocaml` |
| `FitsIn`, its note, probes and receipt | `b3453c241` | narrow build; `#axiom_audit`; `make gen-semantics` |
| The ingest fix | `f51812cee` | `bun test ingest/test`; `scripts/check-ingest.sh` |
| The TypeScript note, receipt and probe | `7bde6f0cf` | `bun probe/named-types/run.ts` |
| The C note, prototype and receipt | `5efde1328`, `abf5259ad` | none: research only |

## 4. After D2

| Piece | Source | Why it waits |
| --- | --- | --- |
| The five showcases, wired into `Test/All.lean` | `3f9ecab46` | `Sandbox` and `ProgramStore` build `Built` by hand; `TreeRow` imports the deleted `Program.AdmitIn` |
| `TreeRow` through `Run.open` with a control that refuses `badDisk` | dogfood receipt, obligation 4 | the session reads named types only after D2 |
| `Api.Built.admit program app` (F3) | dogfood F3 | D2 owns `Built`'s shape |
| `typesJson` on the session tool's `open` (F12) | dogfood F12 | D2's session takes `SigApp` |

## 5. The backlog

Each item names its source. The order within a group is the order of value.

### 5.1 The proofs and the typing

1. The D3 landing: `World.types`, `Fits := FitsIn w.types w`, the tie in `MachineTyped`, and
   the 41 premises `types = []` (math note §7). It also removes finding 3's duplicate arm.
2. The five planned goals of `FitsIn`, in the math note's §6 order.
3. `Fits` as a fold over the codes (math note §8, S2). A face's validator then agrees with
   membership by `hom_eq_cata_ty`, one theorem per face.
4. The shape decides membership under a table (S4), and one environment judgment (S6).
5. The checker readers' twins merged (`TyHead`, `Decision`), from the audit.

### 5.2 The TypeScript face (W5)

1. The repin of lean4-typescript at `2ae4083`, after the owner pushes it, and its six arms.
2. The declaration block, the target head and the deferring spelling (TypeScript note §4.2).
3. The printer's refusals of a clashing name (§4.3).
4. The Schema document's reference arm and `N_S`'s rule; the Schema code (§4.5, §4.6).
5. The readers of the block (§4.7).
6. P1 to P6 of the note's §5.2. P4, one compiler build, and P5, codes on expected errors, are
   small.

### 5.3 The OCaml estate

1. A generated `.mli` beside each LCNF artifact: 11.7 s off a cold build.
2. One lowered machine for every lane: `todo_gen.ml` lowers 795 declarations again.
3. `REPO` and its adapter generated from a typed host structure.

### 5.4 The C face

1. LC-9's `@[export]` byte entries and the reply entry (C note §5.3). They edit
   `Run/Live.lean`, so they wait for D2.
2. A library target cut to the session's closure (`lakefile.toml`).
3. A C printer of `Modeled` codecs as an algebra of the type fold, with a table of C type rows.
4. The layout as measured target data, and profile support for C carriers.
5. Paths (C note §4.6). The owner confirmed that "fpath" names Bünzli's OCaml library, as the
   C seat read it.

### 5.5 The API and ergonomics (dogfood)

1. One small slice: F4's stop reason, F8 `Authoring.elab`, F10 `Built.calls`, F11
   `Store.seeded`.
2. The envelope (F2), after a ruling on D-C of `docs/core/api-surface.md` §2.
3. One naming rule for the reader and the edits (F5, F7).
4. The reader's statements and operators (F13), and the low items F14 to F17.

## 6. What the owner decided, and what stays open

1. Open: the push of lean4-typescript's branch `types/type-alias`, and with it the repin.
2. Ruled: "fpath" names Bünzli's OCaml library, as the C seat read it.
3. Ruled: the switch `rocq` stays. The OCaml seat now models interaction trees in Rocq, on the
   vessel dogfood (branch `codex/vessel-dogfood`).
4. Retasked: the math seat takes the call tree, the session and the program graph.
5. Retasked: the TypeScript seat takes Schema interop and the semantics of its expressions.

## 7. Landed after this triage

- D2 (decisions row 407) and the math seat's two commits, `FitsIn` and the call chains, with
  `Api.Built.calls` (F10) and the dictionary's relation. They are on branch `wip/declared-ref`, then
  `refactor/phase1-phase3`.
- The near battery check reads Lean's `.ilean` references: D2 reaches 212 batteries, not 697.
- The math seat takes D3 next, from that head.

## 8. What this does not establish

- No gate ran for this triage. Each verdict in §3 owes the gate its row names.
- The seats' numbers are their receipts', not measured again here.
- Finding 3 comes from reading two arms. No build tested the removal.
