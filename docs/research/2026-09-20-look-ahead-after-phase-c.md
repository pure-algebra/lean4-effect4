# Look-ahead after Phase C: the plan against the tree, and the next slices

Read at `16090306` on `refactor/phase1-phase3` (Phase C closed; nothing pushed). The plan of
record is the deep-dive review's slice table (`2026-09-19-plan-deep-dive-review.md` §4: T1–T5,
M1–M7, P1–P5) and the ranked order of the open design issues
(`2026-09-20-open-design-issues-order-and-observation-packet.md` §1). This note sets both against
what is in the tree, names the drift, and cuts the next slices into probes for Gemini. It rules
nothing.

## 0. Verdict

- **M1 is landed in full, M2 is half landed, M3–M7 are unstarted.** The redirect (Phase A, the
  placement, the skeleton, Phase C) delivered D2 (completion as data), the exact clock, the fiber
  origin with its site, the functor connector, and the `World` record with its order, columns
  and extension theorems. What M2 still owes is the hinge to everything after it: the
  `Preds World` instance (the seven custom predicates defined over the world) and the
  `RStateOk` statement on a loaded program. Without that instance there is no concrete
  ledger for M6 to count.
- **The instrument is ready for the milestone.** The ledger closes 351 of 393 statements by bank
  search across 65 gates, reports every miss of a scope at once, and the banks are split by
  role. The remaining 42 are known by cause; 31 of them are theorem-backed and want one
  small instrument change, not proof work (§3).
- **Two independent slices are done** (P2 `Arena`; R3 of P1), **three are untouched** (P3
  identities, P4 transactions, P5 Latch), and the plan's two tooling amendments that M6 needs
  (per-written-set frames F6, the coverage join F5) are not in the tree.
- **The register lags the chat.** Five rulings the owner gave on 2026-09-20 are not written in
  `decisions.md` (§2). By the project's own rule they are not rulings until they are.

## 1. The plan against the tree

| slice | planned deliverable (§4 of the deep-dive) | at `16090306` | state |
| --- | --- | --- | --- |
| T1–T5 tooling | ProofGraph, `#typed_state`, `#frame_rules`, the ledger, wiring | merged `de27095d`; Phase B repaired the heartbeat cache, made searched proofs portable, and the ledger now reports all misses | done |
| T3 amendment F6 | frames per *written field set* before M6 | `Laws/Auto/Frames.lean` is still one rule per field | **absent** |
| T4 amendment F5 | `#typed_state_coverage <steps> over <state> ledger S` | no such command | **absent** |
| M1 = D2 | `DeferredCell.completion : Option Completion`, `due : List (Owed Completion)`, `MemoEntry.effect` gone, the six deletions, OCaml regen | `8b64039f` (with the exact `ClockMillis` clock and protocol v3); connector closed 30/30 in `b2bf4cca` | done, one leftover: the memo identity write (§3.1) |
| placement | 47 files | `05417cc6` | done |
| M2 layer 1 | `World`, `WorldOrder`, Γ/Π/Ρ extension, the columns on data, **the nine hand predicates, `instance : Preds World`**, `Expect` pruned, `RStateOk P₁ w (loadR e fuel)` stated | `Typed/World.lean`: record, preorder, `WorldOrder` instance, columns as aliases of the generated `Stores_refs`/`DeferredStore_cells` clauses, coverage iffs, `heapNat_iff`, fork/refMake/deferredMake extension proved; `Expect` is three constructors. **No `Preds World` instance; none of `StackOk`, `ServiceOk`, `RaceOk`, `ResumeOk`, `InterruptOnly`, `CaptureOk` is defined over `World`** (only `Book.PendingOk` exists, at the fiber); no `RStateOk` control | half |
| M3 residual | `Typed/Residual.lean`, `#answer_gate`, `OpOk`/`AnswerOk` forty arms, `TypedProg`, `HandlesFit` | nothing; layer 0 (`Laws/Effects/Protocol.lean`) has the `WorldOrder`/`Protocol` signatures; `HandlesFit` is named in World's doc comment only | not started |
| M4 keeps and stack | `Laws/Machine/Keeps.lean`, `Typed/Stack.lean`, `popR_typed`, the handshake proof | `ParkHandshake` is *stated* (`Laws/Machine/Handshake.lean`) and its reachable obligation is held at ceiling 1 (`Guard/Handshake.lean`); no ladder, no typed stack | statement only |
| M5 = S1 | `denoteR_typed`, `InterpTyped` for the hook fields | nothing | not started |
| M6 = S2 | `Typed/Ledger.lean`, `Typed/Step/*`, coverage green before the first proof, the ceiling pinned | the ledger *mechanism* is exercised on 65 gates; the transition ledger itself does not exist | not started |
| M7 = S3 | `Typed/Transfer.lean`, `run_typed` through `replay_rel` | `TypedRun.run_sound` exists for the straight fragment (earlier work); nothing for the machine | not started |
| P1 observations | `Obs.semantic`, `Run.holder`, `Factors`, `transfer_safety`; R3 | R3 landed as `RunFiber.origin` with the site (row 20's yes); `Obs` unchanged (R79.1); `Run.Observation` is the holder view but the "never through the trace" factorization (R79.2) is not a theorem; `forkedOf` still exists and `Agrees` compares it to `originForks` (the trace-agreement residue); erasure has one open obligation | half |
| P2 arena | `Arena`, its laws, `refStepOf` over it, the list instance, OCaml `prop_store` | `Laws/Machine/Arena.lean` 14/14 at ceiling 0; red controls decided; OCaml controls `8cb639b4` | done |
| P3 identities | `ScopeKey`, `FinKey`, `Token`, `RaceId` as one-field structures | nothing | not started |
| P4 transactions v1 | after M7, `TxBody ∩ Straight` | nothing; row 84 open | not started |
| P5 Latch | the `Unit`/broadcast/scheduled instance | nothing; row 81 open | not started |

Two things the plan did not schedule landed anyway and are worth naming: the exact clock with
protocol version 3 (Phase A; the receipt says the owner chose it, the review asked for
confirmation), and the fiber-site path threaded from the compiler through `Prim.fork` (row 20,
an alphabet change that regenerated LCNF).

## 2. The register lags the chat

`decisions.md` at HEAD still reads: row 79 "open, recommended"; row 20 "open"; rows 48 and 51
"recommended"; row 52 "open, recommended". The memory of 2026-09-20 records the owner adopting
R79.1–R79.5, R3 in one-field form with row 20's site, and rows 48/51/52 as M3 content, the same
day. The tree already implements R3 and row 20. Before Gemini reads the register as authority,
these five rows need their ruling text; that is a docs edit for the owner to confirm, not a
design question. Row 84 (the first transaction fragment, F9) and the clock (review F4) remain
genuinely unanswered.

## 3. The Phase C residue, as work items

The forty-two open statements fall into five items. Only the first is a runtime change.

### 3.1 The memo slice (the review's F3)

`SyncOp.memoComplete` (`Machine/Stores.lean:2014`) completes the cell and then writes
`st.memo.updateEntry memoMap layer id`. The write is the identity on every entry, but
`updateEntry` goes through `mapAt` (the *first* map with that id) and `setMap` (which writes
that map into *every* map with that id). So on a memo world with duplicate map ids the "identity"
write collapses the duplicates to the first one; deleting it leaves them distinct. That is the
behaviour change Codex saw and kept the write for. The invariant that makes the write a no-op is
that map ids are unique: `MemoKeysFresh s := (s.memo.map (·.id)).Nodup` (or the `KeysBelow`
form the scope store already uses, `ScopeKeysFresh`, if memo ids are minted from a counter).
Under it `setMap (mapAt id) = id` is one lemma, `memoEntry_keys` follows, the write goes, and
the twelve `deferred.*`/`layer.memo-*` census witnesses are restated. It is a runtime edit, so
it takes the full regeneration order (`gen-lcnf`, `gen-cas`, `gen-eff`, then the OCaml build and
the differential run) in its own commit.

### 3.2 The static-site bridge (five obligations)

`source_fork_site`, `source_forkIn_site`, `source_forkScoped_site`, `source_race_site`,
`source_two_race_sites` (`Laws/Api/Supervision.lean:755–810`): from
`Node.at_ (.eff program) path = some (.eff (.withFiber …))` to `site ∈ supervision program`.
`supervision` is a fold; the missing piece is one lemma, membership in the fold from a located
node, by induction on the path, with the four site kinds as its corollaries. No design content.

### 3.3 The trace agreement (two obligations)

`step_agrees` and `reachable_agrees` (`Guard/TraceOrigin.lean`): `forkedOf m.trace =
originForks m` holds at load and is kept by a step. The route is that only `spawn` emits
`forked` and only `spawn` writes an origin, and every fork arm goes through `spawn`
(`spawn_origins`, `start_origins`, the three fork arms and the race launch are already proved).
Once this is a theorem on reachable machines, `forkedOf` becomes a control and then goes, which
is the deletion P1 promised (R79.2). This is the one residue item with real proof weight.

### 3.4 The observation ignores the trace (one obligation)

`observe_replace_trace` (`Laws/Run.lean:874`): every reader `Run.observe` composes
(`inspect`, `outstanding`, `pendingReplies`, `fiberStatuses`, `HostProtocol.observe`) is
trace-free after R3, so this is one projection lemma per reader and then `simp`. It is the
definitional half of R79.3.

### 3.5 The thirty-one theorem-backed statements

Each has a compiled theorem of the same name in the tree; the obligation stays open because
aesop's normalisation (`subst`, `simp`, the `And` split) changes the goal before the bank rule
fires. The receipt lists them by shape. Rather than restate thirty-one rules, change the
instrument once: when an obligation `S.x` has a namesake theorem `S.x` whose proposition is the
obligation's, the ledger closes it by that theorem through the existing `ProofRef.validate`
(name, universes, proposition by `isDefEq`, axioms within `[propext, Quot.sound]`) before it
runs the search. That is the declaration-backed pairing the ledger already documents, made
literal; it changes what is *counted*, not what is proved, and it removes the pressure to shape
rules for the search. One control: a namesake with a different proposition is refused.

### 3.6 The handshake

`parkHandshake_reachable` stays held until M4 by design.

## 4. The order from here

1. **Close the residue** (§3.5 first, then 3.4, 3.2, 3.3): the ledger reads zero open outside
   M4 and the memo slice. Half a day of proof work once the instrument change is in.
2. **The memo slice** (§3.1) as its own commit with regeneration and OCaml validation.
3. **The register** (§2): write the five rulings; answer row 84 and the clock.
4. **M2b: `Preds World`.** Define the seven custom predicates over `World` and state
   `RStateOk P w (loadR e fuel)` as the red control. Row 48 (the existential typed stack) is
   `StackOk`; row 51 (`ServiceOk` context-wide) is `ServiceOk`; the plan's F7 said
   `ResumeOk`/`InterruptOnly` retire by a table edit, and the table still carries both, so that
   is the first question the probe answers. This is the slice that turns the skeleton into a
   statement about the machine.
5. **T3/T4 amendments** (F6, F5): both are required before M6 and neither exists.
6. **M3, M4, M5, M6, M7** in the plan's order; M6 pins the ceiling.
7. **Beside the milestone, any time:** P3 identities (mechanical), the holder factorization of
   P1, L4 of rows 42/43 before M6 reaches `refUpdate`. **After M7:** rows 84/80, Latch.

## 5. The probes for Gemini

Gemini probes; it does not land. A probe reads the named files, writes the slice's statements
in a scratch file, elaborates them only when the compiler is free (one Lean process per
checkout; the editor's language server is tolerated), and returns a brief in the shape of the
2026-09-19 Gemini briefs: read list with line numbers, the statements, the deletions, the red
controls, the build commands, and every risk it hit. Nothing under `src/` changes; no generator
runs; `README.md` is untouched.

| probe | question it answers | reads | returns |
| --- | --- | --- | --- |
| **G1 residue instrument** | can the ledger close a namesake-theorem obligation through `ProofRef.validate` before searching, with a refusal control? does `isDefEq` accept the `let`-shaped statements (`fork_source_extension`, `actionAt_*`)? | `Laws/Auto/Obligations.lean`, `tools/ProofGraph/{Proof,Ledger,Search}.lean`, `test/Audit/Obligations.lean`, the receipt's §3 list | the patch as a diff in the note, the control's `#guard_msgs` text, the list of the 31 it would close |
| **G2 residue proofs** | the fold-membership lemma for `supervision` (§3.2); the spawn-only-forks route for `step_agrees` (§3.3): which step arms touch `trace` or `origin`, and is every `forked` emission under `spawn`; the per-reader lemmas for §3.4 | `Laws/Api/Supervision.lean` (`supervision`, `forkedOf`, `originForks`, `spawn_origins` block), `Machine/Fibers.lean` (`spawn`, `start`, `emit` sites), `Laws/Run.lean:860–880`, `Run.lean:213–262` | the lemma statements elaborated; a table of every `emit` site and what it emits; the reader table |
| **G3 memo slice** | the exact `MemoKeysFresh` (nodup or counter form); which ops mint map ids; is a duplicate id reachable from `load`; the no-op lemma; the census rows to restate; the regeneration order and the OCaml checks to rerun | `Machine/Stores.lean:551–600, 2014–2022`, `Laws/Machine/{StoresLaws,Handles}.lean` (`memoEntry_keys`), `docs/GENERATED.md`, `scripts/generate.py`, the Phase A receipt's OCaml check list | the invariant statement, the lemma list, the regen and validation checklist, the file radius |
| **G4 M2b `Preds World`** | for each custom row in `Typed/Sources.lean`: the smallest definition over `World`, what it reuses (`Book.PendingOk`, the fiber protocol, rows 48/51), whether `ResumeOk`/`InterruptOnly` still exist after F7; the `RStateOk P w (loadR e fuel)` control; whether `Expect` needs a fourth constructor for hooks at the world | `Typed/{Sources,Vocabulary,State,TypedStateDecl,World}.lean`, `Laws/Machine/Book.lean:234`, `docs/research/2026-09-18-typed-state-plan.md` §2–§3, the kickoff note §2 | seven definitions, the instance, the control, the open questions for the owner |
| **G5 M3 residual** | the forty `OpOk`/`AnswerOk` arms listed from `progress`'s hypotheses; the `FiberOp` constructors without a row (the gate's red control); `HandlesFit` for fibers, promises and refs against Γ/Π/Ρ; `TypedProg`; the external-table `Extends` premise World's doc comment says M3's weakening must carry | `Laws/Effects/Protocol.lean`, `Laws/Program/Residual.lean`, `Laws/Program/Progress.lean:346` (`progress`), `Typed/World.lean:8–47`, rows 48/51/52 | the arm table, the three `HandlesFit` statements, the weakening statement with its premise |
| **G6 T3/T4 amendments** | per-written-field-set frames: which step arms write which field sets (from the write census); the `#typed_state_coverage` join: step roots over state roots, what a "holder without a declaration" refusal looks like | `Laws/Auto/Frames.lean`, `Typed/Frames.lean`, `Laws/Auto/Obligations.lean`, `Test/Audit/{FrameRules,Obligations}.lean`, the deep-dive F5/F6 | the written-set table, the command's syntax and its controls |
| **G7 P3 identities** | which key types cross the bytes boundary (wire, CAS, LCNF) so a one-field structure is or is not a regeneration; the site count per key | `Machine/{Stores,Fibers}.lean`, `tools/Effect4Gen/wire-tags.json`, `ocaml/gen/roots.json` | the count, the regeneration verdict, the order |

G1–G3 are the residue and can start now. G4 and G5 are the milestone's next content and the
ones whose answers change what is built. G6 is owed before M6. G7 is filler for an idle probe.

## 6. Risks

- **M6's count.** The plan pins the ceiling at M6 after M1 and M2 for a reason: the transition
  ledger is one obligation per write-census holder per arm, and the 85-position census with 46
  frame rules and 90 reused clauses is the lower bound of its shape. `Preds World` (G4) is what
  makes the count concrete; F6 is what keeps it from being per-field × per-arm.
- **Monotonicity.** World's doc comment records that `ValueOk`/`CompletionOk` are *not*
  monotone for arbitrary worlds because `Stores.le` orders lengths and external handle
  admission reads spellings. M3's result weakening must carry external-table `Extends` or a
  legal-step spelling premise. G5 must state it, not discover it in a proof.
- **The bank search as the closer.** Phase C showed the search closes equations and
  single-conclusion facts well and whole-statement rules badly. If the M6 ledger is filled the
  same way, the instrument change of §3.5 is the difference between "proved" and "proved but
  open".
- **Two writers on one checkout.** Codex holds the compiler for M1–M2; Gemini's probes must
  stay at statement level or run when the compiler is idle; a worktree per seat is the safe
  form if the owner wants elaboration in parallel.

## 7. Numbers at HEAD

| measure | value |
| --- | --- |
| ledger gates / statements / closed / open | 65 / 393 / 351 / 42 |
| open by cause: unproved / theorem-backed | 11 / 31 |
| wanted markers in `src` | 44 |
| bank registrations Stores / StoreKernel / Fibers / TypedState | 129 / 4 / 91 / 10 |
| `make check` | green (`16090306`) |
| coverage | 133 green, 2 partial, of 135 |
| plan slices done / half / not started | T1–T5, M1, placement, P2 / M2, P1 / M3–M7, P3–P5, F5, F6 |
