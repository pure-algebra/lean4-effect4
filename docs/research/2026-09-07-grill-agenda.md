# Grill agenda — 2026-09-07

Consolidation of four reports against `2026-09-07-implementation-direction.md` and the
fifteen questions in `2026-09-07-open-design-questions.md`:

- **S** = `2026-09-07-direction-scout.md` (Fable, forward probe of the direction; verified)
- **P** = `2026-09-07-lit-papers.md` (the 21 effect-handler papers)
- **L** = `2026-09-07-lit-lineage.md` (this repo's own notes, 09-02 → 09-07)
- **X** = `2026-09-07-lit-siblings.md` (foldlab, effect4_of_ocaml, lean4-CAS, lean4-effects,
  WHATWG streams, effect4-host)

§1 is the per-question reconciliation. §2 is the delta this applies to the direction (v2).
§3 is the list of calls for the grill, each with the default I recommend. V1 is already
dispatched (`2026-09-07-v1-dispatch.md`); nothing below changes it.

## 1. Per question

| Q | S | P | L | X | Reconciled |
| --- | --- | --- | --- | --- | --- |
| **Q1 handlers** | — | KEEP (a), sharpen | KEEP (a) | KEEP (a) ×3 | **Keep dictionary passing.** Write the coupling: it is sound only because continuations never escape as values (P T3). Index `Ctx.services`, never scan (P T2). Duplicate service instances need distinct keys (L 24). A context that is only a dictionary pays one acquisition per *use*; the memo store is what makes it per *build* (X Q13). |
| **Q2 scoped ops** | — | KEEP + taxonomy | KEEP | KEEP | **Constructors for the scoped set; captures for the latent set; no body-carrying row kind for either.** P's taxonomy (algebraic / scoped / latent) settles it: masks, scope, catch, timeout are scoped and return to the continuation; releases, service bodies, deferred cell bodies are latent and cannot be expressed by a scoped row (Hefty §2.6.4). If a scoped row is ever added its shape is `⟨request, bodies, answer⟩`. **Open (§3.1):** how derived forms (`timeout`, `withPermits`, `transaction`) are stored. |
| **Q3 continuations** | — | KEEP | KEEP | KEEP ×4 | **Keep.** Two riders: a `Point` is a syntactic label, never an identity — request identity stays `(fiber, token)` (X Q12); and the run's result must say what happened to open scopes at a frontier (P change 5). **Open (§3.9).** |
| **Q4 profile** | — | KEEP | KEEP profile, CHANGE framing | KEEP | **Finite profile, membership + `hasTy`, no row polymorphism.** But requirement rows already carry a join-semilattice with proved laws (provision-algebra), so "no row typing" is wrong; add the three typing grades (schema/ty/param/handle) and the *error* half of a row to the admission surface before it freezes (L). Grammar is data. |
| **Q5 coordination** | WakeMode now/scheduled | CHANGE: phase number; drain-before-poll | CHANGE: one *protocol*, per-family policy; Task widening is a core change | CHANGE: TxRef out; cancelled-waiter disposition; four completion milestones | **One allocation-and-wake protocol: waiter list + completion + `WakePhase : Nat` + cancelled-waiter disposition.** Per-family payload discipline stays (Semaphore signed counter/no FIFO, Queue signal-then-repoll, Latch two flushes, Deferred completion is a program). `TxRef` is its own subcalculus, not a member. Timer is an instance keyed by deadline (P Q6). The scheduler surface (wider `Task`, addressable dispatcher, coalescing guards) is an explicit core slice before Queue. **Open (§3.4).** |
| **Q6 time** | `clockAdjust`+`sleep` first; `advance` with inject | KEEP `advance` decision | KEEP decision; `advance (by)` not `(to)`; `clockAdjust` collides with refusal R2 | KEEP; logical clock cannot detect deadlock | **A4 lands `sleep`, `clockNow`, and the decision `advance (by : Nat)`** (duration; R1 stays refused), staged fire semantics as the workshop transcribed, with the one new `RunInterp` field S says it needs. No `clockAdjust`: the store models the live clock (R2). Phantom-parameter removal stays a separate sweep (S). H1 needs a wall-clock stall deadline: a parked run spends no budget (X). **Open (§3.3).** |
| **Q7 tape** | fact 11 wrong; projection from the frame | KEEP; INV-TAPE-1/2 | KEEP | KEEP tape; bound all-tapes; three outcomes; resume-from-snapshot is a trap | **Keep.** Write INV-TAPE-1 (no off-tape choice) and INV-TAPE-2 (a frontier names the row it awaits; projection total on frontiers). Say which decision sources the tape covers and that fairness is not among them. Three outcomes + one latched frontier (effect4-host already has them). `replay(program, tape)` is proved sound in the predecessor (`replay_is_a_function`); **accepting a supplied snapshot is a different operation and is not in the 0.1 surface** (X). Decide partial state on refusal: operational only (§3.5). |
| **Q8 composing** | — | KEEP | KEEP narrowed | KEEP | **Keep:** the product of two machines is a host loop, no fusion law. |
| **Q9 CAS** | D1–D4: append-only, tape bytes, log projection, snapshot group | NO GUIDANCE | CHANGE: job / receipt / checkpoint | CHANGE: pre-image recipe, lattice, identity chain, name the three observables | **Adopt the settled objects.** Job = `(program address, fuel, tape address, profile)`; receipt = annotation node with result digest, evidence never in identity; checkpoint = machine bytes + decision word since the last, portable only at a stable cut. Pre-image `versionByte :: kind :: enc(canon …)`, decoder validates the byte; one-byte domain prefix; a snapshot node *references* the program node; order program → frame → machine; no machine kind exists yet — mint one, append-only; hash bytes, never declarations. Name tape / log / exits apart first (X: "one name, three objects" survived a green gate). |
| **Q10 inject/observe** | `inject` later; `Point.root` now | KEEP | injection = an *answer*; the trace is NOT an observation (×4); three owed rulings | KEEP | **Two injection shapes, not one:** (a) answers to foreign rows (the tape, already); (b) starting an additional root program = a decision carrying the program's *address* (a value), after X2's admission. **Observation:** `Obs` stays exits + stores; the observer face (reading/mask/narrative over the daemon ring) is an unproved public surface, said plainly; its three owed rulings (op `site`, `Ann ≠ Unit`, `annotate`) travel with the wire-touching alphabet changes (§3.6). Rename one of the two "middlewares". |
| **Q11 program algebra** | — | KEEP; decide ElabTable vs wire-breaking | KEEP + derived-forms table | KEEP | **Keep `StdLib/` expansions; laws only where an optimisation relies on one.** The storage question is §3.1. |
| **Q12 callbacks** | — | KEEP two kinds; Capture is the general rule | CHANGE: three kinds (name tables exist, three more planned) | KEEP two kinds | **Three kinds today, converging on two.** Name tables (`FnName`, `φ`, `ν/σ`) are frozen: no new one unless the pin gives a closed opcode union (Schedule does not, so `SchedName` is refused). New *pure* callbacks wait for the term carrier below `Machine` (R4: `SyncOp` cannot import `Program.Term`; `Data/Term.lean` may already be that carrier — verify). New *effectful* bodies mint a `Capture`, never a `FinName` arm (P). `DecidableEq` gate applies to all three. **Open (§3.2).** |
| **Q13 Layer** | fold; NO `LayerTable`; path-addressed | KEEP L1 (makes S item B moot) | KEEP fold | KEEP fold ×4; is `St.memo` needed? | **Fold, path-addressed.** Three A3 warnings from X: give the shared store a bottom; do not state a `provide` associativity law (kernel-false at both planes); check which way a duplicate key shadows (row and meaning differ). From L: memo agreement must stay statable; refcount law `present ↔ observers > 0`; reserved keys 0–3. Memo store stays (rc.112 memoisation is observable across provide sites) — verify during A3, not before (§3.10). |
| **Q14 parallelism** | — | KEEP | KEEP | KEEP | **Keep.** |
| **Q15 cause** | — | KEEP + product decision | premise wrong: carrier is flat | premise wrong; adopt EC1-R21 | **Restate:** the runtime `Cause` is already rc.112's flat dedup'd list and *is* the normal form; the tree is `CauseTerm`, whose `causeOf` is a declared lossy quotient. No canonical form on the wire; interrupt-reason equality is annotation-map *identity*, so a structural canonicaliser would be wrong (X). Record `both`'s order as scheduler-dependent. Build the owed witness (distinct ordered `CauseTerm`s, one reason list). Three owed alphabet changes (`Outcome.defect`, `Ann ≠ Unit`, `CauseTerm.done`) go with the tape touch, before bytes freeze. **Open (§3.7).** |

## 2. Delta to the direction (v2)

Applied on top of `2026-09-07-implementation-direction.md`; the earlier file stays as the
record of the first cut.

1. **Order:** B1 → A2 (V1, dispatched) → A1′ (U1b, Context half only) → A3 (join,
   path-addressed) → scheduler-surface slice → A4 (timer) → Queue … (S §F; L Q5).
2. **L1/L2 stand; Layer D4 dies:** no `LayerTable` in the machine; `LayerTerm` joins the `Eff`
   family, `Eff.provideLayer` appended, `LayerId := List Nat` (S §B; X Q13).
3. **L3 stands, generalised:** every future deferred body mints a `Capture`; `FinName` and the
   other name tables are frozen (P Q12; L Q12).
4. **L4 stands.** L5 corrected: the row is projected from the parked frame, not from a name;
   the external row (`Row.registration`, `EffName.external`, `requestOf`) is X2's first item
   and precedes H1 (S §D).
5. **L6 replaced:** A4 = `sleep` + `clockNow` + `advance (by : Nat)` as a decision (one new
   `RunInterp` field) + `WakePhase : Nat` on the due drain + cancelled-waiter disposition;
   phantom removal separate; no `clockAdjust` (S §C; P Q5/Q6; L Q6; X Q5).
6. **L7 stands; three owed alphabet changes** (`Outcome.defect`, `Ann ≠ Unit`,
   `CauseTerm.done`) and the observation rulings land together with the first tape-format
   touch (X2), append-only (L Q15, Q10).
7. **L8 stands** with S §E: `Nat.pow` clamp first; roots `run`/`replay` before
   `bytesOf`/`ofBytes`; program bytes through `eff_wire.ml` until strings exist.
8. **New: the 0.1 daemon runs on `ocaml/link`** (compiled Lean); the generated engine is the
   js/wasm lane and replaces link's engine when it passes the truth corpus (S §G; owner call).
9. **New: the public log is a projection with its own codec; `RunEvent` is internal.** The
   snapshot is a generator `Machine` group plus two hand images. `Point.root` now (S §D/§G).
10. **New: CAS objects** are job / receipt / checkpoint with the pre-image recipe, domain
    prefix, machine kind minted append-only, evidence never in identity; resume-from-snapshot
    is not a 0.1 operation (L Q9; X Q7/Q9).
11. **New: INV-TAPE-1/2 written into DB-12;** three outcomes and a latched frontier; the tape
    covers the listed decision sources and not fairness (P Q7; X Q7).
12. **Standing warnings carried into A3/A4** (L "Forgotten"): reserved keys 0–3; memo refcount
    law; memo agreement statable; store bottom; no `provide` associativity; shadowing direction;
    staged fires; integer-width refusals (63-bit OCaml, 31-bit wasm); the released-token gap
    on interrupting a parked host promise.

## 3. Calls for the grill

**Ruled 2026-09-07 by the owner: all fifteen (1–11 below, and 12–15 from the late lineage
lane) as recommended.** 12: request records are a projection from the parked frame, never a
machine field; `TapeAbides` is never a premise of the agreement theorem. 13: `eff_frame.ml`
readers for tags 11/12 are the PC generator lane's first commit, not optional. 14: fiber-local
state is a context region, no per-fiber store. 15: the decision log is machine-relative,
stamped with the run address; no handle-freeness lemma. Item 8 (daemon on `ocaml/link`) was
explained and accepted with the JS-host condition.

Each with my default. None blocks V1.

1. **Derived forms (`timeout`, `withPermits`, `transaction`).** Options: (a) store programs
   *expanded* — derived forms are Lean library + printer/reader sugar, the address changes when
   an expansion changes and meaning per address is fixed; (b) an `Eff.derived` constructor plus
   a named elaboration table — the address is stable and meaning per address changes with the
   engine. **Default (a):** identity hashes presentations; a stable address with drifting
   meaning is the trap the CAS estate recorded. Cost: none now.
2. **Callback kinds.** Freeze the name tables; refuse `SchedName`/`LookupName`/`TTLName`; pure
   callbacks with capture wait for the term carrier below `Machine` (check `Data/Term.lean`
   first); effectful bodies are captures. **Default: yes.** One follow-up: who moves the term
   carrier, and when (after A3).
3. **Timer decision shape.** `advance (by : Nat)`, staged fires, one new `RunInterp` field,
   Bridge/Fuzz/Avatar retouch accepted, phantoms separate. **Default: yes.**
4. **Scheduler surface as its own slice** (wider `Task`, addressable dispatcher, coalescing
   guards) between A3 and A4, since every family after Deferred needs it and it is a core
   change. **Default: yes**, short, before Queue; A4 may land on the current surface if timers
   only need `due`.
5. **Refused replay and partial state.** A refused decision returns the machine at refusal and
   the position, operational only; no observational-equality claim over refused runs.
   **Default: yes.**
6. **Alphabet changes bundled with the first tape touch:** `Outcome.defect`, `Ann ≠ Unit`,
   `CauseTerm.done`, op `site`, `annotate`. **Default: yes**, all append-only, at X2.
7. **Cross-host failure equality as a product requirement.** **Default: no**; `both`'s order is
   scheduler-dependent and recorded as a divergence row; no canonicaliser.
8. **0.1 daemon engine.** `ocaml/link` now; generated engine in parallel. **Default: yes**
   unless 0.1 must ship a JS host.
9. **Frontier resource semantics.** A frontier is a third outcome, live and resumable; open
   scopes are *reported* in the receipt, not closed; a daemon `abandon` operation (interrupt
   the root, flush) is what runs the finalizers. **Default: yes.**
10. **Memo store necessity.** Keep `St.memo` (rc.112 memoisation is observable across
    `provide` sites); verify during A3 with one program that provides the same layer twice.
    **Default: keep.**
11. **Injection shape.** (a) answers to foreign rows on the tape; (b) `RunDecision.inject
    (program : address)` after X2. **Default: both, in that order.**

## 4. What retired the predecessors (X §"learned the hard way", kept short)

Not a proof and not a trap: a ratification queue growing faster than the rulings, and eight
parallel lanes against an unfrozen carrier producing eight incompatible checkers. The
direction's seat protocol (§4) and deferred list (§5) are the instruments against both.
Two disciplines worth adopting now: mutation-test every gate once (break the guarded thing,
confirm red); grade the artifact, never the run status.
