# The engine — shared brief for the design and build seats (2026-09-08)

Owner's ask, verbatim: *"coordinate a team of crack opus 5 max agents to design and build a
low level stupid fast engine for handling the math, state, persistence, caching, queueing,
query for running fiber machines."*

This file is the context every seat reads first. It says what the engine is, what it must
agree with, what already exists, what is ruled, and how the work is split. Seats write their
own documents beside it; nothing here is optional.

## 1. What the engine is

The OCaml host runtime under the Lean fiber machine: the part of the system that, for a
running `RunMachine`, holds its state, persists it, caches what is content-addressed, queues
work and wakes, and answers queries — fast. It is **not** a second interpreter. The semantics
are Lean's (`src/Effect4/Machine/Fibers.lean`, `Stores.lean`, `Api.lean`); Lean's compiler IR
is already translated into OCaml as the one engine (`ocaml/gen/api_gen.ml`, 475 declarations,
`api_run`/`api_replay`, agrees with Lean on the corpus; generalization ruling 2026-09-07:
**one OCaml engine = `gen/`**, the avatar is retired estate). What is slow in that engine is
the *carriers* it inherited from Lean — `List` for every store, `trace ++ events` on every
step (Θ(steps²)), `find?` + `map` over the fiber list per command — and what is missing is
everything around it: durable storage, caching, queueing across machines, and query.

So the engine is six components plus the seam that lets the generated code use them:

| component | what it holds / does | seat |
| --- | --- | --- |
| **math** | the 63-bit `Nat` profile (saturating `pow`, literals ≥ 2^62, `n / 0 = 0`, `n % 0 = n`, guarded shifts); SHA-256 (the content address is `sha256` of canonical bytes, `Store/Digest.lean`; OCaml's stdlib has only MD5); the hex codec; be64 framing; the ordinal tables | A1 |
| **state** | persistent carriers behind the generated code: fiber table, trace, per-family cell stores (refs, deferreds, scopes, memo world), dispatcher buckets — `Map.Make(Int)`-class, persistent, snapshot = the value | A1 |
| **persistence** | the CAS on disk (grow-only nodes keyed by digest; flat bytes `tag :: be64 length :: payload`; kinds; roots plane moved by compare-and-set on a version; the ordinal ledger as stored tables), the append-only log/WAL with a checksummed length prefix, the control file, snapshots/checkpoints as CAS nodes, crash consistency | A2 |
| **caching** | a bounded Cid-keyed node cache (bytes and decoded), the memo world's parent-chain lookup, the subterm index (`TreeSig`), dependents index | A2 |
| **queueing** | dispatcher priority buckets (persistent FIFO per priority), the due-resume queue and its family order, the timer store as a persistent priority-search queue keyed `(deadline, seq)`, the wake protocol (`WakePhase : Nat`, cancelled-waiter owes one wake), cross-machine mailboxes/inbox/ring (mutable, host-level — the existing `ocaml/link/e4_{mailbox,inbox,ring,quiescence}.ml` shapes) | A3 |
| **query** | indexes over the log (trace index → event; fiber → rows; scope → open/close; token → park/answer), by-Cid / by-occurrence / by-path lookup, `replaySteps` (the machine at position *i*), "free rows" (queries that cost no fuel and never reach the tape) | A3 |
| **the seam** | how the generated `api_gen.ml` calls the carriers without hand edits: the LCNF generator's extern table + functor/`.mli` emission (probe §4.3, ~70 lines Lean in `src/OCaml5/{Lcnf,Ml,Tools}`), or a hand-written `RunInterp`/store driver over the generated types — A1 decides which, with evidence | A1 |

"Stupid fast" means: sub-quadratic in steps for every workload, O(log n) or O(1) per store
op, no allocation on the hot path that a persistent update does not require, and measured —
the probe's bench matrix (`2026-09-07-probe-stores-performance.md` §6.2, W1–W4) with steps/s,
words allocated, and snapshot bytes per cell. Route 1's numbers are the floor to beat
(§6.3: 302 298 steps/s single machine `pFork` evaluate+flush; 114k → 512k steps/s over 1 → 8
domains at 200 machines).

## 2. What it must agree with (non-negotiable)

1. **The Lean machine is the semantics.** For every program in the corpora and every tape,
   the engine's outcome, exits, fiber table and trace rows equal `Effect4.Api.run/replay`'s.
   The oracle in-process is `api_gen.ml` as generated (List carriers); the oracle across
   faces is the Lean side (`harness/truth`, `ocaml/eff/goldens`, `ocaml/goldens/eff`, the
   avatar corpus `ocaml/avatar/corpus/programs.txt` 158 programs). A differential is the
   evidence; a claim without one is not a result.
2. **Identity is canonical bytes** (proposals §0.2). The address of anything is the SHA-256 of
   its canonical bytes as Lean computes them (`Store/{Canonical,Word,Node,Digest,Digits}.lean`,
   `Program/Wire.lean`; `ocaml/eff/eff_wire.ml` is the exact OCaml reader/writer for programs).
   No second encoding is ever hashed. Sexp is a human face beside bytes, never an identity.
3. **Saved machine states hold no mutable structure** (A2 ruling; probe D1(b)): everything in
   `RunMachine`/`RunFiber`/`Stores` is persistent; `Hashtbl`/`Buffer`/`Queue` may live only
   inside one step or at the host level (mailboxes), never in a snapshot.
4. **The scheduler makes no off-tape choice** (INV-TAPE-1). Every decision is on the tape;
   free rows are exactly the queries that never reach it.
5. **The 63-bit host profile** (`ocaml/gen/NOTES.md` §5): saturate, never wrap; `2^62` and
   above are refused at the wire (`eff_frame.ml`); jsoo is 32-bit and wasm 31-bit —
   `decode_nat` bounds from `Sys.int_size`.
6. **Append-only alphabets**: constructor ordinals are positions in a content table; a
   reordered inductive must be refused, not silently renumbered (proposal 1; CAS amendment
   M17 "every ordinal in canonical bytes is a position in a content table").
7. **Dependencies**: stdlib only inside `ocaml/gen` forever; hand code in the engine is
   stdlib (`unix`, `bigarray`, `threads`) unless a *measured* need names one package from the
   allowlist (`psq 0.2.1` is installed in the switch). Base/Core not before the wasm question
   is settled. No ppx. Zero third-party edges exist in the estate today — keep it that way
   unless you can show the number.
8. **Files you may not touch**: `src/Effect4.lean`, `Test/All.lean`,
   `Test/Audit/AxiomGate.lean`, `lakefile.toml`, anything under `src/Effect4/` (the Mac owns
   the core Lean tree this week: join commit 5 is in flight there), `ocaml/gen/*_gen.ml`
   (generated; regenerate through the generator or leave alone), `ocaml/avatar/*` (retired).
   Lean edits are allowed only under `src/OCaml5/{Lcnf,Ml,Tools}` and only by the seat that
   owns the seam.

## 3. What exists (read these before designing)

| thing | where | note |
| --- | --- | --- |
| the generated engine | `ocaml/gen/api_gen.ml` (`api_run`, `api_replay`), `ocaml/gen/api_check.ml` (G0 smoke), `ocaml/gen/NOTES.md` | build/test: `wsl -e bash -lc 'eval $(opam env --switch=effect4 --set-switch) && cd /mnt/c/Users/kokok/Dev/lean4-effect4/ocaml && dune build gen && dune build @gen/runtest'` |
| the program IR library | `ocaml/eff/` (`eff_types`, `eff_wire`, `eff_frame` with `Val` frames tags 11/12, `eff_json`, `eff_typed`, goldens), `ocaml/eff/README.md` | the exact wire; the corpus programs as bytes; **note** `eff_types.eff` and `api_gen`'s `eff` are two OCaml types for one Lean type — the engine needs one conversion or one generation |
| route 1 host core | `ocaml/link/` (`e4_mailbox`, `e4_inbox`, `e4_ring`, `e4_quiescence`, `e4_worker`, `e4_router`, `e4_host`, `e4_bench`), `link/README.md`, `link/REPORT.md` | the daemon shapes and the baseline numbers; property lists at file heads are the house style |
| the hot-path probe | `docs/research/2026-09-07-probe-stores-performance.md` | **the prior design of the seam** (§4: what may be substituted and why it is safe, the `STORE`/`FIBERS`/`TRACE` signatures, the `Extract Constant` mechanism already in `Lcnf/Translate.lean`), the bench matrix (§6), the plan P0–P10, owner decisions D1–D6 (defaults: D1(b), D2(a) then (b) on measured need, D3(b), D4(b), D5(b)) |
| the OCaml reviews | `2026-09-07-ocaml-{proposals,deps-tradeoffs,ecosystem-survey,tooling-review}.md` | proposals 1–24 ranked; the daemon rows (15–21) and CAS rows (22–24) are inputs to A2/A3 |
| the CAS design | `2026-09-07-cas-design.md`, `2026-09-08-cas-amendments.md` (M1–M18), `2026-09-08-cas-knockon-work.md`, `2026-09-08-cas-attacks.md`, `2026-09-08-cas-repository-algebra.md` (`TreeSig`, T1–T3), `2026-09-08-effectful-repository-notes.md` (Unison comparison) | the three identities (`Cid`, node `Ref`, `Occurrence {program, path}`), kinds 16–22 + `table`, pins at publish, tables as content, the subterm index |
| the Lean CAS | `src/Effect4/Store/*.lean` (`Store.lean`: grow-only nodes keyed by digest, admission, roots plane with CAS-on-version; `Digest.lean`: SHA-256 via lean4-hash; `Canonical`/`Word`/`Node`/`Digits`) | read-only; the OCaml persistence must reproduce `Node.encode` and the admission order byte-for-byte — goldens must be cut from Lean (ask the coordinator; one Lean process on this machine) |
| the Lean stores | `src/Effect4/Machine/Stores.lean` (`Stores = {refs, deferreds, scopes, memo, nextName}`, `syncOpStep : SyncOp → Stores → Option (Stores × Val)`), `Program/Sched.lean` (`FiberOp`, the term scheduler's signature) | read-only; the field-by-field carrier map |
| the design language | `2026-09-08-design-language.md` | the reading axis is the trace index; the query API must serve it (§3, §6.4: the owed log rows, `replaySteps`) |
| the build path | `2026-09-08-build-path.md` | where the Mac is; what is parked |

## 4. Rules of work on this machine

- **PowerShell only** for shell; the Bash tool is denied. WSL commands go through
  `wsl -e bash -lc '<single-quoted command>'` with `eval $(opam env --switch=effect4 --set-switch)`
  first; the repo is `/mnt/c/Users/kokok/Dev/lean4-effect4` from WSL.
- **OCaml builds** are cheap and unbounded: `dune build`/`dune test` in WSL as often as needed.
  A new project goes under `ocaml/engine/` (library `effect4_engine`) and is added to
  `ocaml/dune`'s `(dirs …)` by its build seat.
- **Lean is one process per machine.** Before any `lake` or `lean` command: create
  `.lake/LANE.lock` with your seat name; if it exists, wait. Always `$env:LEAN_NUM_THREADS=3`
  and `-M4096`. Delete the lock when done. Design seats do **not** run Lean.
- **Scratch** goes under `C:\Users\kokok\AppData\Local\Temp\claude\C--Users-kokok-Dev-lean4-effect4\cb8f3540-da84-4adf-a734-96212df0dcb5\scratchpad\<seat>\`
  (`/mnt/c/Users/kokok/AppData/Local/Temp/claude/C--Users-kokok-Dev-lean4-effect4/cb8f3540-da84-4adf-a734-96212df0dcb5/scratchpad/<seat>/` from WSL). Probes are welcome there.
- **Do not commit.** The owner commits. Leave the tree building.
- **Every number behind a command**; every claim about the repo as `file:line`; every
  library fact with its source. Property lists at file heads (`ocaml/STANDARDS.md`).
- **No ceremony**: no "what proof means" essays. Interfaces, laws, code, tests, numbers.

## 5. The split

**Phase A — design (three seats, parallel, read-only on the repo; probes in scratch):**

- **A1 state + math + seam + drive + bench** → `docs/research/2026-09-08-engine-a1-state.md`
- **A2 persistence + caching** → `docs/research/2026-09-08-engine-a2-persistence.md`
- **A3 queueing + query** → `docs/research/2026-09-08-engine-a3-queue-query.md`

Each design document delivers: (1) the `.mli` of every module it proposes, complete; (2) the
laws each carrier must satisfy, and which Lean theorem or corpus differential licenses the
substitution; (3) the file-ownership map for the build lanes (disjoint files, one lane per
module group); (4) the tests (unit, property, differential) and the bench cells with
acceptance numbers; (5) risks and the questions only the owner can answer, with a default
for each; (6) what it measured in scratch, with the commands.

**Phase B — build (lanes of two or three at a time on disjoint files, tests green in WSL).**
**Phase C — the differential over all corpora and the bench matrix; one receipt.**
