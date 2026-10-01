# Build path — updated 2026-09-08 (after join commit 4)

Supersedes `2026-09-07-plan-review-after-join3.md` §3. All core Lean work runs on the **Mac
seat** for now; the PC holds the merge and the tooling lanes parked until the owner reopens
them. One Lean driver per tree; two seats maximum.

## 1. Where the trees are

| Tree | Head | State |
| --- | --- | --- |
| origin/main | `4d7c34e` join commit 4 (layers by path) | pushed from the Mac |
| Mac | `4d7c34e`, clean | commit 5 started, **paused** |
| PC | `7d53312` = `4d7c34e` merged with the PC lanes `9cfd213` (frame kernel tags 11/12; generated engine at `Api`; known-red policy; `tools/Effect4Gen/{manifest.json,Driver.lean}`) | built green (376 jobs, 44,989 declarations, gate `[propext, Quot.sound]`, 7/41); the Lean driver regenerates `Program/Derived.lean` byte-identically through the manifest that now carries the three `ServiceKey` types; **not pushed** |

**2026-09-08, later:** the PC is now three commits ahead of origin — `7d53312`, then
`f276d4e` (the LCNF generator's extern table + functor emission; `api_gen.ml` regenerated
from HEAD; `effect4_eff`/`effect4_gen` public) and `b7fc49c` (`ocaml/engine`: the host engine
— carriers, CAS, WAL, queues, scheduler, query; 148 612-comparison differential at 0
divergences; see `2026-09-08-engine-build-packet.md`). All three need pushing; none touches
`src/Effect4/`, so the Mac's commit 5 pulls them fast-forward.

**Commit 5 needs the PC lanes on the Mac**: its regeneration should go through the portable
driver (`lake env lean --run tools/Effect4Gen/Driver.lean --group <G> --verify`), which lives in
`9cfd213`. So the order is: push `7d53312` → Mac `git pull` (fast-forward) → resume commit 5.

## 2. Commit 5 on the Mac — the checklist, updated

**What is already in the Mac's working tree (paused, uncommitted, 319 lines over four
files):** the compile-route witnesses the coverage re-point needs, written before the rows are
edited — `Program/Agreement.lean` §joinWitnesses (`compileLayer_*` per constructor arm,
`currentMemoMapOf_*`, `regionCode_*`, the `*K` reader equations `buildWithScopeK_context`,
`serviceLookupK_found/missing`, `provideThenK_context`, `combineWithK_provide/provideMerge`,
`updateThenK_context`, `mergeContextsK_contexts`, `provideLayerWithK_at`,
`provideLayerBodyK_context/exit`, `finalizerProgram_scopeClose`, `enterScoped_eq`,
`exitScoped_restores`), `Machine/StoresLaws.lean` (the finalizer names as programs:
`finProgram_closeChildOnFailure_*`, `finProgram_memoEntry/memoDone`,
`contAOf_closeIfLast_scope`), `Machine/Stores.lean` (`MemoWorld.get_own/get_parent`), and
`src/OCaml5/Eff/World.lean` adding `LayerTerm` (`layer_term`) to the `Eff` block — so the
OCaml world already knows the new family member, which lane 7's sexp printer and the engine
regeneration depend on. Each carries its `census:` row tag; not yet built on the Mac (no
receipt). Items 1–5 below are what remains.

From `2026-09-07-join-dispatch.md` §5 as amended by what commit 4 landed:

1. **Regeneration, once.** `Program/Derived.lean` is already regenerated (commit 4) — verify
   with the driver (`--group Program --verify`, expect `same`). Avatar `Derived/{Context,
   Layer,Stores}.lean` regenerate once through their own tool (`src/OCaml5/Tools/Describe.lean`);
   `Avatar/Check.lean`'s projection pin (44, V1-12) is restated to the new count with the note
   removed. The avatar is retired estate: drift beyond the pinned rows is recorded, not repaired.
2. **The Layer machine retires.** `Machine/Layer.lean`'s remaining copies and its import in
   `src/Effect4.lean` (coordinator-owned root); the 42 guards are already re-homed on the
   compile route by commit 4 (the five `finalizerOr` ones re-spelled). Delete, do not merge.
3. **Coverage rows, edited never added** (frozen 137/135): `scope.acquire-release`
   (`RuntimeCoverage.lean:5774`, `separateCalculus` → installed; witnesses →
   `Intro.lean`'s `release_intro`/`foreignRelease_intro`/`acquireIn_intro`),
   `scope.add-after-closed` (`Scope.closingExit_addUnsafe`), the 18 `Layers.*` rows re-pointed
   at the compile-route restatements (`layer_intro`, `layerBuild_intro`, `denoteLayer`). Needs
   `import Effect4.Program.Intro` in the coverage module (root-adjacent; coordinator).
4. **Records.** DB-11 and DB-12 do **not exist yet** (`DESIGN-BASIS.md` ends at DB-10): write
   them — DB-11 one carrier, images, admission status "theorem premise; executable at X2";
   DB-12 one context with services, layers as program subterms addressed by path, memo keys
   are paths, no layer table. `ARCHITECTURE.md` module map (`ContextMap`, `Layer` gone).
   Register rows citing `Layers.*` re-point; CE-013/015/016 to installed-repair text.
5. **Receipt** `docs/research/2026-09-07-join-delivery.md` (base/head, files, commands, what was
   not run), and one finding to carry to the grill: **memo hits are unreachable from printed
   programs under path identity** (rc.112 keys the memo map on the layer object; commit 4
   message), so `pProvideTwice` pins the protocol, not a hit — grill call 10 ("keep the memo
   store; verify with a provide-twice fixture") is **not yet decided by a fixture**. The
   repository seat's T3 (build order-independence) and #9 (memo-world confluence) are the
   theorems that would settle whether `St.memo` is derivable.

## 3. After commit 5, on the Mac, in order

| # | Slice | Packet | New inputs folded since it was planned |
| --- | --- | --- | --- |
| 1 | **Scheduler surface** — wider `Task` (two constructors vs seven library shapes), addressable dispatcher, `WakePhase : Nat` on the due drain, cancelled-waiter disposition (a cancelled waiter owes one wake), coalescing guards, the `Delay` reply as Queue's signal-then-repoll | to compose (coordinator) | grill rulings 3/4; `lit-siblings` Q5 fixtures from the WHATWG streams contracts; `ocaml-ecosystem-survey` #1, #17, #23 |
| 2 | **A4 timer** — `Stores.timers` as a `Psq` instance keyed by `(deadline, seq)` (`Lib/Psq.lean` spec), rows `sleep`/`clockNow`, decision **`advance (by : Nat)`** with one new `RunInterp` field, staged fires; no `clockAdjust` (refusal R2); phantom `ν σ` removal a separate sweep | to compose after 1 | `psq 0.2.1` installed; timer refusal rows; the score's clock staff (design language §2) |
| 3 | **X2** — the external row (`Row.registration`, `EffName.external`, `requestOf` projection from the parked frame); executable admission at `Api` (`replayChecked`, refused decision returned with the machine and position, operational only); the run-relative kinds as **bytes from hand images** (amendment M2), `job : Ref Job` on each; the five append-only alphabet changes (`Outcome.defect`, `Ann ≠ Unit`, `CauseTerm.done`, op `site`, `annotate`) in one touch; the log rows the design language owes (`scopeOpened/Closed`, `finalizerRegistered/Ran`, the awaited row at a park, the Point at an event, frames as rows, the tape in the manifest); `Api.replaySteps` (~40 lines, the viewer's one real need) | to compose after 2 | `2026-09-08-design-language.md` §3/§6.4/§9; `cas-amendments` M2/M5/M6; INV-TAPE-1/2 written into DB-12 |
| 4 | **CAS lane (Opus)** on `2026-09-08-cas-amendments.md` §2 with **M17/M18**: commit 1 kinds (16–22, sentinel 127, plus a `table` kind), 2 scheme, 3 `Cid` (kind-aware `byCid`), 4 program-as-content, **6 subterm index via `TreeSig`** (the rose-tree signature from `cas-probes/repo2-operad.lean`, emitted by the generator; retires the hand `argIndex` table), 5 occurrence with `ProgPath`/`ValPath`, 7 run objects, 8 registry + pins + `prev` check, 9 batteries/DB-12; **tables as content** (`WireKey`/`KeyTable`/`resolve` in `Key.lean`, `keyOf` over a supplied table, the ordinal ledger as a stored `table` node) as its own commit before anything is published | ready; runs on whichever seat is free | `cas-repository-algebra.md` §3.5, §6; probes at `docs/research/cas-probes/` |
| 5 | **H1 daemon** on `ocaml/link` — `Bridge.lean` takes canonical decisions/checkpoints as hex; `run`/`replay` in `e4_router`/`e4_host`; ordered shutdown + `abandon` under a finalizer fuel budget (new ruling); Eio for transport/timers only; sexp faces beside bytes; version handshake + checksummed length prefix; keep the mutex mailbox | after 3 and CAS 1–4/8 | `ocaml-proposals.md` §3 H1 rows; `cas-amendments` M1 (pins at publish), M9 (63-bit refusal row) |
| 6 | Queue → permits/gates → PubSub on the wake protocol; `TxRef` as its own subcalculus | after 2 | `lit-siblings` Q5 |

## 4. PC lanes — parked until the owner reopens them

| Lane | Content | Status |
| --- | --- | --- |
| 4 wire discipline | ordinal ledger (**now: a stored `table` node per alphabet, rule "every ordinal is a position in a content table"**, must cover `NativeOp`); manifest digest in tape/snapshot headers; `decode_nat` from `Sys.int_size`; `Lib/Deque.lean` → `Core.Fdeque`, retire `W4-DEQ-CAPACITY` | briefed, not dispatched |
| 5 engine surface | `.mli` for `api_gen`; **emitter-generated `sexp_of`** (no ppx in `gen`) | after 4 |
| 6 hygiene | `.ocamlformat`+ignore, warnings policy, `@check` gate, repo-root `dune-project`, `failwith` for ⊥, div-by-zero row, promote transcripts | briefed, not dispatched |
| 7 sexp-native Eff, Lean half | `Codegen/Sexp.lean` printer/reader for `Eff`/`Val`/`Decision` (must cover the three new constructors + `LayerTerm`); snapshot as sexp; `Bridge.lean` | after join 5 |
| U1c | `Config.Val := carrier` | any time |
| performance probe | the List carriers measured on `api_gen` | any time |

## 5. Research folded into the path since the last review

- **Design language** (`2026-09-08-design-language.md` + §9 string-diagram fold-in): the
  score/tape/enclosure notation; hue for four agents only; the naming-fix table (§5.2:
  `started→entered`, `fire→drain`, `Point.tape→choices`, `promise→deferred`, …) goes to the
  grill as one item; the owed log rows go to X2 (above).
- **Repository algebra** (`2026-09-08-cas-repository-algebra.md`): the repository is the free
  multicategory of contexts over the `Eff` signature; grafting laws proved (`TreeSig`);
  **M17** tables as content; levers **T1** (machine congruence over grafts), **T2** (renaming
  invariance), **T3** (build order-independence under `NoShadow`); canonical forms modulo
  D-DEFORM stay a view. Programmes P1–P5 (§8) are the post-immediate direction.
- **Unison companion** (`2026-09-08-effectful-repository-notes.md`): our `Cid` is Unison-shaped
  except for ordinal encoding; dependents index yes, `propagate` no; store the term, not the
  expansion.
- **CAS** amended (M1–M18); knock-on register (68 rows); adversary (4 breaks, all resolved in
  the amendments; all seven open statements true).
- **OCaml**: proposals (24 rows), dependency trade-offs (Base fails under wasm at runtime;
  `Core.Fdeque` is the persistent deque), ecosystem survey (Riot `Delay`, data-encoding tags,
  irmin control file, `Psq`, ordered shutdown).

## 6. Owner calls still open

1. Push `7d53312` (unblocks commit 5's driver-based regeneration on the Mac).
2. CAS: M1 pins at publish; M2 two kind classes; **M17** the unit `(bytes, keys)` and a
   `table` kind. Defaults: yes.
3. The naming fixes (design language §5.2) — one grill item.
4. Grill call 10 (memo store) reopened by the commit-4 finding; default stays "keep", settled
   by T3/#9 rather than a fixture.
5. When the PC lanes reopen, and whether the CAS Opus lane runs on the Mac after X2 or on the
   PC in parallel.
