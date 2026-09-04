# Seat F3: OCaml as runtime and workhorse, criticised against the current Deep model

Status: 2026-09-04, seat F3 at `625a207` (Mac; the PC is still editing — an untracked
`Effect4Test/Deep/Volume.lean` and possibly more repairs). Read for this note: the second
Deep review and its four repair steps (`64857bb`..`8a51d95`), the three plans (`625a207`),
`Effect4/Deep/*`, `Effect4/Runtime/Runtime.lean`, `Effect4/Syntax/{Eff,Compile}.lean`, the
coverage join, the OCaml5 estate (avatar, daemon, `Ml/`, `Lib/`, `Effect.lean`), the
`Effects` algebra, and the vendored rc.112. Every claim cites a file and line at that commit.

## 0. The recommendation, in three lines

1. **The compiled Lean Deep machine is the reference executor** and the Lean face of the
   observation platform; the avatar is a *second runtime*, judged as a fourth face of the
   same wire, never "the runtime representation of Deep".
2. **Keep OCaml where it is native** — the effects-native avatar as a runtime and the jsoo
   product path — and *derive* everything of it that is first-order (carriers today, the
   machine-level functions next), leaving the frame hole hand-written under a pinned
   divergence table and a Lean-hash drift gate.
3. **The free-monad embedding is the program-level bridge** for OCaml-authored programs
   (Path C), not a model of Deep; it is packet three, not one.

## 1. Is the arm-for-arm hand port the right mechanism?

**What the estate has.** The carriers are generated: `Render.lean`'s SEAT W1 section
(`workshop/OCaml5/Render.lean:1293`) describes every `Stores`/`Context`/`Layer`/`ForkFlow`
carrier as a `StructDesc`/`InductiveDesc` and `render-deep.sh` diffs the rendered block
against the file (`workshop/OCaml5/avatar/render-deep.sh:33-56`), 129 `#guard`s pinning
constructor counts and field orders. The *functions* are hand-written, one OCaml declaration
per Lean declaration with the Lean line cited (`deep_fibers.ml:718`, `:755`, `:809`, `:1035`,
`:1110`, `:1169`). F2 checked thirteen review findings arm for arm and found every one carried
by the avatar (`2026-09-04-seat-w1-deep-port.md:530-549`, "carried it? yes" on R2-1, 2, 5,
9, 10, 3, 4, 12, 13, 7, 8, 11; half on R2-6) plus two of its own (F2-1, F2-2, `:554-557`).
Today the counts have drifted again: `Clauses.lean` has 132 theorems and the avatar 126,
`Witnesses.lean` 62 and the avatar 60, and `extract-census.py --check` reports six rows changed
(`E4-RUN-CE-038/039`, step 4b). That is the mechanism's steady state: the avatar lags the Lean
model by one repair wave, always.

**What the Deep definitions are.** `Fibers.lean` is total, first-order and fuel-bounded:
`drive` recurses on fuel (`Effect4/Deep/Fibers.lean:1160-1236`), `flushAll`/`flushRoot` on
rounds (`:1279-1298`), `countdownWalk` and `Dispatcher.insert` on lists (`:593-603`,
`:127-133`); no `partial`, no `unsafe`, no `implemented_by` anywhere under `Effect4/Deep/`
(grep). The bodies use `match`, `let`, `{ f with … }`, `if`, `List.foldl/filter/map/find?/
contains/all/flatten`, `Option`, `decide` and `where` locals — exactly the fragment
`OCaml5.Ml.Syntax` already spells (`workshop/OCaml5/Ml/Syntax.lean:285-361`: `letIn`,
`matchE`, `record`, `recordWith`, `field`, `setField`, `ifThen`, `listLit`, `fn`, `app`) and
`Ml.Passes.mutate` already rewrites (`workshop/OCaml5/Ml/Passes.lean:12-30`, the linear
`{ f with }` → `f.x <- v` pass with its residue checker). The type parameters
`ν σ β ε δ ι α χ St` are fixed by the profile's substitution table (`Render.lean:1355-1395`),
which is what a transpiler would read instead of a human.

**Price of a Lean→OCaml transpiler for the Deep fragment.** Two routes. (a) *Kernel-level*
(`ConstantInfo` → `Ml.Expr`): must undo `matcher` auxiliaries, `brecOn`/`WellFounded.fix`,
instance arguments and `Decidable` — weeks, and W3 already priced the elaborator as "the one
piece that would make generated true" and left it out (`2026-09-04-seat-w3-ml-api.md:411-417`).
(b) *Syntax-level* (`Lean.Syntax` of each `def` → `Ml.Expr`): the Deep files are written in a
disciplined subset, so a driver that parses `Fibers.lean`, walks `def f … | pat => body` /
`match` / `let` / `{ x with }` / application, and maps `List.*` through a named table (the
profile's `LibVal` rows, `Ml/Profile.lean:174-215`) is two to four days for the fragment, with
an explicit residue list. Done-when is the carrier discipline applied to functions: the rendered
group diffs byte-identical to the hand port after `mutate`, and `render-deep.sh fibers` runs
in `run-witnesses.sh`.

**What would not transpile, and how to hole it.** The avatar's thesis is DIVERGENCE 1
(`deep_fibers.ml:8-15`): `FrameFiber.current : Prim` and `.stack : List Prim`
(`Effect4/Runtime/Runtime.lean:274-285`) *are* the OCaml 5 stack — `control = Program | Onstack
| Suspended kont | Failing | Ended` (`deep_fibers.ml:219-226`). Everything that builds or
inspects a `Prim` tree is therefore a hole: `evaluatePrim`'s arms (`Fibers.lean:771-848`),
`finalizerOr`/`stepFrame` (`:853-891`), `withFiber`'s program-carrying arms (`:903-929`,
`:957-981`), the parks' pushed `asyncFinalizer` frames (`:623`, `:796`, `:822`, `:971`),
`Stores.lean`'s `progOf`/`contAOf`/`contEOf`/`actionOf` (`Effect4/Deep/Stores.lean:1088-1309`;
the avatar refuses the three continuation tables structurally, W1-9), and every `RunInterp`
field that returns a `Prim` (`Fibers.lean:370`, `:373`, `:390`, `:393`, `:409`, `:420`). The
whole `Runtime.lean` frame machine (`step`, `:2384-2443`; `run`, `:2450`) is the hole's other
half. `Cmd.loop`/`deliver`/`finish` have no OCaml existence (DIVERGENCE 2, `deep_fibers.ml:17-21`,
`:471-480`). The hole is the one A0 asked P5 for (`2026-09-04-spike-a0-avatar.md:55-58`).

What *does* transpile is the machine-level, `Prim`-free group: `Dispatcher.*` (`:125-144`),
`RunMachine.*` incl. `arm`/`disarm` (`:446-500`), `interruptRecord` (`:550-571`; one hole,
`current := Prim.failure`, which the avatar spells as three cases, DIVERGENCE 8),
`interruptEach` (`:577-587`), `countdownWalk` (`:593-603`), `spawn`/`start`/`launchEntrant`
(`:658-696`), `linkScope` (`:702-731`), `runloopTop`/`countOp`/`yieldVerdict` (`:735-748`),
`fireObserver` minus the `resumePrim` answer (`:1044-1106`), `exitFiber`'s store branch
(`:1126-1137`), `settle`'s dispatch (`:1142-1156`), `drive`'s command arms other than `loop`/
`deliver` (`:1168-1236`), `fire`/`flushAll`/`flushRoot` (`:1263-1298`), `runFork`/`runCallback`/
`runSyncExit`/`promiseOutcome` (`:1330-1366`). Of F2's thirteen carried findings, nine live in
that group (R2-2 `exitFiber`, R2-4 `countdownWalk`/`fireObserver`, R2-5 `interruptEach`, R2-8's
`Cmd.link`, R2-9 `linkScope`, R2-10 `launchEntrant`, R2-11 `Cmd.launch`, R2-14/15 the schedule)
and four in the hole (R2-1, R2-3, R2-7, R2-12/13's programs). A transpiler halves the drift
surface; it does not close it. It is still worth it, because the half it closes is the half
that drifts silently (an ordering, a flag, an annotation), while the hole drifts loudly (a
missing arm refuses by name, `deep_fibers.ml:496-499`).

**Verdict.** Hand porting is the wrong steady state for the derivable half and the only
possible state for the frame hole. Derive the half; pin the hole.

## 2. The monadic linkage

The Lean side has `Effects.Program` — `pure | vis (op) (Answer op → Program)`
(`/Users/pooks/Dev/lean4-effects/Effects/Algebra/Program.lean:33-38`) — with `Handler`
(`Handler.lean:30-33`), `interpret` by structural recursion (`:45-48`), `interpret_bind`
(`Laws.lean:72-81`), `eq_of_all_interpretations` (`:116-125`) and `IsMonadMorphism`
(`Universal.lean:28-36`). The Deep machine is not stated over `Program`: it runs `Prim` trees
(`Runtime.lean:100-146`), and the bridge from `Program` to frames is `FrameSimulation.compile_simulates`
on the compiled fragment only (`docs/TRACE-DAG.md:50`). `Eff` (`Effect4/Syntax/Eff.lean:266-306`)
is first-order and `DecidableEq`; `compileEff` (`Effect4/Syntax/Compile.lean:280-356`) makes
names into points and `interpOf` (`:625-734`) gives them meaning.

**The OCaml sketch.** The generator (`Ml.Reflect`, `workshop/OCaml5/Ml/Reflect.lean:96-140`)
renders a `Signature` as a GADT-free pair and `Program` as a variant with one closure field:

```ocaml
(* rendered from Effects.Signature / Effects.Program by OCaml5.Ml *)
type ('op, 'ans) signature = { answer_of : 'op -> 'ans }         (* a code, not a type *)
type ('op, 'ans, 'a) program =
  | Pure of 'a
  | Vis of 'op * ('ans -> ('op, 'ans, 'a) program)
type ('op, 'ans) handler = { handle : 'op -> 'ans }               (* M = the avatar's effects *)
let rec bind p k = match p with Pure a -> k a | Vis (op, next) -> Vis (op, fun a -> bind (next a) k)
let rec interpret h = function Pure a -> a | Vis (op, next) -> interpret h (next (h.handle op))
let perform op = Vis (op, fun a -> Pure a)
(* the avatar as a handler: an operation is one perform on the fiber's own stack *)
let avatar_handler : (store_request, value) handler = { handle = fun req -> Effect.perform (Op_store req) }
```

Answer types are indexed in Lean (`Signature.Answer : Op → Type`, `Signature.lean:31-33`); in
OCaml without a GADT they collapse to one `'ans` — which is exactly what the avatar already
does with `value` (`deep_fibers.ml:64-73`) and what the trace wire does (`Effects.Trace.Val`).
A GADT `('op, 'a) op` would keep the index but leaves `Ml.Syntax`'s fragment (`Ml/Syntax.lean`
lists GADT constructors as syntax only) and W3's checker.

**What it buys.** (i) `bind`/`interpret` are three-line structural recursions, so they *are*
the transpiled image of `Program.bind` and `interpret` (`Program.lean:43-46`, `Handler.lean:45-48`)
— the one place where "Lean equality transfers by construction" is literally true, because
the OCaml text is the Lean text. (ii) A direct-style OCaml program `let x = perform op in …`
under `identityHandler` (`Laws.lean:102-104`) is its own `Program` value: the algebra's
reification-for-free, on the OCaml side. (iii) Path C (`2026-09-04-ocaml5-state-and-paths.md:75-78`)
gets a lawful target: user programs emitted as `program` values, interpreted into the avatar's
effects by `avatar_handler`, with `interpret_bind`'s shape holding of the rendered code.

**What it costs and does not buy.** `Program` is deliberately not serializable (DB-01,
`docs/DESIGN-BASIS.md:79-88`); its OCaml image inherits that — `Vis` holds a closure, so no
content identity, no diff, no golden. Lean equalities transfer only for programs that *exist
on both sides*, i.e. those elaborated from first-order `Flow`/`Eff` — and those already have
a compile to `Prim` with the machine underneath. So the embedding relates OCaml-authored
programs to the algebra; it does not relate the avatar to Deep, and it does not replace the
`Eff → Prim` compile. One generated module plus one hand handler, about a day; value only once
someone writes Effect programs in OCaml. Packet three.

## 3. From every angle: what the estate observes and what it cannot

| angle | exists | where |
| --- | --- | --- |
| service rows (5 families, 3 masks, 2 yield settings) | yes | `generated/traces/{ref,deferred,scope,layer}`, `harness/trace/*-tail.ts`; avatar `build-avatar.sh`; 75+75 pairs (`seat-w1-deep-port.md:767`) |
| `RunEvent` trace | Lean and avatar | `Fibers.lean:268-290`; `deep_fibers.ml:337-358`, `EFFECT4_EVENTS=1` |
| daemon step snapshots, `explain`/`why`/`reachable`/`budget` | yes | `workshop/OCaml5/server/e4d_snapshot.ml:260`, `effect4_daemon.ml:629`; 19 requests, 14,677 checks (`seat-w2-daemon.md:20-22`) |
| the Eff AST and its printer | yes (reader planned) | `Eff.lean:266`, `Print.lean`; A4 reads the *printer's image* only (`a4-reader-plan.md:394-470`) |
| golden TSVs, corpus, fuzz | yes | 25 goldens; 158 corpus programs authored once, run on both faces (`spike-a0-avatar.md:754-767`); 220 P5 programs |
| jsoo/JS closures, the Promise bridge | probed | A0 §5 (`:234-274`, the C crux: a perform inside a JS callback is `Unhandled`); P6 `Await` (`spike-p6-promises.md:144-160`) |
| frame stream on the host | recorded, never compared | `harness/trace/tracer.ts:363-408` (`frames`), TRACE-DAG `bridges` open (`docs/TRACE-DAG.md:55`) |

Missing, with the cheapest OCaml-side mechanism:

1. **The frame stream R2-16..19 need** (`deep-review-2.md:106-115`; R4 §1's `prim <f> <tag>
   <depth>` rows, `r4-host-loop-plan.md:161-175`). Lean has it: `RunEvent.frame` wraps
   `FrameEvent` per fiber (`Fibers.lean:280`, `Runtime.lean:301-316`). The avatar cannot: its
   frames are the OCaml stack; `FrameEv` is declared (`deep_fibers.ml:349`) and never emitted.
   A perform-site row gives the *tag* (every `effc` arm is one primitive, `:1302-1310`) but not
   the *depth*, and pushed handler frames (`OnSuccess` under `bind`) are invisible. Cheapest
   honest mechanism: none on the avatar — the frame angle is the Lean executor's and the
   host's. Recording that as a refusal row is cheaper than faking a depth counter in
   `on_exit_program`/`masked_region` (`deep_stores.ml:839`, `:860`).
2. **Ingesting real Effect TS source into `Eff`.** A4 inverts `print` and refuses anything
   the printer never emits (`a4-reader-plan.md:400-409`). Real source needs the TypeScript
   compiler API on the node side: a script over rc.112 programs emitting `Eff` as JSON, and an
   `Eff` decoder generated by `Ml.Reflect` from `Eff.lean` (with `Lib/Sexp.lean`'s round trip,
   `2026-09-04-seat-w4-library-carriers.md:32`). Not an OCaml-side parse.
3. **Observing a running rc.112 process rather than replaying rows.** The jsoo daemon already
   runs inside node (`require("./effect4d.js")`, `seat-w2-daemon.md:24-27`), and P6 shows
   JS→OCaml calls are fine at a fiber boundary (`spike-p6-promises.md:292-303`). Cheapest:
   one node process loading rc.112 with the `Tracer.context` hook and R4's `fiber.fork`/
   `fiber.interrupt` hunks (`r4-host-loop-plan.md:304-312`), pushing each row into the daemon's
   `diff` live — a plain function call per row, no perform across the boundary.
4. **The host loop R4 names.** `deep-tail.ts` is TypeScript (`r4-host-loop-plan.md:279-315`).
   The OCaml counterpart is the avatar as a fourth face of the *same* `effect4-deep-v1` wire:
   `e4d_wire.ml` already renders masks and rows; a renderer from `run_event` to the deep rows
   is an afternoon, because the avatar's alphabet is Lean's (`deep_fibers.ml:336-358`).

## 4. Alternatives to OCaml as the workhorse

**Compile the Lean Deep machine itself.** Every `def` under `Effect4/Deep` compiles today;
`#guard`/`#eval` run the compiled code (the stress plan relies on it, `2026-09-04-stress-plan.md:24-26`).
A `lean_exe` over `Syntax.Compile` + `Deep.Fibers` + a `RunEvent` renderer that reads a
program (a `ProgName`, or an `Eff` through A4) and a tape and prints the deep wire is the
reference executor with **zero drift by construction** — the executable *is* the model. Its
known costs are the S3 items (`drive`'s recursion depth, `emit`'s `++`, `Fibers.lean:454-456`;
`s3-volume-plan.md:8-11`), which are owed anyway, and Lean's C backend is a trust boundary of
the same kind as `ocamlopt`. What it lacks: it is not a runtime anyone ships, and it has no
effects-native stack — it runs `Prim` trees, which is the point.

**Keep TypeScript as the only host and Lean as the only model.** This is where the estate
was before A0 and it is not wrong: the goldens, the corpus and R4 compare rc.112 to Lean
directly. What it loses is a *second implementation* — A0's corpus found three Lean gaps by
being one (`spike-a0-avatar.md:884-896`), and F2's re-diff is where every Lean repair was
checked against an independent reading of the same rc.112 lines.

**Where OCaml genuinely wins.** (a) Effects-native fibers: park/resume/discontinue are the
runtime's own one-shot continuations, so the avatar is a *runtime*, not an interpreter of
trees (`deep_fibers.ml:1283-1310`, `:1302-1304`). (b) jsoo to JS with a modelled compiler:
`OCaml5.Effect` (`workshop/OCaml5/Effect.lean:1-60`, 258 theorems), `Cps.lean`/`CpsProof.lean`
(77), 57/64 native≈jsoo arms (`ocaml5-state-and-paths.md:19-27`) — a JS target with three
named compilers between it and the bytes, against a runtime the census reverse-engineers
(`spike-a0-avatar.md:302-307`). (c) One language for daemon, runtime and observation, byte-
identical on three hosts (`seat-w2-daemon.md:22-23`). (d) Jane Street tooling, once the
switch is used (it is built: `2026-09-04-ocaml-packages-plan.md:31-37`; the avatar's dune
project is green, `seat-w1-deep-port.md:429`).

**Where it merely duplicates.** As a *model* of Deep it is a second, weaker copy: no fuel of
DB-04's shape (`spike-a0-avatar.md:703-737`: two bounds, the command fuel not a frontier —
W2 measured 4/14/11/14 rows at fuel 1..5, `seat-w2-daemon.md:232-238`), no `Prim`, no frame
stream, one repair wave behind. Every clause it "holds" (121 of 126) is a re-execution of a
Lean theorem that already holds by `rfl`/`decide`. The `deep_clauses.ml` battery is honest
evidence about the *avatar*; it is no evidence about Deep.

## 5. Risks

1. **Drift.** Hours behind (F2's checkpoint at `57924eb`, step 4b at `8a51d95` half an hour
   later); every bug carried; today 6/2/6 count drifts (§1). The daemon already measures
   citation drift (8 to 65 lines, `seat-w2-daemon.md:240-262`) but nothing *fails* on it.
   Mitigation: the avatar header pins the SHA-256 of `Effect4/Deep/*.lean` it was diffed
   against (`e4d_pins.ml` has the digests, `seat-w2-daemon.md:135`) and `run-witnesses.sh`
   fails on mismatch, so a stale avatar cannot report green.
2. **The op counter and `Cmd.loop`.** The avatar counts one op per *perform* (`guard`,
   `deep_fibers.ml:1393-1409`); rc.112 counts one per `runLoop` iteration over any primitive
   (`internal/effect.ts:643`), frames included. The service families agree at `MAX_OPS=3`
   because service rows are frame-insensitive (separation 8, `docs/TRACE-DAG.md:100-104`); the
   fiber family does not (`spike-a0-avatar.md:656-675`, E4-SEM-CE-011), and any witness that
   budgets a frame pop will not either. This is structural (DIVERGENCE 2), not a bug.
3. **The missing frame stream** (§3.1): R2-16..19 and R2-11b are invisible to the avatar,
   so the trace-level half of the review cannot be re-diffed there at all.
4. **The two-bound fuel** (A0 §19): a fuel-bounded avatar snapshot is "a reachable state,
   not a prefix" (`seat-w2-daemon.md:237-238`), i.e. DB-04's monotonicity
   (`docs/DESIGN-BASIS.md:166-171`) is false of the avatar's `drive`. A3's relation must be
   indexed by `(fuel, ops)` and nobody has written it.
5. **The profile's refusal rows.** 15 of 20 admitted modules have no Lean carrier
   (`seat-w3-ml-api.md:184-215`; `Ml/Profile.lean` has four `carrier := some` rows, `:405`,
   `:455`, `:525`, `:550`), 34 of 55 laws are unproven, five W4 theorems reach
   `Classical.choice` (`seat-w4-library-carriers.md:98-107`), and the Picos carrier was
   wrong in four claims and one bug once the source was read (`:196-257`). The
   representability ruling (`ocaml-packages-plan.md:61-90`) is today a list of IOUs; any
   port that starts using `Base.Map`/`Deque`/Eio inherits them.
6. **The unpushed PC edits.** `lake env` dies on this Mac (`fatal: unable to read tree
   6a70b884…`; F2 Q1, `seat-w1-deep-port.md:786-791`), so `lake build OCaml5.Render` is
   impossible here and `render-deep.sh` runs `lean` over stale oleans (`Fibers.olean` 03:20,
   `Fibers.lean` 05:49). `Volume.lean` and further repairs are on the PC only. Every avatar
   checkpoint is against a moving, partly invisible target.
7. **The fork-options reading** (F2-2, `seat-w1-deep-port.md:557`): `Witnesses.lean:239-251`
   still spells `immediateChild`/`deferredChild`/`daemonChild` as `inherit` citing
   `:5264-5272`, where rc.112 defaults `uninterruptible = false`; invisible while every witness
   root is interruptible, a Lean edit owed to the coordinator.

## 6. The first three packets

| # | packet | files | done when |
| --- | --- | --- | --- |
| 1 | **Re-diff to `625a207` and the drift gate** (this seat, today). `RunMachine.armed`, `arm`/`disarm`, `flushAll` in arming order, `flushRoot`, `runSyncExit` over the root's dispatcher; clauses 132/132, witnesses 62/62, census 84 rows; `hYieldStorm` re-run; the avatar pins the Deep files' digest and `run-witnesses.sh` fails on mismatch | `workshop/OCaml5/avatar/{deep_fibers,deep_clauses,deep_witnesses,deep_census}.ml`, `run-witnesses.sh` | counts equal, corpus 0 unclassified, `known-divergences.tsv` empty or re-classified, gate red on a Deep edit |
| 2 | **Derive the machine-level function group** (2–4 days). A syntax-level driver over `Fibers.lean` rendering the `Prim`-free group of §1 through `Ml.Syntax` + `mutate`, diffed against the hand port like the carriers | `Render.lean` SEAT W1, `avatar/render-deep.{sh,lean}`, `deep_fibers.ml` (generated block) | the group renders byte-identical; `render-deep.sh fibers` in `run-witnesses.sh`; the residue list names every function that stays hand-written and why |
| 3 | **`deep-run`, the Lean reference executor** (coordinator: `lakefile.toml`, a new `lean_exe`, 1–2 days after lake works). Reads `(ProgName \| Eff, tape)`, prints the `effect4-deep-v1` rows; the avatar prints the same rows; the Deep-covered corpus families (A, B, D, `iW*`, `spike-a0-avatar.md:809-813`) compared three ways | `Effect4/Target/TypeScript/DeepTrace.lean` (R4 §1), a `Deep/Run.lean` main, `avatar_trace.ml` | the corpus runs Lean-face vs avatar vs rc.112 under `fibers`; the avatar's fuel/ops divergences are rows, not surprises |

The free-monad embedding (§2) follows as packet four, once packet 3 gives Path C a reference
to be judged against.
