# Scout A — the run API: what it is today, what its proofs give, and the API to replace it with

Read-only scout, 2026-09-17, on `refactor/phase1-phase3` at the working tree as given. I ran no
Lean process and changed no file under `src/`, `Test/`, `tools/` or `ts/`; this note and nothing
else.

**Evidence words, used exactly.**

- **proved** — a theorem with a proof term at the cited line; I read the statement and the proof.
  I did not build, so "proved" means "in the tree", not "green in this session".
- **tested** — a `#guard`, `#guard_msgs` or battery pin at the cited line.
- **stamped** — a receipt written somewhere else (an axiom print, a gate marker, `docs/STATE.md`).
- **assumed** — my own reasoning about code I read. Every line of proposed Lean in §5 and §6 is
  assumed: none of it has been elaborated.
- **reproduced** — nothing in this note is reproduced; I ran no command that could reproduce
  anything.

---

## 1. The run API today

### 1.1 Four layers, five vocabularies

| layer | module | what a caller holds |
| --- | --- | --- |
| program as data | `src/Effect4/Program/Eff.lean:304` | `Eff NativeOp` (`Api.Program`, `src/Effect4/Api.lean:90`) and a `RowTable` beside it (`src/Effect4/Program/Native.lean:134`) |
| authoring | `src/Effect4/Program/Authoring.lean:78` | `Src Op = Env → List Nat → Except Refusal (Eff Op)`, and `Module Op` (`:178`) |
| certificate | `src/Effect4/Api.lean:441`, `src/Effect4/Program/Admission.lean:88` | `Api.Typed table` (program + typing) **or** `AdmittedProgram program table` (typing + three execution checks + three integer scans) |
| execution | `src/Effect4/Api.lean:284`, `:314`, `:323`; `src/Effect4/Api/HostSession.lean:84` | `Api.Run` / `Machine × ExitV` / `Session program table` |
| boundary | `src/Effect4/Api/RunnerBytes.lean:37` | `Bytes` rows and `ShapeDoc` schemas |

The five vocabularies do not line up, and lining them up by hand is most of what a caller writes
(§3).

### 1.2 The two routes into a run

**Raw route (no host).** `Api.replay program fuel tape answers table compileFuel`
(`src/Effect4/Api.lean:284-292`) loads a machine (`Api.load`, `:256-261`) and walks a decision
tape. `Api.run` is that tape fixed to `[evaluate, flush]` (`:314-317`); `Api.runSync` is
`Effect.runSyncExit` (`:323-330`). All three are documented as **raw**: they type nothing and
check no table (`:277-283`). The `answers` argument is a pre-loaded queue consumed in
registration order (`ExternalStore.ofAnswers`, `src/Effect4/Machine/Stores.lean:2032`); the
facade's own docstring calls it "the legacy route the session replaces … nothing new should use
it" (`src/Effect4/Api.lean:56-58`). The truth harness still uses it: `harness/truth/Truth.lean:611`
is `Api.run p fuel answers table`.

**Keyed route (the session).** `Effect4.Api.HostSession` (`src/Effect4/Api/HostSession.lean`), a
checked state machine over the same `Api.Machine`, where a reply is bound to the call it answers
before it becomes a decision (DI-23, DI-58). `Api.Runner` (`src/Effect4/Api/Runner.lean`) packs
the session with what indexes it and gives it one command alphabet; `Api.RunnerBytes`
(`src/Effect4/Api/RunnerBytes.lean`) is the same thing with rows of canonical bytes.

The keyed route is **not** reachable from the application facade: `src/Effect4/Api.lean:1-21`
imports neither `Api.HostSession` nor `Api.Runner`, and `Api/HostProtocol.lean:1` imports
`Effect4.Api`, so the dependency runs the other way. An application that writes
`import Effect4.Api` gets the raw route only and must import the session module by name.

### 1.3 The types a caller must construct, keyed route

Seven, before anything runs.

1. **`RowTable`** — `List Row` (`src/Effect4/Program/Native.lean:134`), `Row` having twelve fields
   (`src/Effect4/Program/Eff.lean:190-213`): `name`, `spelling`, `shape`, `trailing`, `kind`,
   `request`, `answer`, `error`, `requires`, `cite`, `typeArgs`, `registration`. A host row is
   `kind := .async, registration := .external` (`externalRow`, `src/Effect4/Program/Compile.lean:1346-1349`).
2. **`Api.Program`** — the `Eff` tree, where a host call is `perform (.external i) request` and
   `i` is **a position in that table** (`src/Effect4/Program/Native.lean:130`, resolved by
   `nativeRowOf`, `:321-323`).
3. **`AdmittedProgram program table`** — seven fields, six of them proofs
   (`src/Effect4/Program/Admission.lean:88-94`). In the battery it is written out by hand with
   `by cbv` / `by decide` per field (`Test/Api/HostSessionContract.lean:18-26`).
4. **`Header`** — `version`, `session`, `profile`, `table` (`src/Effect4/Api/HostSession.lean:23-28`).
5. **`Call`** — `version`, `session`, `table`, `callId`, `fiber`, `op`, `request`
   (`:32-40`), plus the guard `token` passed beside it (`bindCall`, `:145`).
6. **`Reply`** — `version`, `session`, `callId`, `key`, `completion` (`:48-54`), where `key` is
   `⟨fiber, token⟩` (`Frontier.lean:12-15`) and `completion` is
   `Completion Val Err Defect FiberId Ann` (`src/Effect4/Machine/Completion.lean:28-31`).
7. **A fuel number per step** — `compileFuel` at `start` (`:129`), a command fuel at every
   `applyReply` (`:204`) and every `advance` (`:239`). `Api.Budget` (`src/Effect4/Api.lean:456-459`)
   exists but is used only by `Typed.*`; the session does not take one.

### 1.4 The steps to run a program

With line references to `src/Effect4/Api/HostSession.lean` unless said otherwise.

| step | call | what it does | phase |
| --- | --- | --- | --- |
| open | `start program table expectedProfile header compileFuel` (`:129-138`) | checks version, non-empty session id, profile against a second copy, header table against the index table, then runs `admitProgram` itself and loads the machine | `Except Refusal (Session …)` |
| start the root | `advance s fuel Api.evaluate` (`:239-250`) | one control decision through `stepDecisionState`, checked against the protocol table, then `retire` | `.progressed` / `.frontier` |
| see the calls | `outstanding s` (`:140-141`) = `awaits machine` (`src/Effect4/Program/Admit.lean:39-43`) | the parked external calls as `(fiber, token, op, request)` | — |
| bind | `bindCall s call token` (`:145-158`) | checks version, session, table, no duplicate key, `callId = nextCall`, and that the machine really holds that row and request at that guard (`requestOf`, `Admit.lean:30-35`) | `.bound` |
| receive | `submit s reply` (`:180-189`) | refuses a second reply for one key, runs `preflight` (`:162-173`), checks a slot exists and the protocol edge allows it, then **stores only** | `.preflight` |
| apply | `applyReply s key fuel` (`:204-225`) or `applyPending s fuel` (`:229-235`) | re-runs `preflight`, steps the machine by the `answerAsync` decision, checks the protocol edge, and consumes only if the guard disappeared | `.applied` / `.frontier` / `.refused` |
| drive on | `advance s fuel decision` (`:239-250`) | any control that is not a direct answer (`:242`) | `.progressed` / `.frontier` |
| read | `inspect s` (`:253-258`) | `replayEval … 0 []` — an empty tape, so it classifies the machine as finished, frontier or stuck and computes the frontier reasons; returns `Api.Run` (machine included, `src/Effect4/Api.lean:272-276`) | — |

`retire` (`:194-199`) runs inside `applyReply` and `advance`: every association whose guard
disappeared moves to `retired`, carrying any accepted-but-unapplied reply.

The refusal alphabet is sixteen constructors (`:95-112`) and the phase alphabet six (`:114-121`).

**Bytes in.** There is no step for it. A program crosses as canonical bytes
(`bytesOf`/`ofBytes`, `src/Effect4/Api.lean:176-180`) and the table does not: a table is "unit
content beside the program's bytes" (`src/Effect4/Program/Native.lean:133-134`), and `Header`
carries the whole table by value (`HostSession.lean:27`). So a holder that receives a job as
bytes must decode the program, obtain the table by some other route, rebuild the header, and call
`start`; `Runner.load` (`Runner.lean:56-60`) takes the decoded values, not bytes. The runner plan
writes this step as if it existed — "`load` | program bytes, row table bytes, profile"
(`docs/research/2026-09-17-runner-schema-codegen-plan.md:83`) — and it does not.

### 1.5 The same thing as a journal

`Api.Runner` (`src/Effect4/Api/Runner.lean`) is the session with the indices packed inside:

```lean
inductive Command                                            -- Runner.lean:35-44
  | bind (call : Call) (token : Nat)
  | submit (reply : Reply)
  | apply (key : Key)
  | control (decision : NativeDecision)

structure Runner where                                       -- :47-53
  program : Api.Program ; table : RowTable ; fuel : Nat ; session : Session program table

def step (p : Runner) (c : Command) : Runner × HostSession.Phase        -- :70-72
def replay (p : Runner) : List Command → Runner × List HostSession.Phase -- :75-80
def inspect / observe / outstanding                                      -- :83, :86, :89
```

`load` (`:56-60`) is `start` with the two fuels split (`compileFuel`, `stepFuel`), and the step
fuel becomes the job's, held once. `Api.RunnerBytes` writes each command as canonical bytes
(`commandBytes`, `:37`), plays a row (`stepRow`, `:50-53`), folds a journal (`replayRows`, `:60-64`),
and publishes eight schemas by name (`schemas`, `:78-86`).

### 1.6 What a real driver looks like

The only non-test driver over the session in the tree is the keyed host lane,
`harness/truth/session/Keyed.lean`. Its two halves are worth reading as the honest measure of the
API:

- `consume` (`:175-200`) decodes one JSON record into one of the five session calls — 26 lines,
  most of it restating `version`, `s.header.session` and `rows` into `Call` and `Reply`.
- `planRun` (`:296-325`) is the driver loop: for every outstanding call not already bound, build a
  `Call` from `outstanding`, `bindCall` it, check the phase is `.bound`; then take the first
  active call, ask a model for an answer, build a `Reply`, `submit` it, check `.preflight`,
  `applyReply` it, check `.applied`, recurse; when nothing is active, `advance … .flush` and
  recurse. Thirty lines, hand-written, and every lane that wants a host must write it again.

`walk` (`:207-220`) is the replay half, and it carries a rule the API does not: it plays every row
at fuel 1000 **except** `apply`, which gets the caller's fuel (`:212`).

This lane runs only in `make check-full` (`Makefile:243`, `:396-397`), not in `make check-host`.

---

## 2. What the proofs guarantee today

All of these are in the checked closure: `src/Effect4/Laws.lean:34-40` roots the seven `Laws/Api`
modules, and `Test/All.lean:2,80-82,90-91` roots the batteries. `docs/STATE.md:11` stamps 320
modules at `[propext, Quot.sound]` at the last landing.

### 2.1 The session (`src/Effect4/Laws/Api/HostSession.lean`)

| theorem | line | in plain words |
| --- | --- | --- |
| `preflight_envelope` | `:11-36` | a successful preflight names the bound call it answers, agrees with its `callId`, establishes the `Envelope` (`Program/Admit.lean:183-185`), and the decision it returns is exactly `answerAsync fiber token completion` — nothing else can be smuggled through |
| `submit_conditions` | `:84-105` | an accepted receipt had: no stored reply for that key, a successful preflight, a slot for the key, and a permitted protocol edge |
| `reply_commute` | `:110-118` | two accepted receipts for different keys commute **as whole sessions** — machine, active calls, call ids, consumed ledger and retired list included |
| `reply_commute_disjoint` | `:121-125` | the same for two different fibers |
| `submit_duplicate` | `:144-148` | a second receipt on one key is refused `.pendingReply` |
| `submit_key_independence` | `:151-157` | a receipt leaves the outstanding set and every other key's stored reply alone |
| `submit_machine` | `:160-169` | a receipt never steps the machine, refusal or not |
| `submit_refusal_retains` | `:171-177` | a receipt refused by preflight leaves the session identical |
| `applied_guard_absent` | `:191-212` | if application reports `.applied`, the exact guard is gone from the machine afterwards |
| `applied_reply_refused` | `:214-219` | therefore the same reply is refused afterwards — at most one completion per call |
| `applyReply_conforms` | `:223-250` | every accepted application is an edge of the protocol table over the real before/after observations |
| `advance_conforms` | `:254-268` | the same for scheduler, clock and cancellation controls |
| `advance_answer_refuses` | `:185-187` | a direct `answerAsync` is never a control; it refuses by `rfl` |
| `applyReply_zero`, `applyPending_zero` | `:179-183` | zero fuel changes nothing and reports `.frontier` |

### 2.2 The journal algebra (`src/Effect4/Laws/Api/Runner.lean`)

| theorem | line | in plain words |
| --- | --- | --- |
| `bindCall_refused`, `submit_refused`, `applyReply_refused`, `advance_refused` | `:26,34,41,52` | each transition leaves the session unchanged when it refuses |
| `step_refused` | `:63-72` | therefore a refused row leaves the whole runner unchanged |
| `replay_append` | `:81-88` | playing `a ++ b` is playing `a` then `b`, phases concatenated |
| `replay_append_player` | `:91-93` | a journal split anywhere reaches the same runner |
| `Play.id_comp`, `comp_id`, `comp_assoc` | `:126-137` | runner transformers that write phases form a monoid |
| `replayPlay_nil`, `replayPlay_append` | `:142-148` | journals under concatenation map into it |
| `replay_unique` | `:157-165` | journals are the free monoid on commands, so any map that is a homomorphism and agrees on single rows **is** `replay` |
| `behaviour_cons` | `:174-175` | observed behaviour unfolds along `step` |
| `replay_skip_refused`, `behaviour_skip_refused` | `:178-187` | a refused row is the unit: dropping it changes nothing later |

`replay_unique` is the load-bearing one for §5: **anything I define as a function into
`List Command` inherits every law above without a new proof.**

### 2.3 The byte boundary (`src/Effect4/Laws/Api/RunnerBytes.lean`)

`commandOf_exact` (`:27`) and `row_unique` (`:37`): a journal row has one spelling.
`commandOf_commandBytes` (`:32`): a well-formed command's row reads back.
`stepRow_command` (`:42`), `stepRow_unreadable` (`:48`): playing a row is playing its command; an
unreadable row is not a refusal and changes nothing. `replayRows_append` (`:66`) and
`replayRows_eq_replay` (`:77-90`): rows act as commands do, so every §2.2 law holds at the
boundary. Axiom ceilings for seven of these are stamped in
`Test/Api/RunnerContract.lean:121-134` at `[propext, Quot.sound]`.

### 2.4 Observation (`src/Effect4/Laws/Api/Frontier.lean`)

`observe_of_reasons` (`:82-91`) is the whole story in one statement: the protocol state is
`awaitingAsync` exactly when some host wait is among the frontier reasons; `terminated` exactly
when there is no host wait and every fiber has exited; `idle` exactly when there is no host wait
and something is runnable; and `awaitDecision` appears exactly when the tape (not the fuel) ran
out with something runnable. Its four components are `:40`, `:50`, `:62`, `:13`.

### 2.5 Fuel and guards

`finished_mono_fuel` (`src/Effect4/Laws/Api/Fuel.lean:12-27`): once a replay finishes, a bigger
command budget gives the identical whole run — store, trace and reasons included.
`guard_persists` (`src/Effect4/Laws/Api/Guard.lean:22-30`): an outstanding host request survives
every raw decision except its own answer, unless its fiber was interrupted or exited;
`guard_persists_single` (`:35`) and `..._tape` (`:46`) are the single-fiber equalities across a
prefix.

### 2.6 The module face (`src/Effect4/Laws/Api/Codegen.lean`)

`checkTyping_type` (`:36`), `printModule_erasure` (`:41`), `printDecl_erasure` (`:52`),
`admitModule_typed` (`:68`), `admitModule_emitModule` (`:79-88`) — the emitted module reads back
and is admitted at the same program and type. This is the interop half of the run API and it is
in better shape than the run half.

### 2.7 What is **not** proved about the run API

Stated plainly, because §5 must not pretend otherwise.

- **No agreement theorem for the session.** Nothing says "a session that answers every call the
  way a host spec answers them reaches the exit the reference reaches". The end-state note lists
  this as open: "keyed agreement open (S8c)"
  (`docs/research/2026-09-16-core-goals-and-end-state.md:233`, row "session → machine").
- **No theorem about `start`.** There is no lemma that a program with a certificate opens.
- **No theorem about `inspect`.** The classification into `finished / frontier / stuck` is
  `replayEval`'s (`src/Effect4/Machine/Fibers.lean:2138-2141`) and is only pinned by guards.
- **`.frontier` from `applyReply` has no law.** That branch keeps the stepped machine, does not
  consume the reply and does not retire (`HostSession.lean:224`); `step_refused` does not cover
  it because it is not a refusal. The runner plan flags the same thing
  (`docs/research/2026-09-17-runner-schema-codegen-plan.md:177-182`).
- **No theorem that a session's own history replays.** `replay` is a function of a journal the
  caller supplies; a session keeps `consumed`, `applied` and `retired`
  (`HostSession.lean:88-93`) but not the rows it played, so "replay this run" is not expressible.
- **`Api.Run` has no codec**, so there is no `inspectBytes`
  (`docs/research/2026-09-17-runner-schema-codegen-plan.md:146-148`); a byte holder can read
  `observeBytes` and `outstandingBytes` and nothing else.
- **The session is not among the LCNF roots** (`tools/Conform/Effect4/Lcnf.lean:15` names
  `Effect4.Api.run` and `Effect4.Api.replay`), so the OCaml engine has a hand-written driver
  instead of a generated session. `docs/STATE.md:55` carries this as backlog.

---

## 3. Friction, by audience

Numbered so the owner can rule on them one at a time. Each is read from the cited lines.

### 3.1 For a human writing a program

**F1 — a host call is written by table position.** `perform (.external 0) request`
(`Test/Api/HostSessionContract.lean:16`) means "row 0 of the table beside this program"
(`src/Effect4/Program/Native.lean:130`). The author keeps the correspondence in their head. The
generated row wrappers (`src/Effect4/Program/Authoring/Rows.lean`) cover the twenty-two built-in
operations and **no** external row: there is no `Host.wait` wrapper because the row is the
caller's data, not the alphabet's.

**F2 — the certificate is written by hand.** Seven fields, six of them proofs, with the type
spelled out (`Test/Api/HostSessionContract.lean:18-26`). `Api.check` (`src/Effect4/Api.lean:446`)
and `Api.author` (`:501`) produce `Typed table`, which the session cannot take: `start` runs
`admitProgram` again (`HostSession.lean:136`). There is no `Typed → AdmittedProgram` bridge in the
tree.

**F3 — the header repeats what the session already has.** `start` takes the table twice (as index
and inside the header) and the profile twice (`HostSession.lean:129-135`). After `start`, only
`header.session` is ever read (`:149`, `:165`); `header.table`, `header.profile` and
`header.version` are never read again — `bindCall` compares the call's table against the
**index**, not the header (`:150`).

**F4 — every call and reply restates what the machine already knows.** `bindCall` refuses unless
`call.op` and `call.request` equal what `requestOf` reports (`:153`), and `outstanding` already
reports exactly those (`:140`). The restatement is deliberate for a recorded claim arriving from
elsewhere (`Program/Admit.lean:145-166`) but there is no constructor that builds the claim from
the session for the local case, so every driver writes `⟨version, s.header.session, table,
s.nextCall, fiber, op, request⟩` by hand (`harness/truth/session/Keyed.lean:305`).

**F5 — three rows per answer.** `bind`, `submit`, `apply` (`Runner.lean:36-41`). The split earns
`reply_commute` and it should stay available, but the common case — a reply that is ready to
apply — has no single call. `applyPending` (`HostSession.lean:229`) exists for one pending reply
and refuses `.selectionRequired` for more (`:235`).

**F6 — fuel is scattered.** `compileFuel` at `start`, a fuel per `applyReply` and per `advance`
(`:204`, `:239`), one `fuel` on `Runner` (`Runner.lean:50`), a `Budget` on the facade used only by
`Typed.*` (`src/Effect4/Api.lean:456-478`), and a driver that has to know that `apply` gets a
different number from everything else (`harness/truth/session/Keyed.lean:212`).

### 3.2 For an agent generating a program

**F7 — the shape of a correct driver is not in the library.** `planRun`
(`harness/truth/session/Keyed.lean:296-325`) is thirty lines of loop that an agent would have to
re-derive: bind everything outstanding, answer the first active call, apply it, flush when nothing
is active. Nothing in `src/` offers it, and the phases that must be checked after each call
(`.bound`, `.preflight`, `.applied`) are part of the protocol an agent has to learn by probe.

**F8 — sixteen refusals, one of them unreachable.** `Refusal.pendingControl`
(`HostSession.lean:110`) is produced by no function in the module (I checked every constructor
against the file); it survives from the wave-2 draft, where a pending reply forbade a control
(`docs/research/wave2-delivery/s6b-1/drafts/HostSession.lean:187`). It now costs a case in the
generated codec and a tag in the sum (`src/Effect4/Api/RunnerDerived.lean:1121`, `:1140`, `:1158`)
and appears in the generator's guard list (`tools/Effect4Gen/guards/runner.lean:33`).

**F9 — the refusals do not say where.** `AuthorRefusal` and `TypeRefusal` carry a path
(`src/Effect4/Api.lean:494-498`, DI-86); the session's `Refusal` carries nothing — not the key,
not the call id, not the expected value. `.staleCall` and `.envelope` are the two an agent will
hit most and both are bare (`:107`, `:108`).

**F10 — the facade does not reach the session.** `import Effect4.Api` gives `run`, `replay`,
`runSync` and the `answers` list the same facade tells you not to use (`src/Effect4/Api.lean:56-58`);
the keyed route needs a second import and a different vocabulary.

**F11 — no self-description of the run.** `schemas` (`RunnerBytes.lean:78-86`) publishes eight
shapes — `Command`, `Verdict`, `Header`, `State`, `Outstanding`, `Program`, `Value`, `Schema` —
and no shape for what a run *is*, because `Api.Run` has no codec. An agent asking "what happened"
gets a protocol state and a list of awaits.

**F20 — a job cannot arrive as bytes.** The rows of a journal are bytes
(`RunnerBytes.lean:37-47`) but the session that plays them is opened from decoded values
(`Runner.load`, `Runner.lean:56-60`). There is no `openBytes`, and the table is not part of the
program's bytes (`src/Effect4/Program/Native.lean:133-134`), so a holder must find the table
elsewhere. Adding it is small — `ofBytes` (`src/Effect4/Api.lean:180`) plus a `Canonical RowTable`
through `Row` — and it is what makes "send a holder a job" one message.

### 3.3 For composing programs and providing services

**F12 — programs written against different tables cannot be composed.** `.external i` is a
position (`Native.lean:130`); two fragments written against two tables mean different rows under
the same syntax, and nothing checks it. `Table.lawful` (`src/Effect4/Program/Table.lean:70-73`)
checks a table for duplicate keys and builtin collisions but says nothing about a program's
indices, and `Api.check` types `.external i` through `nativeRowOf table` (`Native.lean:321-323`),
so a mismatched composition types fine against the wrong row.

**F13 — services are identified by two numbers.** `ServiceKey` is `⟨name, service⟩`, both codes
(`src/Effect4/Machine/Key.lean:79-82`), written at the authoring site as `⟨⟨4⟩, ⟨4⟩⟩`
(`Test/Program/LayerSharingContract.lean:16-17`). The carrier the signature types it at lives
elsewhere, in the `nativeServiceTypes` list (`Native.lean:291-293`), so nothing at the authoring
site connects a key to its type.
Scout D proposes and has compiled a `ServiceDef` surface for exactly this
(`docs/research/2026-09-17-scout-named-and-exact-service-keys.md:412-462`), queued as D-2 in
`docs/research/2026-09-17-scout-findings-ledger.md`.

**F14 — a `Typed` cannot be composed.** `Typed` holds a program and its certificate
(`src/Effect4/Api.lean:441-443`) and has no `bind`, `andThen` or `map`; composing two checked
programs means going back to the trees and checking again. That is arguably right (a certificate
is about one tree) but it means the composable layer is `Src` and the runnable layer is `Typed`,
with no operation that carries evidence across.

**F15 — a module has layers but not rows or services.** `Module Op` is
`{ layers : List (String × LayerSrc Op), main : Src Op }` (`Authoring.lean:178-180`). The row table
and the service keys are not part of it, so "here is my program and everything it needs" is not
one value; `Test/Program/AuthoringContract.lean:201-210` shows the layers by name and the keys as
loose constants.

### 3.4 For observing, replaying and program-as-data

**F16 — a run does not record itself.** The session keeps counters and ledgers
(`HostSession.lean:88-93`) but not the commands it played. `Runner.replay` takes a journal the
caller kept (`Runner.lean:75`). The runner plan's "journal first" rule
(`docs/research/2026-09-17-runner-schema-codegen-plan.md:203-206`) has no support in the API: the
holder must keep the journal itself and there is no law that a session and its journal agree.

**F17 — observation is five calls and a private machine.** `inspect` (`:253`), `observe`
(`Runner.lean:86`), `outstanding` (`:89`), `pendingReplies` (`HostSession.lean:176`), plus the
session's own fields. `inspect` returns `Api.Run`, which holds the whole machine
(`src/Effect4/Api.lean:272-276`), so the one call that says the most is the one that cannot cross
a boundary.

**F18 — the trace is not in the observation.** `Run.trace` (`src/Effect4/Api.lean:335-336`) is the
machine's `RunEvent` list (`src/Effect4/Machine/Fibers.lean:360-384`), which carries `Task` values
and is not first-order content. Nothing projects it to something a holder or an agent can read.

**F19 — replay is defined but not reachable from a real run.** The three replay theorems
(`replay_append`, `replay_unique`, `replayRows_eq_replay`) are about journals; the only journals in
the tree are a literal in a battery (`Test/Api/RunnerContract.lean:31-33`) and the JSON schedule
the host lane computes with one hand-written planner and replays with another
(`harness/truth/session/Keyed.lean:296-325` writes it, `:207-220` plays it). There is no function
from a finished session to the rows that produced it.

---

## 4. The API I would build

### 4.1 The one idea

**Journals are the free monoid on commands, and that is already proved
(`Laws/Api/Runner.lean:157-165`).** So the whole dream API can be *functions that produce rows*,
plus one session that plays and records them. Nothing needs a new semantics, and every
convenience inherits `replay_append`, `step_refused` and `replay_skip_refused` for free. The wire
alphabet does not change, so the codec questions the runner plan leaves open
(`docs/research/2026-09-17-runner-schema-codegen-plan.md:155-161`) stay open exactly as they are.

Three modules, not five: **`Author`** (what you write), **`Session`** (what runs it), **`Face`**
(what crosses a boundary — mostly `Api` as it stands). Everything in §1.1's table becomes a field
of one of three records.

### 4.2 `Author` — creating, composing, providing

The carrier does not change: `Src Op = Env → List Nat → Except Refusal (Eff Op)`
(`Authoring.lean:78`). `Env` gains one field, exactly as `layers` was added
(`Authoring.lean:69-72`), and one hand-written lift resolves it, exactly as `Layer.ref` does
(`:167-170`) and as `var` does (`:133-136`).

```lean
-- proposed
structure RowDef where
  row : Row                                   -- Program/Eff.lean:190
  deriving DecidableEq, Repr

namespace Row
/-- A host row an author declares once. `kind := .async, registration := .external` is what
`externalRow` (Program/Compile.lean:1346) demands of a row the host answers. -/
def host (spelling : String) (request answer : Ty) (error : Ty := .never)
    (cite : String := "") : RowDef
end Row

/-- The one extra field. `Env.push` and `Env.closed` (Authoring.lean:90-93) do not touch it,
so every generated lift and every `Src.Scoped` lemma is unchanged. -/
structure Env where
  names  : Names := []
  layers : LayerNames := []
  rows   : List (String × Nat) := []          -- new

/-- The one new name-resolving operation, the third of three. The key is `rowKey`
(Program/Table.lean:19), the same pair `Table.lawful` requires to be unique. -/
def Row.call (r : RowDef) (request : TermSrc) : Src NativeOp := fun env p =>
  match env.rows.find? (·.1 == rowKey r.row) with
  | some (_, i) => (perform (.external i) request) env p
  | none => .error ⟨p, .unboundRow r.row.spelling⟩
```

and the module becomes the one value that holds everything a program needs:

```lean
-- proposed
structure Module (Op : Type) where
  rows     : List RowDef := []                 -- the table, by name
  services : List ServiceDef := []             -- scout D's surface, queued as D-2
  layers   : List (String × LayerSrc Op) := []
  main     : Src Op

/-- Elaborate, assemble the table in declaration order, type, admit — one call, one value. -/
def Author.build (m : Module NativeOp) : Except BuildRefusal Built
```

with the packed certificate that makes the run API usable at all (the same packing trick
`Runner` already uses, `Runner.lean:47-53`):

```lean
-- proposed
structure Built where
  table    : RowTable
  program  : Api.Program
  admitted : AdmittedProgram program table     -- Program/Admission.lean:88
  rowNames : List (String × Nat)               -- for blame, printing and the reactor
```

`BuildRefusal` is the sum of the three refusals that already exist and carry a location:
`Authoring.Refusal` (`Authoring.lean:61-64`), `TypeRefusal` (DI-86), `AdmitRefusal`
(`Admission.lean:69-83`).

Four conveniences, all functions over the generated lifts, none a constructor:

```lean
-- proposed
def fork (p : Src Op) (opts : ForkOptions := {}) : Src Op   -- withFiber (Action.fork p opts)
def join (f : TermSrc) : Src Op                             -- awaitFiber f .awaitValue
def with_ (l : LayerSrc Op) (body : Src Op) : Src Op        -- provideLayer l false body
def give (s : ServiceDef) (v : TermSrc) (body : Src Op) : Src Op
```

`fork`/`join` do not exist today; the battery writes
`withFiber (Action.fork (…) immediateChild)` and `awaitFiber (var "f") .joinEffect`
(`Test/Program/AuthoringContract.lean:249-251`).

### 4.3 `Session` — running, answering, observing, replaying

```lean
-- proposed
structure Session where
  built   : Built
  id      : String
  budget  : Api.Budget := {}                   -- src/Effect4/Api.lean:456
  machine : Api.Machine
  ledger  : Ledger                             -- today's active/pending/consumed/retired/nextCall
  journal : List Command                       -- every row played, in order        ← new
  phases  : List Phase                         -- the verdict of each               ← new

/-- No refusal: the certificate is the evidence `start` re-derives today. -/
def open (b : Built) (id : String) (budget : Api.Budget := {}) : Session

/-- A job as one message (F20): the program's bytes and the table's, checked into a `Built`. -/
def openBytes (program table : Bytes) (id : String) : Except BuildRefusal Session

/-- Play rows and record them. `Runner.step` under the hood. -/
def play (s : Session) (rows : List Command) : Session

/-! Rows, as data. Every one of these is a `List Command`, so §2.2 covers all of them. -/
def Rows.control (d : Api.Decision) : List Command
def Rows.start   : List Command                       -- [control evaluate]
def Rows.flush   : List Command                       -- [control flush]
def Rows.clock (millis : Nat) : List Command          -- [control (.advance millis)]
def Rows.receive (s : Session) (key : Key) (c : Answer) : List Command   -- [bind …, submit …]
def Rows.answer  (s : Session) (key : Key) (c : Answer) : List Command   -- [bind …, submit …, apply key]
def Rows.answerAll (s : Session) (r : Reactor σ) (st : σ) : List Command × σ

/-- The rows depend on the session (they carry the recorded claim, F4), so each `Rows.*` has a
method beside it that plays what it builds. These two are the common case. -/
def answer (s : Session) (key : Key) (c : Answer) : Session := s.play (Rows.answer s key c)
def control (s : Session) (d : Api.Decision) : Session := s.play (Rows.control d)

/-- The claim a local driver would otherwise write out (F4): built from `outstanding`. -/
def Call.at (s : Session) (key : Key) : Option Call

/-- One record, all first-order, with a generated `Canonical` instance. -/
structure Observation where
  state     : HostProtocol.State                -- Api/HostProtocol.lean:12
  outcome   : Api.Outcome                       -- src/Effect4/Api.lean:265
  exit      : Option ExitV
  awaiting  : List Await                        -- Program/Admit.lean:37
  pending   : List Key
  retired   : List Key
  applied   : Nat
  reasons   : List FrontierReason               -- Api/Frontier.lean:22
  deriving DecidableEq, Repr

def observe (s : Session) : Observation

/-- The host, as a pure function of the row, the request and its own state: the executable
half of `HostSpec` (Program/Profile.lean:178-194), the shape `Profile.Scalar.step?` already
has (Profile.lean:333-335). -/
abbrev Reactor (σ : Type) := Row → Val → σ → Option (Answer × σ)

/-- Bind, answer and apply every outstanding call, then flush, until nothing is outstanding or
the rounds run out. This is `planRun` (harness/truth/session/Keyed.lean:296-325) as a library
function. -/
def drive (s : Session) (r : Reactor σ) (st : σ) (rounds : Nat) : Session × σ

/-- Three named drivers, each a journal, replacing `Api.run`, `TestClock.run` and the hand tapes. -/
def runPure (b : Built) : Observation                       -- play (start ++ flush)
def runClock (b : Built) (adjusts : List Nat) : Observation  -- Api/TestClock.lean:38
def runWith (b : Built) (r : Reactor σ) (st : σ) : Observation × σ
```

Two properties this shape has that today's does not:

- **A session is its own recording.** `s.journal` is what happened, so `program-as-data` extends
  to `run-as-data`: `(Api.bytesOf s.built.program, s.journal.map commandBytes)` is the whole run
  as content, and `replayRows` (`RunnerBytes.lean:60`) plays it back.
- **The reactor never appears in the journal.** Replay is `play` over recorded rows and calls no
  reactor, which is the rule the runner plan states (`…runner-schema-codegen-plan.md:203-206`).

### 4.4 `Face` — the boundary

Unchanged in substance: `print`, `read`, `readAt`, `readable`, `roundTrip`, `bytesOf`, `ofBytes`,
`printModule`, `emitModule`, `admitModule` (`src/Effect4/Api.lean:142-239`), plus
`RunnerBytes`'s row and schema functions. Two additions:

- `schemas` gains `"Observation"`, `"Journal"` and `"Table"` (the last is F20's other half), which
  closes the gap the runner plan records (`…runner-schema-codegen-plan.md:146-148`) without a
  machine codec, because `Observation` is first-order by construction.
- `Built.emit name` is `Typed.emit` (`src/Effect4/Api.lean:484`) on the packed certificate, so the
  printed module and the run come from one value.

### 4.5 Which theorem covers which function, and what is new

| proposed | defined as | covered today by | new obligation |
| --- | --- | --- | --- |
| `Session.open` | `HostSession.start` with the header built from `Built` | the certificate fields (`Admission.lean:88-94`) | **O-1** `open_total`: with a `Built`, opening never refuses. One line; the only refusals left are version/session-id, which `open` no longer takes |
| `Session.openBytes` | `ofBytes` (`src/Effect4/Api.lean:180`), a `Canonical RowTable`, then `Author.build` on the decoded pair | `Wire` round trip for the program | **O-14** `openBytes_eq_open`: bytes that decode open the session the decoded values open. Follows from the program's decode-exactness and the row table's generated instance |
| `Rows.control` / `Session.play` | `Runner.step`, `Runner.replay` | `step_refused` (`Laws/Api/Runner.lean:63`), `replay_append` (`:81`), `replay_skip_refused` (`:178`) | none |
| `Rows.receive` | `[bind …, submit …]` | `submit_machine` (`Laws/Api/HostSession.lean:160`), `submit_conditions` (`:84`), `submit_duplicate` (`:144`), `submit_key_independence` (`:151`), `reply_commute` (`:110`) | **O-2** `receive_rows`: the two rows are the two transitions — an unfolding equation, `rfl`-shaped |
| `Rows.answer` | `receive ++ [apply key]` | `preflight_envelope` (`:11`), `applyReply_conforms` (`:223`), `applied_guard_absent` (`:191`), `applied_reply_refused` (`:214`) | **O-3** `answer_rows` (unfolding) and **O-4** `answer_once`: playing the same `answer` twice refuses the second — follows from `applied_reply_refused` |
| `Call.at` | from `outstanding` | `requestOf` is what `bindCall` checks against (`HostSession.lean:153`) | **O-5** `bindCall_at`: a call built by `Call.at` is never `.staleCall`. Direct from `awaits`/`requestOf` (`Program/Admit.lean:39-43`) |
| `Session.drive` | fold of `play` over `Rows.answerAll` | everything above, through `replay_unique` (`Laws/Api/Runner.lean:157`) | **O-6** `drive_eq_play`: driving is playing the rows it chose, so replay needs no reactor. **O-7** `drive_envelope`: if the reactor's answers fit the row's `answer`/`error` types, every `submit` it writes preflights — the missing link between `HostSpec` (`Profile.lean:178`) and `preflight_envelope` |
| `Session.observe` | `inspect`, `observe`, `outstanding`, the ledger | `observe_of_reasons` (`Laws/Api/Frontier.lean:82`) ties state to reasons | **O-8** the generated `Canonical` instance and its `fits` proof (the generator writes these, `Api/RunnerDerived.lean`) |
| `Session.journal` | recorded by `play` | — | **O-9** `journal_replays`: `play (open s.built s.id s.budget) s.journal = s`. Induction on `play`; this is the theorem that makes replay mean something |
| `runPure` | `play (start ++ flush)` | `run_eq_meaning` on `Straight`, `run_eq_ref`, `TypedProgram.run_soundB` (`docs/STATE.md:48`), `finished_mono_fuel` (`Laws/Api/Fuel.lean:12`) | **O-10** `runPure_eq_run`: the journal `[evaluate, flush]` gives the same machine as `Api.run` (`src/Effect4/Api.lean:317`), so the existing agreement theorems transfer verbatim. Both call `stepDecisionState` per decision (`Machine/Fibers.lean:2146`, `HostSession.lean:247`); the only extra step is the protocol edge, and `controlLabel` sends both decisions to `.schedule` (`Api/HostProtocol.lean:102`), which the table allows from every state (`:69-72`) |
| `Author.build` | elaborate, assemble, check, admit | `elaborate_scoped` and the 48 lift lemmas (`docs/STATE.md:14`), `explain_none_iff` (`src/Effect4/Api.lean:125`), `admitProgram_*_int` (`:397-400`) | **O-11** `build_table_lawful`: a table assembled from `RowDef`s with distinct spellings is `Table.lawful` (`Program/Table.lean:70`) — decidable, one proof for all programs, and it is what F12 fixes. **O-12** `build_rows_resolve`: every `Row.call` in a built module resolves to the row it names |
| `Row.call` | one name resolution | the carrier is unchanged, so `Src.Scoped` (`Laws/Program/Authoring.lean:42-43`) applies as written | **O-13** one scope lemma, in the shape of the 48 generated ones (`Row.call` resolves no binder, so it is the `perform` lemma with a lookup in front) |
| `ServiceDef` | scout D's structure | `carrier_unique` is already written and compiled by scout D (`…scout-named-and-exact-service-keys.md:452-462`) | none beyond D-2 |

Fourteen new obligations, twelve of them small. **O-7** and **O-9** are the two that carry weight:
`drive_envelope` is the first theorem in the tree that relates a host specification to the
session, which is the open row of the proof chain
(`docs/research/2026-09-16-core-goals-and-end-state.md:233`); `journal_replays` is what makes
"replay a run" a proposition rather than a convention.

### 4.6 What this deletes

- `applyPending` and `Refusal.selectionRequired` (`HostSession.lean:229-235`, `:104`): the
  convenience is `Rows.answer key`, which always names a key.
- `Refusal.pendingControl` (`:110`), unreachable today (F8).
- `Refusal.version`, `.session`, `.profile`, `.table` and `.program` (`:96-100`) move off `open`
  and onto the journal boundary, where a foreign row is checked — `commandOf` already has the
  "this row is not a command" verdict (`RunnerBytes.lean:50-53`).
- `Header` as an argument; it stays as the wire form.
- The `answers` argument of `load`, `replay`, `run` and `runSync` (`src/Effect4/Api.lean:257`,
  `:285`, `:315`, `:325`) once the truth harness drives a `Reactor` instead
  (`harness/truth/Truth.lean:611`). That is the last piece of DI-23's amendment.
- `planRun` and `consume` in the host lane (`harness/truth/session/Keyed.lean:175-200`, `:296-325`),
  about 60 lines, replaced by `drive` and a `Reactor` built from the fixture's model.

---

## 5. Three examples, today and proposed

### 5.1 A service call

**Today** (`Test/Api/HostSessionContract.lean:14-39`, twenty-six lines, plus the driver):

```lean
def table : RowTable := [Profile.Scalar.waitRow]
def program : Api.Program :=
  .bind (.perform (.external 0) (.lit (.nat 2))) (.perform (.external 0) (.lit (.nat 3)))
def header : Header := ⟨2, "session-A", "serial-root-scalar-v1", table⟩
def admitted : Api.AdmittedProgram program table where
  ty := ⟨.nat, .prod .string .string, .empty⟩
  typed := by cbv
  lawful := by decide
  runnable := by decide
  intFreeTable := by decide
  intFreeProgram := by decide
  intFreeType := by decide
def initial : Session program table := { admitted, header, machine := Api.load program 100 }
def parked  := (advance initial 100 Api.evaluate).session
def call0 : Call := ⟨2, "session-A", table, 0, Api.root, .external 0, .nat 2⟩
def bound0  := (bindCall parked call0 0).session
def reply0 : Reply := ⟨2, "session-A", 0, ⟨Api.root, 0⟩, .ofExit (.success (.nat 2))⟩
def pending0 := (submit bound0 reply0).session
def after0   := (applyPending pending0 100).session
def call1 : Call := { call0 with callId := 1, request := .nat 3 }
def bound1   := (bindCall after0 call1 1).session
def reply1 : Reply := { reply0 with callId := 1, key := ⟨Api.root, 1⟩,
                        completion := .ofExit (.success (.nat 3)) }
def pending1 := (submit bound1 reply1).session
def finished := (applyPending pending1 100).session
#guard (inspect finished).exit = some (.success (.nat 3))
```

**Proposed** (assumed; the reactor is the Scalar profile's own rule,
`Program/Profile.lean:326-328`):

```lean
def wait : RowDef := Row.host "Host.wait" (request := .nat) (answer := .nat)
                              (error := .prod .string .string)

def twice : Module NativeOp :=
  { rows := [wait]
    main := eff do
      let _ ← wait.call 2
      let b ← wait.call 3
      return b }

def echo : Reactor Unit := fun _ request st => some (.ofExit (.success request), st)

#guard (Author.build twice |>.map fun b => (Session.runWith b echo ()).1.exit)
  = .ok (some (.success (.nat 3)))
```

Everything the old version restated — the table position, the type, the six certificate proofs,
the header, two calls, two replies, two keys, two fuels — is either derived or gone. The rows the
session recorded are still there in `s.journal` if the test wants to pin them.

### 5.2 A fork and an await

**Today** (`Test/Api/KeyedHostContract.lean:14-37`):

```lean
def opts : Supervision.ForkOptions := { daemon := false, startImmediately := true, maskMode := .inherit }
def program : Api.Program :=
  .bind (.withFiber (.fork (.perform (.external 0) (.lit (.nat 2))) opts))
    (.bind (.withFiber (.fork (.perform (.external 0) (.lit (.nat 3))) opts))
      (.bind (.awaitFiber (.var 0) .awaitValue) (.awaitFiber (.var 1) .awaitValue)))
def initial : Session program table where
  admitted := { ty := ⟨.exitOf .nat (.prod .string .string), .never, .empty⟩, typed := by cbv, … }
  header := ⟨version, "multi", "keyed-v2", table⟩
  machine := Api.load program 1000
def parked := (advance initial 1000 Api.evaluate).session
def ca : Call := ⟨version, "multi", table, 0, ⟨1⟩, .external 0, .nat 2⟩
def cb : Call := ⟨version, "multi", table, 1, ⟨2⟩, .external 0, .nat 3⟩
def bound := (bindCall (bindCall parked ca 0).session cb 1).session
def a : Reply := ⟨version, "multi", 0, ⟨⟨1⟩, 0⟩, .ofExit (.success (.nat 2))⟩
def b : Reply := ⟨version, "multi", 1, ⟨⟨2⟩, 1⟩, .ofExit (.success (.nat 3))⟩
```

The author writes the child fiber numbers `⟨1⟩` and `⟨2⟩` and the guard tokens `0` and `1` by
hand, having worked out what the machine will mint.

**Proposed** (assumed):

```lean
def pairUp : Module NativeOp :=
  { rows := [wait]
    main := eff do
      let f ← fork (wait.call 2)
      let g ← fork (wait.call 3)
      let _ ← join f
      let y ← join g
      return y }

-- `join` is `awaitFiber … .awaitValue`, so the answer is the child's exit as a value, exactly
-- as the battery's `(inspect …).exit = some (.success (Val.exitOk (.nat 3)))` reads it
-- (Test/Api/KeyedHostContract.lean:59).
#guard (Author.build pairUp |>.map fun b => (Session.runWith b echo ()).1.exit)
  = .ok (some (.success (Val.exitOk (.nat 3))))
```

No fiber number and no token appears: `drive` reads them from `observe`'s `awaiting` and hands
each request to the reactor. If a test wants to fix the interleaving it answers by key instead,
and each row still carries the claim the session checks:

```lean
def s0 := (Session.open built "multi").control Api.evaluate
def s1 := s0.answer ⟨⟨2⟩, 1⟩ (.ofExit (.success (.nat 3)))
def s2 := s1.answer ⟨⟨1⟩, 0⟩ (.ofExit (.success (.nat 2)))
```

and `reply_commute` (`Laws/Api/HostSession.lean:110`) still says the two receipts commute, because
`Rows.receive` is those two transitions and nothing else.

### 5.3 A layered service

**Today** — the authoring half is already good
(`Test/Program/AuthoringContract.lean:193-222`):

```lean
def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩      -- Test/Program/LayerSharingContract.lean:16-17
def kRef : ServiceKey := ⟨⟨6⟩, ⟨7⟩⟩
def counter : LayerSrc NativeOp :=
  Layer.effect kA <|
    bind "ref" (service kRef) <|
    andThen (Ref.update .incr (var "ref")) <|
    succeed (nat 5)
def onceByName : Module NativeOp :=
  { layers := [("Counter", counter)]
    main :=
      bind "r" (Ref.make (nat 0)) <|
      provideService kRef (var "r") <|
      bind "n" (provideLayer (Layer.ref "Counter") false <|
                provideLayer (Layer.ref "Counter") false <| service kA) <|
      Ref.get (var "r") }
#guard elaborateModule onceByName = .ok once
```

and then, to run it, the caller leaves this vocabulary entirely: elaborate, check, build an
`AdmittedProgram` or call `Api.run` raw (`Test/Program/LayerSharingContract.lean:21-33` writes the
tree by hand instead).

**Proposed** (assumed; `ServiceDef` is scout D's, `…scout-named-and-exact-service-keys.md:412-462`):

```lean
-- The two numbers are the battery's `kA` and `kRef` (Test/Program/LayerSharingContract.lean:16-17)
-- and the carriers are the ones `nativeServiceTypes` assigns those codes (Native.lean:291-293).
-- Whether a key also gains a spelling is scout D's open ruling (D-1 in the findings ledger).
def Counter : ServiceDef := Service.define (name := 4) (code := 4) (carrier := .nat)
def RefSvc  : ServiceDef := Service.define (name := 6) (code := 7) (carrier := NativeOp.refTy)

def counter : LayerSrc NativeOp :=
  Counter.built <| eff do
    let ref ← RefSvc.use
    Ref.update .incr ref
    return 5

def app : Module NativeOp :=
  { services := [Counter, RefSvc]              -- carriers checked by `Agrees`, by `decide`
    layers   := [("Counter", counter)]
    main := eff do
      let r ← Ref.make 0
      RefSvc.give r <| eff do
        let _ ← with_ (Layer.ref "Counter") (with_ (Layer.ref "Counter") Counter.use)
        Ref.get r }

#guard (Author.build app |>.map fun b => (Session.runPure b).exit)
  = .ok (some (.success (.nat 1)))
```

The expected value is the battery's: `once` finishes with exit `.nat 1` and the heap at
`[.nat 1]` — the shared layer is built once however many times it is referenced
(`Test/Program/LayerSharingContract.lean:151-153`).

The three things that changed: the keys are declared once with their carriers instead of written
as four numbers; the module carries its services; and running it is one call on the same value
that was built, with no second certificate.

---

## 6. Open decisions for the owner

**D1 — Does `answer` join the wire alphabet, or stay a function into rows?**
*Recommend: stay a function.* Adding a fifth `Command` constructor costs a wire tag, a codec case,
a compatibility-policy entry (`Test/fixtures/baseline/66ee4657-supplement-v1.policy.json`) and a
re-proof of `step_refused` for the new arm. As a function into `List Command` it inherits
`replay_append` and `replay_unique` (`Laws/Api/Runner.lean:81`, `:157`) with one unfolding lemma
(O-2, O-3). The three-row split also stays visible in the journal, which is what a holder wants to
audit.

**D2 — Does the session record its own journal?**
*Recommend: yes, every row including refused ones.* It costs one list field and gives O-9
(`journal_replays`), which is what makes "replay a run" a proposition. Refused rows are the unit
of the action (`replay_skip_refused`, `:178`), so a compaction may drop them and the note already
proves that dropping them is sound. The cost is memory in a long run; the compaction is the
answer, not a policy of not recording.

**D3 — Does `open` still refuse?**
*Recommend: no.* Take a `Built` (a packed `AdmittedProgram`) and an id, and make the five
identity refusals (`version`, `session`, `profile`, `table`, `program`) properties of **decoding a
journal row** instead, where `commandOf` already has a verdict for a row that is not a command
(`RunnerBytes.lean:50-53`). It removes five of sixteen refusals from the run path, and a
certificate cannot be forged because it is indexed by the program and the table
(`Admission.lean:85-88`).

**D4 — Is the row table an input to elaboration or an output of it?**
*Recommend: an output.* `Module.rows` declares rows by name, `Author.build` assembles the table in
declaration order, and `Row.call` resolves names to positions exactly as `Layer.ref` resolves
layers today (`Authoring.lean:167-170`). It fixes F1 and F12 with a mechanism that already exists
three times in the same file, and it gives O-11 (`build_table_lawful`) once instead of a `decide`
per program. Against it: a program whose table is given by a host (a package's rows, DI-89) still
needs the table as an input, so `build` must accept a pre-assembled table too — that is one extra
field, not a different design.

**D5 — Is the reactor in `src/` or in the harness?**
*Recommend: `src/`, as `Reactor σ := Row → Val → σ → Option (Answer × σ)`.* It is the shape
`Profile.Scalar.step?` already has (`Profile.lean:333-335`), it is the executable half of
`HostSpec` (`:178-194`), and it makes `drive` a library function instead of thirty lines per lane
(`harness/truth/session/Keyed.lean:296-325`). It is also the one place where a theorem can connect
a host specification to the session (O-7), which is the open row of the proof chain.

**D6 — Does `Observation` replace `inspect`?**
*Recommend: yes for the public face; keep `inspect` for Lean-side batteries.* `Api.Run` holds the
machine (`src/Effect4/Api.lean:272-276`) and therefore cannot cross a boundary; `Observation` is
first-order and gets a generated codec, which is what closes the runner plan's missing
`inspectBytes` (`…runner-schema-codegen-plan.md:146-148`). Batteries that assert on stores and
traces keep the machine-valued reading.

**D7 — Does the trace get a projection?**
*Recommend: yes, but after D6, and as a named subset.* `RunEvent`
(`src/Effect4/Machine/Fibers.lean:360-384`) carries `Task` values and will not get a codec. A
projection to `(fiber, kind, payload)` rows covers fork, park, resume, interrupt and exit — the
five an agent asks about — and its totality is a guard, not a theorem. Until then, `Observation`
without a trace is honest and `Run.trace` stays the Lean-side reading.

**D8 — One `Budget` for the whole job, or fuel per step?**
*Recommend: one `Budget` on the session* (`Api.Budget`, `src/Effect4/Api.lean:456-459`), as
`Runner.fuel` already does for the step half (`Runner.lean:50`). Two holders playing one journal
then stop in the same places, which is the runner plan's recommendation
(`…runner-schema-codegen-plan.md:180-182`), and `finished_mono_fuel` (`Laws/Api/Fuel.lean:12`)
says a larger budget cannot change a finished run. The host lane's rule that `apply` gets a
different fuel from everything else (`harness/truth/session/Keyed.lean:212`) then disappears.

**D9 — Is `Refusal.pendingControl` deleted now or at the next codec change?**
*Recommend: now, with the codec regeneration.* It is produced nowhere (F8), it occupies tag 14 of
the generated sum (`Api/RunnerDerived.lean:1121`) and the families are deliberately not yet frozen
in `wire-tags.json` (`…runner-schema-codegen-plan.md:155-161`), so this is the cheapest moment it
will ever have.

**D10 — Does the facade re-export the session?**
*Recommend: yes, and retire the `answers` argument in the same step.* Today
`import Effect4.Api` reaches only the route its own docstring tells you not to use
(`src/Effect4/Api.lean:56-58`). The import runs the wrong way for one reason: the session needs
the facade's machine-side definitions — `Api.Machine` and `Api.Decision`
(`src/Effect4/Api.lean:248-249`), `root` (`:252`), `load` (`:256`), `Outcome` (`:265`) and `Run`
(`:272`) — so `Api/HostProtocol.lean:1` imports `Effect4.Api` and `HostProtocol.observe` reads
`Api.Machine` (`:92`). Move those six into a small module below both (they are thirty lines of
abbreviations and one loader), and the facade can import the session; then one import is the
whole language.

---

## 7. What I did not check

- I did not build anything. Every "proved" above is a statement I read with its proof term at the
  cited line, not a green build in this session; the ceiling stamp is `docs/STATE.md:11`.
- I did not read `src/Effect4/Api/RunnerDerived.lean` in full (1,758 generated lines); I read its
  `Refusal` arms to settle F8 and its header.
- I did not check the OCaml engine's driver against the session; `docs/STATE.md:55` and
  `tools/Conform/Effect4/Lcnf.lean:15` are my evidence that the session is not generated.
- I did not check the TypeScript side of the keyed lane (`harness/truth/session/*.ts`) beyond the
  script that runs it (`scripts/check-host-protocol.py:30-60`).
- The proposed `Env` change is argued from `Src.Scoped`'s statement
  (`Laws/Program/Authoring.lean:42-43`), which quantifies over every `Env` and reads only
  `env.names.length`: adding a field cannot break it. That is assumed, not compiled.
