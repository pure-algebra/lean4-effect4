# 2026-10-12 Probe: where a new user stumbles on the authoring API

Status: research note (history, not authority). Base: `9e90f9a1d` on `refactor/phase1-phase3`.
Toolchain: Lean 4.33.1. No tracked file changed, and nothing was committed.

## Question

The owner prepares an initial release. Where does a capable newcomer stumble when writing small
Effect4 programs from the README, the user-facing documents and the API sources?

The probe wrote six programs, one per scenario, and eleven control files. Each file compiled
with `LEAN_NUM_THREADS=2 lake env lean <file>` from the repository root. The probe ran no
`lake build`.

## Know this first

A newcomer who reads this section first avoids the top eight frictions below. Each line rests
on a program or a control in the appendix, or on the source that a finding row names.

1. Import `Effect4.Author` to write programs, and add `Effect4.Run` to run them under a clock or
   a host. `import Effect4.Api` alone has no `eff`, `fork`, `join`, `bindWith` or
   `Api.Author.build`. `import Effect4` brings everything, the library modules included.
2. Open three namespaces: `open Effect4 Effect4.Program Effect4.Program.Authoring`. The `eff do`
   block is scoped syntax, so it exists only where `Effect4.Program.Authoring` is open.
3. Put `set_option autoImplicit false` at the top. Otherwise a misspelled type name becomes an
   implicit variable, and the error points elsewhere.
4. Do not name a top-level definition `main`. Lean reserves it for an `IO` entry point.
5. A program is a `Src NativeOp`, and a value inside it is a `TermSrc`. Write `nat 3`,
   `str "a"`, `Atom.add x y` and `Atom.pair a b`. Prefer `Atom.*` to `app "name" [...]`: a
   misspelled atom string is refused only as a bare `term`.
6. Check a program with `Api.Author.program src`, or a module with
   `Api.Author.build { rows, services, main }`. Both answer a `Built`. `Api.author src` answers a
   `Typed`, which is the only one with `emit`.
7. Read a result yourself. No answer type has `Repr`. Use `b.ty.answer.render` for a type,
   `repr v` for a `Val`, and the `showExit` and `describe` functions of the appendix.
8. Run a pure program with `b.runSync`. Run a program that sleeps with
   `Run.runClock b [millis]`. Run a program that calls a host row with
   `Run.runWith b reactor state`.
9. Read `die asyncFiber` as "the run did not finish", not as a bug. A sleep, a host call or the
   default budget of 1000 commands causes it. A loop of a few hundred rounds needs
   `b.runSync { fuel := 100000 }`.
10. Check `b.closed` before a run. A program that needs a service with no layer builds, and its
    run dies with `missingService`.
11. A service key is two numbers, `⟨⟨name⟩, ⟨code⟩⟩`, with `name ≥ 4`. The code fixes the carrier:
    4 `number`, 5 `boolean`, 6 `void`, 7 `Ref<number>`, 8 `SqlClient`, 9 `KeyValueStore`.
    No other carrier is accepted.
12. There is no `retry`, `timeout`, `catchAll` or `mapError`. Use `catchCause` to remove an error
    from the channel. Build retry and timeout as in program P4.
13. Emit TypeScript with `t.emit name` and `Api.render (.ts e.module)`. The text has no imports.
    The header and the prelude it needs are in `harness/truth/module-imports.ts` and
    `harness/truth/prelude.ts`.
14. A file compiles in about 5 seconds once the modules are built.

## What was read or run (each with its evidence word)

- **Reading**: `README.md`, `AGENTS.md`, `docs/core/api-surface.md`, `docs/STATE.md`, and the
  sources `src/Effect4/Api.lean`, `src/Effect4/Api/*.lean`, `src/Effect4/Author.lean`,
  `src/Effect4/Run/Basic.lean` and `src/Effect4/Program/Authoring*.lean`. The probe followed a
  definition into its module when the API sources named it.
- **Tested**: six programs P1 to P6, and the controls P0, X1, X3 and X7 to X12. The appendix
  lists each file, its final form and its output. The scratch directory is
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e1e92e6e-f6fa-4134-946a-d08ffba1e7ca/scratchpad/usability/`.
- **Tested**: the README's record, Queue, Semaphore, Pool and fold examples (P0, X7). Each
  compiled and answered the value the README states.

## Findings (each with its evidence)

Several things worked. The README examples compiled verbatim and answered as stated (P0, X7).
The scope reader names an unbound variable and an undeclared row (`unbound "y"`,
`unboundRow "ping"`, X9). The checker names a failing release and a join of a non-fiber
(`releaseFails`, `notFiber`, X9). The host session refuses a reply outside the row's answer type
(P5). Retry and timeout behaved as intended once written by hand (P4).

The table ranks the frictions by how many newcomers meet them and how long recovery took.
Every row is a finite probe on the named files, not a theorem.

| # | Friction | Evidence | Cause | Smallest fix | Kind | Cost |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Which import and which `open`. The README says "Import `Effect4.Api`", and that face cannot write a fork. | X8a, X8c: `Unknown identifier eff`, `fork`, `bindWith`, `Api.Author.program`. X8b: `Unknown identifier eff` without the third `open`, with no hint. The README uses `Effect4.Api` and `Effect4`; `docs/core/api-surface.md` §1.3 uses `Effect4.Api.Author` with `Effect4.Library.Queue.Defs`, and §1 names five entry modules and calls `Api` "the older face". | `src/Effect4/Api.lean` imports neither `Program/Authoring/Sugar.lean` nor `Program/Authoring/Services.lean` nor `Api/Author.lean`. `eff` is `scoped syntax` in `Program/Authoring/Sugar.lean` (row 17). The README section "The application face" predates row 332. | A "Start here" block at the top of the README: the two imports, the `open` line, `set_option autoImplicit false`, one five-line program and its check. | doc | S |
| 2 | Nothing prints. A newcomer cannot see a type, an exit or a refusal. | X1: `#eval (Api.author p).map (·.ty)` fails with `Unable to synthesize MonadEval`; `#eval` of a `runSync` result fails with `could not synthesize a Repr`. X3: no `Repr` for `Cause`. Every probe file carries a hand `showExit` and `describe`. The README says "its run answers `7`" and shows no line that prints it. | `Exit` (`src/Effect4/Machine/Exit.lean`), `Cause` and `Reason` (`src/Effect4/Machine/Cause.lean`), `EffTy` (`src/Effect4/Program/Typing/Rules.lean`), `TypeRefusal` and `TypeReason` (`src/Effect4/Program/Typing/Blame.lean`), `Term` (`src/Effect4/Machine/Term.lean`) and `BuildRefusal` derive `DecidableEq` only. `docs/core/api-surface.md` §2 records "`Repr` is not derived (C D12)". | Doc: a README snippet with `Ty.render`, `repr` on `Val` and a `showExit`. API: render functions `ExitV.render`, `TypeRefusal.render` and `BuildRefusal.render`, admitted by exact name in `Test/Audit/AxiomGate.lean` as `Ty.render` is. | doc + API | S + M |
| 3 | A run that does not finish reads as a defect, and three runners report it three ways. | P4: a program that sleeps ends `runSync` with `die asyncFiber`. X12: a 400-round loop at the default budget gives `die asyncFiber` under `runSync`, exit `none` with reason `awaitDecision` under `Run.runPure`, and reason `commandFuel` under `Typed.run`. | `Api.runSync` is `Effect.runSyncExit` (its docstring, `src/Effect4/Api.lean`). `Api.Budget` defaults to 1000 commands. `HostSession.inspect` (`src/Effect4/Api/HostSession.lean`) replays the stored machine at fuel 0 with an empty tape, so `Run.inspect` reports `awaitDecision`, not the fuel that stopped the row. The test clock is named only in the docstring of `Api.run`. | Doc: a "Running" table: pure, sleeps, host rows, long loops, and what `asyncFiber` means. API: `Built.runToEnd : Budget → Except FrontierReason ExitV`, and keep `commandFuel` in `Run.inspect`. | doc + API | S + M |
| 4 | The common Effect combinators are absent. | P4: retry needs 12 lines with `iterateWith`, `Forms.matchCause` and a stated cursor type. Timeout needs `withFiber (Action.raceAllFirst …)` and prints as `Effect.raceAllFirst([...])`, not `Effect.timeout` (P6). P3: `catchIf "err" (bool true)` keeps `string` in the error column; `catchCause` removes it. | `Codegen.Forms.all` (`src/Effect4/Codegen/Forms.lean`) holds 19 forms. Its `duals` table records `timeout`, `retry`, `mapError` and `catch` as dual-call heads with no expansion and no authoring form. rc.112 exports both (`vendor/effect-4.0.0-rc.112/src/Effect.ts:7192`, `:8293`). | Example now: P4's `retry` and `timeout` in a README section. API later: forms `catchAll`, `mapError`, `orElse`, `timeoutFail` and `retryTimes`, each pinned to its rc.112 expansion and given a truth case. | example + API | S + L |
| 5 | A refused atom names nothing. | X9: `app "plus1" [x, nat 2]` and `Atom.add (str "a") (nat 1)` both answer `typing refusal at [1]: term`. `Term` has no `Repr`, so the term cannot be shown. The path is a list of child indices. | `TypeReason.term` is the fallback (`src/Effect4/Program/Typing/Blame.lean`). `TermTypingRefusal` (`src/Effect4/Program/Typing/TermRefusal.lean`) locates records, tuples and folds only. `Authoring.app` takes the atom as a `String`, and the README writes atoms that way. | Doc: write atoms as `Atom.add` (`src/Effect4/Program/Authoring/Atoms.lean`) in the README. API: an `atom` alternative in `TermTypingRefusal` for an unknown name and for argument types. | doc + API | S + M |
| 6 | A missing service or scope builds, and the run dies. | P1 `bare`: `closed false`, then `die missingService`. P2 `leaky`: `acquireWith` with no `scope` builds with a required key and dies the same way. The required key prints as `{ name := { value := 0 }, service := { value := 0 } }`. Effect TypeScript refuses `runSync` of an effect whose `R` is not `never`. | `Api.Author.build` (`src/Effect4/Api/Author.lean`) admits at `⟨table, []⟩` and never tests `Built.closed`. `Built.runSync` runs an open program. | API: `Built.runSync` answers a refusal that names the required keys when the program is not closed. Doc: "check `b.closed`". | API + doc | S |
| 7 | Emitted TypeScript is not a runnable file, and the route to text is hidden. | P6: `t.emit name`, then `Api.render (.ts e.module)`. The module has no imports. It names `add`, `pair`, `eq`, `div` and `ifCase`, which live in `harness/truth/prelude.ts`. Binders print as `a0`, `a1`. Each export has an empty doc comment. Services print as `"k10_4"`. X10: the `Api` docstring's `house0` is `TypeScript.house0`. | `ModuleEmission.module` (`src/Effect4/Codegen/Checked.lean`): "Empty imports are an explicit limit of this producer". The import list is TypeScript data in `harness/truth/module-imports.ts`. | Doc: a README "Emit" snippet, where the prelude lives, and the `house0` docstring repair. API: `Typed.emitText` that writes the import header from Lean data. | doc + API | S + M |
| 8 | Services are numbers whose second half is a type code. | X9: a `string` service is refused as `declared string, signature (some number)`. A key under a reserved name answers `signature none`, with no word "reserved". P1: the TypeScript names the service `"k10_4"`. The README documents none of it. | `nativeServiceTypes` and `nativeServiceTy` (`src/Effect4/Program/Native.lean`) fix six carriers by code. `Author.disagreeingService` checks against `nativeSignature`, not `nativeSignatureWith` (decision D-I, `docs/core/api-surface.md` §2). | Doc: the code table. API: `ServiceDef.of name carrier`, which picks the code and refuses an unsupported carrier by name, and a `reservedName` reason. | doc + API | S + M |
| 9 | Schema input: a guessed name fails, and a refusal has no reason. | P5: `Effect4.Schema.Codec.decode` is unknown; the function is `Effect4.Schema.decode`. `decode` answers `Option Val`, so a wrong-typed field and an extra field both answer `none`. A JSON number needs `Arch.Json.ofNat`. A host reply outside the answer type is refused as `Refusal.envelope`, and the run stays live with exit `none`. | `decode` is declared in namespace `Effect4.Schema` in `src/Effect4/Schema/Codec.lean`. The library has no JSON text reader; `tools/Tools/JsonBridge.lean` is a tool. No declaration answers the README's phrase "checked schema endpoints". | Doc: a schema-input snippet (P5). API: the alias `Schema.Codec.decode`, and a `decodeAt` that answers the failing path and reason. | doc + API | S + M |
| 10 | `autoImplicit` hides a missing type name. | P4: `def showExit : ExitV → String` under the README's `open` line elaborates `ExitV` as an implicit variable. The error says the expected type of `.success` "is not of the form `C ...`". | The run types live in `Effect4.Machine` and are re-exported as `Api.ExitV` and `Api.Val`. Lean's `autoImplicit` is on by default. The library turns it off file by file, and `lakefile.toml` does not. | Doc: `set_option autoImplicit false` in the template. API: export `ExitV` and `Val` into `Effect4.Program.Authoring`. | doc + API | S |
| 11 | A documented example does not compile. | X11: `docs/core/api-surface.md` §1.3 names its program `main`. Lean answers "`main` function must have type `(List String →)? IO …`". | `Module.main` invites the name. | Rename the example's definition to `program`. | doc | S |
| 12 | Two values and ten runners for one job. | P1 to P6: `Api.author` answers `Typed` (has `emit`); `Api.Author.program` answers `Built` (has `closed`, `runSync`, `print`, no `emit`). Runners: `Typed.run`, `Typed.runSync`, `Built.runSync`, `Run.runPure`, `Run.runClock`, `Run.runWith`, `Api.run`, `Api.runSync`, `Api.replay`, `Api.TestClock.run`. | Two faces coexist (`docs/core/api-surface.md` §1, row 332). | Doc: one table "check, run, emit". API: the alias `Built.emit`. | doc + API | S |
| 13 | Small inconsistencies. | `Ref.update current f request` and `Ref.updateWith request f` order their arguments differently. `scope` spells Effect's `scoped`. `Forms.matchCause` takes written names and has no minted form. A missing `fork` under `bind` reports `overloaded, errors` twice (X8c). | `src/Effect4/Program/Authoring/Rows.lean`, `Lifts.lean`, `Codegen/Authoring/Forms.lean`. | Doc lines; a minted `Forms.matchCauseWith`. | doc + API | S |

### Fixes that change no API (doc or example only)

1. README "Start here": the imports, the `open` line, `set_option autoImplicit false`, a program
   and its check (rows 1, 10).
2. README snippets that print a type, an exit and a refusal (row 2).
3. README "Running" table: pure, clock, host, budget, and what `die asyncFiber` means (rows 3, 6).
4. README section with the hand-written `retry` and `timeout` of P4 (row 4).
5. Atoms written as `Atom.add` in every README example (row 5).
6. README "Emit" snippet, the prelude's location, and the `TypeScript.house0` docstring repair
   in `src/Effect4/Api.lean` (row 7).
7. The service code table and the reserved names (row 8).
8. A schema-input snippet modelled on P5 (row 9).
9. The rename of `main` in `docs/core/api-surface.md` §1.3 (row 11).
10. One "check, run, emit" table that maps `Typed` and `Built` to their runners (row 12).

### Fixes that change the API

1. Render functions for `ExitV`, `TypeRefusal` and `BuildRefusal`, gated by exact name (row 2).
2. `Built.runToEnd`, and `commandFuel` kept in `Run.inspect` (row 3).
3. Forms `catchAll`, `mapError`, `orElse`, `timeoutFail` and `retryTimes` with truth cases
   (row 4).
4. An `atom` alternative in `TermTypingRefusal` (row 5).
5. `Built.runSync` refusing a program that is not closed (row 6).
6. `Typed.emitText` with the import header (row 7).
7. `ServiceDef.of` and a `reservedName` reason (row 8).
8. The alias `Schema.Codec.decode` and a located `decodeAt` (row 9).
9. `ExitV` and `Val` exported into `Effect4.Program.Authoring` (row 10).
10. The alias `Built.emit` and a minted `Forms.matchCauseWith` (rows 12, 13).

## Compile times

Each time is the wall time of one `LEAN_NUM_THREADS=2 lake env lean` run, measured by the probe.

| File | Imports | Wall time (final run) |
| --- | --- | --- |
| P0 (README records) | `Effect4.Api` | 5.0 s |
| P1 service and layer | `Effect4.Author` | 6.2 s (10.1 s at the first, cold run) |
| P2 acquireRelease | `Effect4.Author` | 4.5 s |
| P3 fork, join, error | `Effect4.Author` | 5.4 s |
| P4 retry, timeout | `Effect4.Author`, `Effect4.Run` | 6.0 s |
| P5 schema input | `Effect4.Author`, `Effect4.Run`, `Effect4.Api` | 6.0 s (16.2 s once, under load) |
| P6 emit | `Effect4.Author`, `Effect4.Api` | 5.8 s |
| X7 README library examples | `Effect4` | 8.4 s |

Compile time is no friction once the modules are built. The probe built nothing. `Effect4.olean`
is dated 2026-10-11 and `Effect4/Api.olean` 2026-10-12, and both loaded without error.

## What this does not establish

- The probe is one reader's path through finite examples. It measures no other newcomer.
- No emitted TypeScript was type checked or run. The printed text is reported as printed.
- A run's answer is the reference machine's answer under the stated budget. No host was run.
- The ranking is a judgment from this probe, not a measurement over users.
- The probe read `src/Effect4/Program/Authoring*.lean` and a few modules beyond `src/Effect4/Api*`,
  because the API sources name them. A reader restricted to `Api*` meets row 1 sooner.

## Appendix A: the programs

Each program is in its final compiling form. Each compiled with exit code 0 and no warning.
The output block is the file's `#eval` output from the final run.

### P1: a typed service with a layer

File: `P1_ServiceLayer.lean`. Two services, a port and a counter cell, provided by two layers. The second build has no layer: it builds, is not closed, and dies at run time.

```lean
import Effect4.Author
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- A port number, provided by a layer. Key name 10; type code 4 spells `number`. -/
def Port : ServiceDef := { key := ⟨⟨10⟩, ⟨4⟩⟩, carrier := .nat }

/-- A request counter: a `Ref<number>` built by a layer. Type code 7 spells `Ref<number>`. -/
def Counter : ServiceDef := { key := ⟨⟨11⟩, ⟨7⟩⟩, carrier := .refOf .nat }

def portLayer : LayerSrc NativeOp := Port.constant (nat 8080)
def counterLayer : LayerSrc NativeOp := Counter.layer (Ref.make (nat 0))

def handle : Src NativeOp := eff do
  let port ← Port.use
  let c ← Counter.use
  let _ ← Ref.updateWith c (fun n => Atom.add n (nat 1))
  let n ← Ref.get c
  return Atom.pair port n

def server : Src NativeOp := provideAll [portLayer, counterLayer] handle

def built := Api.Author.build { services := [Port, Counter], main := server }

/-- The same handler with no layer: it builds, and it needs both services. -/
def bare := Api.Author.build { services := [Port, Counter], main := handle }

def showExit : Api.ExitV → String
  | .success v => s!"success {repr v}"
  | .failure c => s!"failure {c.reasons.map fun
      | .fail e _ => s!"fail {repr e}"
      | .die d _ => s!"die {repr d}"
      | .interrupt _ _ => "interrupt"}"

#eval match built with
  | .ok b => IO.println s!"type: {b.ty.answer.render}; closed: {b.closed}; exit: {showExit b.runSync}"
  | .error _ => IO.println "refused"

#eval match bare with
  | .ok b => IO.println s!"bare: closed {b.closed}; requires {b.requires.length} keys; exit: {showExit b.runSync}"
  | .error _ => IO.println "refused"

#eval match built with
  | .ok b => match b.typed.emit "server" with
    | .ok emission => IO.println (Api.render (.ts emission.module))
    | .error _ => IO.println "emission refused"
  | .error _ => IO.println "refused"
```

Output:

```text
type: readonly [number, number]; closed: true; exit: success (Val.list [(Val.nat 8080), (Val.nat 1)])
bare: closed false; requires 2 keys; exit: failure [die Effect4.Machine.Defect.missingService]
/**

 */

export const server: Effect.Effect<readonly [number, number], never, never> = Effect.provide(Effect.flatMap(Effect.service(Context.Service<"k10_4", number>("k10_4")), (a0) => Effect.flatMap(Effect.service(Context.Service<"k11_7", Ref.Ref<number>>("k11_7")), (a1) => Effect.flatMap(Ref.update(a1, (a2) => add(a2, 1)), (a2) => Effect.flatMap(Ref.get(a1), (a3) => Effect.succeed(pair(a0, a3)))))), Layer.mergeAll(Layer.effect(Context.Service<"k10_4", number>("k10_4"), Effect.succeed(8080)), Layer.effect(Context.Service<"k11_7", Ref.Ref<number>>("k11_7"), Ref.make(0))))

exit 0, wall 6.2 s
```

### P2: a scoped resource with acquireRelease

File: `P2_AcquireRelease.lean`. A resource acquired in a scope, read, and released into a log cell. The second program forgets the scope.

```lean
import Effect4.Author
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- Open a "connection" (a cell holding 42), read it, and record the release in a log cell. -/
def useConnection : Src NativeOp := eff do
  let log ← Ref.make (nat 0)
  let v ← scope (eff do
    let conn ← acquireWith (Ref.make (nat 42)) (fun _conn => Ref.set log (nat 1))
    Ref.get conn)
  let closed ← Ref.get log
  return Atom.pair v closed

/-- The same, with the scope forgotten: it builds, requires `Scope`, and dies at run time. -/
def leaky : Src NativeOp := eff do
  let conn ← acquireWith (Ref.make (nat 42)) (fun _conn => Forms.void)
  Ref.get conn

def describe : Except Api.BuildRefusal Api.Built → String
  | .ok b => s!"ok: answer {b.ty.answer.render}, error {b.ty.error.render}, requires {repr b.requires}"
  | .error (.scope r) => s!"scope refusal at {r.path}: {repr r.reason}"
  | .error (.typing r) => s!"typing refusal at {r.path}: {r.reason.head}"
  | .error (.admission _) => "admission refusal"
  | .error (.serviceCarrier k _ _) => s!"service carrier {repr k}"

def showExit : Api.ExitV → String
  | .success v => s!"success {repr v}"
  | .failure c => s!"failure {c.reasons.map fun
      | .fail e _ => s!"fail {repr e}"
      | .die d _ => s!"die {repr d}"
      | .interrupt _ _ => "interrupt"}"

#eval IO.println (describe (Api.Author.program useConnection))
#eval match Api.Author.program useConnection with
  | .ok b => IO.println (showExit b.runSync)
  | .error _ => IO.println "refused"
#eval IO.println (describe (Api.Author.program leaky))
#eval match Api.Author.program leaky with
  | .ok b => IO.println (showExit b.runSync)
  | .error _ => IO.println "refused"
#eval match Api.author useConnection with
  | .ok t => match t.emit "useConnection" with
    | .ok e => IO.println (Api.render (.ts e.module))
    | .error _ => IO.println "emission refused"
  | .error _ => IO.println "refused"
```

Output:

```text
ok: answer readonly [number, number], error never, requires []
success (Val.list [(Val.nat 42), (Val.nat 1)])
ok: answer number, error never, requires [{ name := { value := 0 }, service := { value := 0 } }]
failure [die Effect4.Machine.Defect.missingService]
/**

 */

export const useConnection: Effect.Effect<readonly [number, number], never, never> = Effect.flatMap(Ref.make(0), (a0) => Effect.flatMap(Effect.scoped(Effect.flatMap(Effect.acquireRelease(Ref.make(42), (a1, a2) => Ref.set(a0, 1)), (a1) => Ref.get(a1))), (a1) => Effect.flatMap(Ref.get(a0), (a2) => Effect.succeed(pair(a1, a2)))))

exit 0, wall 4.5 s
```

### P3: fork and join with an error channel

File: `P3_ForkJoinError.lean`. Two forked workers; one fails with a text error. `catchIf` recovers the value and keeps `string` in the type; `catchCause` removes it.

```lean
import Effect4.Author
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- 100 / n, failing with a text error at zero. -/
def safeDiv (n : TermSrc) : Src NativeOp := eff do
  if Atom.eq n (nat 0) then
    fail (str "division by zero")
  else
    return Atom.div (nat 100) n

/-- Two workers in parallel; the second fails, and the parent recovers with 0. -/
def recovered : Src NativeOp := eff do
  let a ← fork (safeDiv (nat 4))
  let b ← fork (safeDiv (nat 0))
  let x ← join a
  let y ← catchIf "err" (bool true) (join b) (succeed (nat 0))
  return Atom.pair x y

/-- The same, with the failure left in the error channel. -/
def unrecovered : Src NativeOp := eff do
  let a ← fork (safeDiv (nat 4))
  let b ← fork (safeDiv (nat 0))
  let x ← join a
  let y ← join b
  return Atom.pair x y

def describe : Except Api.BuildRefusal Api.Built → String
  | .ok b => s!"ok: answer {b.ty.answer.render}, error {b.ty.error.render}"
  | .error (.scope r) => s!"scope refusal at {r.path}: {repr r.reason}"
  | .error (.typing r) => s!"typing refusal at {r.path}: {r.reason.head}"
  | .error (.admission _) => "admission refusal"
  | .error (.serviceCarrier k _ _) => s!"service carrier {repr k}"

def showExit : Api.ExitV → String
  | .success v => s!"success {repr v}"
  | .failure c => s!"failure {c.reasons.map fun
      | .fail e _ => s!"fail {repr e}"
      | .die d _ => s!"die {repr d}"
      | .interrupt _ _ => "interrupt"}"

def exitOf : Except Api.BuildRefusal Api.Built → String
  | .ok b => showExit b.runSync
  | .error _ => "refused"

/-- `catchCause` takes the error out of the channel; `catchIf` keeps it. -/
def viaCause : Src NativeOp := eff do
  let b ← fork (safeDiv (nat 0))
  catchCause "cause" (join b) (succeed (nat 0))

#eval IO.println (describe (Api.Author.program recovered))
#eval IO.println (exitOf (Api.Author.program recovered))
#eval IO.println (describe (Api.Author.program unrecovered))
#eval IO.println (exitOf (Api.Author.program unrecovered))
#eval IO.println (describe (Api.Author.program viaCause))
#eval IO.println (exitOf (Api.Author.program viaCause))
```

Output:

```text
ok: answer readonly [number, number], error string
success (Val.list [(Val.nat 25), (Val.nat 0)])
ok: answer readonly [number, number], error string
failure [fail Effect4.Machine.Err.text "division by zero"]
ok: answer number, error never
success (Val.nat 0)
exit 0, wall 5.4 s
```

### P4: retry and timeout, by hand

File: `P4_RetryTimeout.lean`. No `retry` or `timeout` exists, so both are written over `iterateWith` and `raceAllFirst`. `runSync` cannot move the clock; `Run.runClock` can.

```lean
import Effect4.Author
import Effect4.Run
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- A flaky call: fails until its third attempt, counted in `calls`. -/
def flaky (calls : TermSrc) : Src NativeOp := eff do
  let n ← Ref.updateAndGetWith calls (fun c => Atom.add c (nat 1))
  if Atom.lt n (nat 3) then
    fail (str "transient")
  else
    return Atom.mul n (nat 10)

/-- `Effect.retry(body, { times })`, by hand: a loop over (attempts left, last answer). -/
def retry (times : Nat) (body : Src NativeOp) : Src NativeOp := eff do
  let r ← iterateWith (Atom.pair (nat (times + 1)) Atom.none)
    { while_ := fun c => Atom.and (Atom.not (Atom.isSome (Atom.snd c)))
                                   (Atom.not (Atom.isZero (Atom.fst c)))
      body := fun _ => Forms.matchCause "v" "e" body (Atom.some (var "v")) Atom.none
      step := fun c a => Atom.pair (Atom.pred (Atom.fst c)) a
      result := fun c => Atom.snd c
      cursorTy := some (.prod .nat (.option .nat)) }
  selectOptionWith r (fail (str "gave up")) (fun v => succeed v)

def retried : Src NativeOp := eff do
  let calls ← Ref.make (nat 0)
  retry 5 (flaky calls)

/-- `Effect.timeout(body, millis)`, by hand: race the body against a sleep that fails. -/
def timeout (millis : Nat) (body : Src NativeOp) : Src NativeOp :=
  withFiber (Action.raceAllFirst
    [body, eff do
      let _ ← Effect.sleep (nat millis)
      fail (str "timed out")])

def slow : Src NativeOp := eff do
  let _ ← Effect.sleep (nat 5000)
  return nat 1

def timedOut : Src NativeOp := timeout 100 slow

def describe : Except Api.BuildRefusal Api.Built → String
  | .ok b => s!"ok: answer {b.ty.answer.render}, error {b.ty.error.render}"
  | .error (.scope r) => s!"scope refusal at {r.path}: {repr r.reason}"
  | .error (.typing r) => s!"typing refusal at {r.path}: {r.reason.head}"
  | .error (.admission _) => "admission refusal"
  | .error (.serviceCarrier k _ _) => s!"service carrier {repr k}"

def showExit : Api.ExitV → String
  | .success v => s!"success {repr v}"
  | .failure c => s!"failure {c.reasons.map fun
      | .fail e _ => s!"fail {repr e}"
      | .die d _ => s!"die {repr d}"
      | .interrupt _ _ => "interrupt"}"

#eval IO.println (describe (Api.Author.program retried))
#eval match Api.Author.program retried with
  | .ok b => IO.println (showExit b.runSync)
  | .error _ => IO.println "refused"
#eval IO.println (describe (Api.Author.program timedOut))
#eval match Api.Author.program timedOut with
  | .ok b => IO.println (showExit b.runSync)
  | .error _ => IO.println "refused"

-- `runSync` cannot move the clock; the test clock is the decision tape.
#eval match Api.Author.program timedOut with
  | .ok b => IO.println ((Run.runClock b [100]).exit.map showExit)
  | .error _ => IO.println "refused"
#eval match Api.Author.program (timeout 10000 slow) with
  | .ok b => IO.println ((Run.runClock b [5000]).exit.map showExit)
  | .error _ => IO.println "refused"
```

Output:

```text
ok: answer number, error string
success (Val.nat 30)
ok: answer number, error string
failure [die Effect4.Machine.Defect.asyncFiber]
(some (failure [fail Effect4.Machine.Err.text "timed out"]))
(some (success (Val.nat 1)))
exit 0, wall 6.0 s
```

### P5: a schema-checked input

File: `P5_SchemaInput.lean`. A structure with `deriving Modeled` gives the record type of a host row. JSON input is decoded under that type before a reactor answers the row. The last two runs answer with an ill-typed value.

```lean
import Effect4.Author
import Effect4.Run
import Effect4.Api
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- The request a host sends: a Lean structure tied to a record `Ty`. -/
structure Signup where
  email : String
  age : Nat
deriving Effect4.Schema.Modeled

def signupTy : Ty := Effect4.Schema.Modeled.ty Signup

/-- The host row that delivers the request; its answer type is the schema. -/
def readSignup : RowDef := Row.host "readSignup" .unit signupTy

def register : Src NativeOp := eff do
  let req ← Row.call readSignup unit
  if Atom.lt (field req "age") (nat 18) then
    fail (str "too young")
  else
    return field req "email"

def built := Api.Author.build { rows := [readSignup], main := register }

/-- The input arrives as JSON and is decoded under the row's answer type. -/
def goodJson : Json := .obj [("email", .str "ada@example.com"), ("age", Arch.Json.ofNat 36)]
def badJson : Json := .obj [("email", .str "bob@example.com"), ("age", .str "old")]
def extraJson : Json :=
  .obj [("email", .str "eve@example.com"), ("age", Arch.Json.ofNat 20), ("admin", .bool true)]

def showExit : Api.ExitV → String
  | .success v => s!"success {repr v}"
  | .failure c => s!"failure {c.reasons.map fun
      | .fail e _ => s!"fail {repr e}"
      | .die d _ => s!"die {repr d}"
      | .interrupt _ _ => "interrupt"}"

/-- A host that answers every call with one decoded value. -/
def replyWith (v : Api.Val) : Run.Reactor Unit := fun _row _request st =>
  some (.ofExit (.success v), st)

def serve (j : Json) : String :=
  match built, Effect4.Schema.decode signupTy j with
  | .error _, _ => "build refused"
  | _, none => "input refused by the schema"
  | .ok b, some v =>
    match (Run.runWith b (replyWith v) ()).1.exit with
    | some e => showExit e
    | none => "still running"

#eval IO.println (signupTy.render)
#eval IO.println (serve goodJson)
#eval IO.println (serve badJson)
#eval IO.println (serve extraJson)

def youngJson : Json := .obj [("age", Arch.Json.ofNat 12), ("email", .str "kid@example.com")]
#eval IO.println (serve youngJson)

-- A host that skips the schema and replies with a number: does the session refuse it?
#eval match built with
  | .ok b =>
    let (r, _) := Run.runWith b (replyWith (Api.Val.nat 3)) ()
    IO.println s!"exit: {r.exit.map showExit}; phases: {r.phases.length}; outstanding: {r.outstanding.length}"
  | .error _ => IO.println "build refused"

#eval match built with
  | .ok b =>
    let (r, _) := Run.runWith b (replyWith (Api.Val.nat 3)) ()
    IO.println s!"phases: {repr r.phases}"
  | .error _ => IO.println "build refused"
```

Output:

```text
{ readonly age: number; readonly email: string }
success (Val.str "ada@example.com")
input refused by the schema
input refused by the schema
failure [fail Effect4.Machine.Err.text "too young"]
exit: none; phases: 4; outstanding: 1
phases: [Effect4.Api.HostSession.Phase.progressed,
 Effect4.Api.HostSession.Phase.bound,
 Effect4.Api.HostSession.Phase.refused (Effect4.Api.HostSession.Refusal.envelope),
 Effect4.Api.HostSession.Phase.refused (Effect4.Api.HostSession.Refusal.noCall)]
exit 0, wall 6.0 s
```

### P6: emitting TypeScript

File: `P6_EmitTypeScript.lean`. A fork and join program and its hand-written timeout, emitted as modules and rendered to text.

```lean
import Effect4.Author
import Effect4.Api
open Effect4 Effect4.Program Effect4.Program.Authoring

def safeDiv (n : TermSrc) : Src NativeOp := eff do
  if Atom.eq n (nat 0) then
    fail (str "division by zero")
  else
    return Atom.div (nat 100) n

def parallel : Src NativeOp := eff do
  let a ← fork (safeDiv (nat 4))
  let b ← fork (safeDiv (nat 5))
  let x ← join a
  let y ← join b
  return Atom.add x y

def timeout (millis : Nat) (body : Src NativeOp) : Src NativeOp :=
  withFiber (Action.raceAllFirst
    [body, eff do
      let _ ← Effect.sleep (nat millis)
      fail (str "timed out")])

def guarded : Src NativeOp := timeout 1000 parallel

/-- Emit a closed program as a TypeScript module, or say why not. -/
def emit (name : String) (src : Src NativeOp) : String :=
  match Api.author src with
  | .error _ => "author refused"
  | .ok t => match t.emit name with
    | .error _ => "emission refused"
    | .ok emission => Api.render (.ts emission.module)

#eval IO.println (emit "parallel" parallel)
#eval IO.println (emit "guarded" guarded)

-- The round trip: does the printed program read back as itself?
#eval match Api.author guarded with
  | .ok t => IO.println s!"readable: {Api.readable t.program}"
  | .error _ => IO.println "refused"
```

Output:

```text
/**

 */

export const parallel: Effect.Effect<number, string, never> = Effect.flatMap(Effect.forkChild(ifCase(() => eq(4, 0), () => Effect.fail("division by zero"), () => Effect.succeed(div(100, 4))), { startImmediately: true, uninterruptible: "inherit" }), (a0) => Effect.flatMap(Effect.forkChild(ifCase(() => eq(5, 0), () => Effect.fail("division by zero"), () => Effect.succeed(div(100, 5))), { startImmediately: true, uninterruptible: "inherit" }), (a1) => Effect.flatMap(Fiber.join(a0), (a2) => Effect.flatMap(Fiber.join(a1), (a3) => Effect.succeed(add(a2, a3))))))

/**

 */

export const guarded: Effect.Effect<number, string, never> = Effect.raceAllFirst([Effect.flatMap(Effect.forkChild(ifCase(() => eq(4, 0), () => Effect.fail("division by zero"), () => Effect.succeed(div(100, 4))), { startImmediately: true, uninterruptible: "inherit" }), (a0) => Effect.flatMap(Effect.forkChild(ifCase(() => eq(5, 0), () => Effect.fail("division by zero"), () => Effect.succeed(div(100, 5))), { startImmediately: true, uninterruptible: "inherit" }), (a1) => Effect.flatMap(Fiber.join(a0), (a2) => Effect.flatMap(Fiber.join(a1), (a3) => Effect.succeed(add(a2, a3)))))), Effect.flatMap(Effect.sleep(1000), (a0) => Effect.fail("timed out"))])

readable: true
exit 0, wall 5.8 s
```

## Appendix B: the controls

Each control is one file in the scratch directory. The result column quotes the compiler or the `#eval` output.

| File | What it tries | Result |
| --- | --- | --- |
| `P0_ReadmeRecords.lean` | The README's record example, checked with `Api.author` | compiles; `ok` (5.0 s) |
| `X1_explore.lean` | `#eval` of a type, an exit and an inspection | `Unable to synthesize MonadEval`; `could not synthesize a Repr or ToString instance` |
| `X3_catch.lean` | `catchCause` typing; `repr` of a failure's cause | error column `never`; `failed to synthesize Repr (Cause …)` |
| `X7_ReadmeExamples.lean` | The README's Queue, Semaphore, Pool and fold examples under `import Effect4` | answers 7, `[1, 7]`, 7 and 203, as the README states (8.4 s) |
| `X8a_ApiOnly.lean` | `eff`, `fork` and `join` under `import Effect4.Api` alone | `Unknown identifier eff` |
| `X8b_NoOpen.lean` | `eff` under `import Effect4.Author` without opening `Effect4.Program.Authoring` | `Unknown identifier eff` |
| `X8c_ApiOnlyWords.lean` | `fork`, `Api.Author.program` and `bindWith` under `import Effect4.Api` | `Unknown identifier` for each; `overloaded, errors` for `bind` |
| `X9_Mistakes.lean` | Nine common mistakes | atom typo and wrong atom type: `term` at `[1]`; unbound name: `unbound "y"`; failing release: `releaseFails`; string service: `declared string, signature (some number)`; unprovided service: builds, `die missingService`; join of a number: `notFiber`; undeclared row: `unboundRow "ping"`; reserved key name: `signature none` |
| `X10_RenderExpr.lean` | The `Api` docstring's `TypeScript.Render.expr house0 0 e` | `Unknown identifier house0`; `TypeScript.house0` works |
| `X11_ApiSurfaceExample.lean` | `docs/core/api-surface.md` §1.3 verbatim | `main function must have type (List String →)? IO …`; compiles after the rename |
| `X12_Fuel.lean` | A loop of 10, 100 and 400 rounds at the default budget | 400 rounds: `runSync` `die asyncFiber`; `Run.runPure` exit `none`, reason `awaitDecision`; `Typed.run` reason `commandFuel`; `{ fuel := 100000 }` answers 400 |
