import Test.Dogfood.Stage
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.Author
import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Rows
import Effect4.Laws.Program.Authoring.Sugar

/-!
# p1: an HTTP call with a timeout, a retry schedule, a typed error and a cache

The rc.112 source is `Test/Dogfood/rc112/p1-http-cache.ts`. A 2 s `Effect.timeout` bounds each
attempt of a quote fetch, and failures retry on an exponential schedule. A 404 is a typed
`HttpError` that the schedule does not retry, and `Cache` serves the second lookup. `run-p1.ts` ran it on
effect 4.0.0-rc.112 under bun 1.4.2 against a scripted `fetch` (`Test/Dogfood/rc112/hostruns.log`):
attempt 1 hangs until the timeout aborts its `AbortSignal`, attempt 2 answers 503, attempt 3
answers the quote, and the program answers `42`. A 404 fails after one call.

This battery ports the model probe's program 1 and its form laws
(`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/ProbeProgram1.lean`,
`ProbeFormLaws.lean` at the same revision), with the verifier's checks of
`verify/VerifyPrograms.lean` §1 and §1b.

**Changes since 2026-09-30.**
* `outstanding` answers `Await` records (row 16), not tuples. The scripted host keeps the probe's
  policy and plays it over `Run` (`src/Effect4/Run.lean`). `Run.runWith` cannot hold a call
  unanswered, which this host's first attempt needs: its drive stops when the host declines.
* Records landed (row 119). A host row may now answer a `Quote` record, and two quotes' prices
  add (section 6). The key-value cache holds strings (DB-15), so the program still keeps the
  body as text.
* The forms and the program are the probe's, unchanged.

**What the language refuses** (section 6): `HttpError{status: number, url}` as a typed failure;
a `Quote` record in the cache; the forms `retry` and `catchTag` (DI-89, DI-39) and `timeout`. The
retry test compares the status text with `"503"`, where rc.112 reads `status >= 500`. When the
timeout gives up on attempt 1, the session retires the call and records it
(`Run.Observation.retired`), where rc.112 aborts the call's `AbortSignal`; the host protocol has
no retirement edge (R6, parked). The retry loop's cursor annotation keeps the program outside the
readable domain (DI-91).

**Waits on:** R10 with DI-89, DI-39 and DI-91 (the forms, with a readable expansion); R3 and
row 120 (the error payload); R7 and row 82 (`Cache` keeps code); R6, parked (the retirement
notice). The slices of row 204 that move it: error payloads (row 120), and the derived forms
beside them.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.P1HttpCache

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The forms, with the one obligation that comes for free

A form is a Lean function over the authoring lifts (DI-89's third route). DI-89 asks of a form a
typing lemma and one behaviour law; requirement R10 adds lexical well-scoping, reader admission,
a readable expansion and a stable identity. These two forms meet lexical well-scoping only. -/

/-- `Effect.timeout(body, millis)` as rc.112 builds it
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3677-3727`: `raceFirst(self, sleep(d) *>
fail(TimeoutError))`, where the first exit wins). The first success wins the language's race
(`raceAll`, `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:1477-1533`), and nothing re-raises
a captured exit. So the form forks both entrants and races their `await`s, which never fail. It
interrupts the loser, which waits for it, and joins the winner, which re-raises its failure. -/
def timeoutForm (body : Src NativeOp) (millis : TermSrc) (timedOut : TermSrc) : Src NativeOp :=
  eff do
    let entrant ← fork body
    let timer ← fork (andThen (Effect.sleep millis) (fail timedOut))
    let winner ← withFiber (Action.raceAll
      [andThen (await entrant) (succeed (nat 0)), andThen (await timer) (succeed (nat 1))])
    ifElse (app "eq" [winner, nat 0])
      (andThen (withFiber (Action.interrupt timer)) (join entrant))
      (andThen (withFiber (Action.interrupt entrant)) (join timer))

/-- `Effect.retry(attempt, { schedule: exponential(base) ∘ upTo(times), while })`
(`vendor/effect-4.0.0-rc.112/src/internal/schedule.ts:51-80`). The attempt runs once, and again
after each retryable typed failure while retries remain, sleeping `base · 2^k` before retry
`k + 1`. The form catches no defect and no interruption, as rc.112 retries typed failures only. The
cursor is (retries so far, next delay, last answer or error). `answerTy` and `errorTy` state the
cursor's type, which no initial value spells. -/
def retryForm (attempt : Src NativeOp) (retryable : TermSrc → TermSrc) (times base : Nat)
    (answerTy errorTy : Ty) : Src NativeOp :=
  let cursorTy : Ty := .prod .nat (.prod .nat (.prod (.option answerTy) (.option errorTy)))
  bindName "retry.last"
    (iterateWith (app "pair" [nat 0, app "pair" [nat base, app "pair" [app "none" [], app "none" []]]])
      { cursorTy := some cursorTy
        -- go on while no success yet, and (first attempt, or a retryable error with retries left)
        while_ := fun c =>
          app "and" [app "not" [app "isSome" [app "fst" [app "snd" [app "snd" [c]]]]],
            app "or" [app "eq" [app "fst" [c], nat 0],
              app "lt" [app "fst" [c], nat (times + 1)]]]
        body := fun c => eff do
          let _ ← ifElse (app "lt" [nat 0, app "fst" [c]])
            (Effect.sleep (app "fst" [app "snd" [c]])) (succeed unit)
          catchIf "retry.error" (retryable (var "retry.error"))
            (bindName "retry.answer" attempt fun a =>
              succeed (app "pair" [app "some" [a], app "none" []]))
            (succeed (app "pair" [app "none" [], app "some" [var "retry.error"]]))
        step := fun c last =>
          app "pair" [app "succ" [app "fst" [c]],
            app "pair" [app "mul" [app "fst" [app "snd" [c]], nat 2], last]]
        result := fun c => app "snd" [app "snd" [c]] })
    fun last =>
      selectOption "retry.ok" (app "fst" [last])
        (selectOption "retry.err" (app "snd" [last])
          (failCause (Cause.die (str "retry: no attempt ran")))
          (fail (var "retry.err")))
        (succeed (var "retry.ok"))

/-- The timeout form is scoped for every scoped body, duration and timeout value: lexical
well-scoping, one of R10's per-form obligations. It establishes no typing lemma and no behaviour
law, and nothing about rc.112's `raceFirst`, whose entrants fork as daemons. -/
theorem timeoutForm_scoped {body : Src NativeOp} {millis timedOut : TermSrc}
    (h0 : body.Scoped) (h1 : millis.Scoped) (h2 : timedOut.Scoped) :
    (timeoutForm body millis timedOut).Scoped := by
  unfold timeoutForm; authoring_scoped

/-- The retry form is scoped for every scoped attempt and every retry test that keeps scoping:
lexical well-scoping, one of R10's per-form obligations. It establishes no typing lemma and no
behaviour law: not the attempt count, the delays, interruption or finalizer runs. -/
theorem retryForm_scoped {attempt : Src NativeOp} {retryable : TermSrc → TermSrc}
    (times base : Nat) (answerTy errorTy : Ty)
    (h0 : attempt.Scoped) (h1 : ∀ e : TermSrc, e.Scoped → (retryable e).Scoped) :
    (retryForm attempt retryable times base answerTy errorTy).Scoped := by
  unfold retryForm
  authoring_scoped
  -- the one goal the tactic leaves: the caller's test applied to the bound error
  exact h1 _ (var_scoped _)

/-- Red control: a source that emits a variable no binder holds. -/
def leaky : Src NativeOp := fun _ _ => .ok (.succeed (.var 99))

/-- Red control: `leaky` is provably not scoped, so the two scoping theorems say something. -/
theorem leaky_not_scoped : ¬ leaky.Scoped := fun h =>
  absurd (h.holds {} [] (.succeed (.var 99)) rfl) (by decide)

/-! ## 2. The program -/

/-- `GET /quotes/:symbol`: the host answers the body as text, or fails with (tag, message). -/
def getQuote : RowDef := Row.host "Http.getQuote" .string .string (.prod .string .string)

def kv : Package := Package.ofRows "kv" Packages.keyValueStoreMemory

/-- Retry network failures, timeouts and exactly `"503"`: rc.112's `status >= 500` needs a number
in the error, which the error column cannot hold (section 6). -/
def retryable (e : TermSrc) : TermSrc :=
  app "or" [app "tagIs" [str "NetworkError", e],
    app "or" [app "tagIs" [str "Timeout", e], app "eq" [app "snd" [e], str "503"]]]

def fetchQuote (symbol : TermSrc) : Src NativeOp :=
  retryForm
    (timeoutForm (Row.call getQuote symbol) (nat 2000)
      (app "pair" [str "Timeout", str "2000 ms"]))
    retryable 3 100 .string (.prod .string .string)

/-- The program, with the host's key-value store as the cache. `Cache` keeps its `lookup` and
creation context, shares in-flight misses, caches failures and expires entries; this program
does none of that. -/
def program1 : Module NativeOp := Package.install [kv]
  { rows := [getQuote]
    main := eff do
      let store ← Row.call (kv.op "Kv.make") unit
      let cached ← Row.call (kv.op "get") (app "pair" [store, str "EFX"])
      selectOption "hit" cached
        (eff do
          let body ← fetchQuote (str "EFX")
          let _saved ← Row.call (kv.op "set") (app "pair" [store, app "pair" [str "EFX", body]])
          return body)
        (succeed (var "hit")) }

/-- `fetchQuote("NOPE")` alone, as the second half of `run-p1.ts` runs it. -/
def fetchModule : Module NativeOp := { rows := [getQuote], main := fetchQuote (str "NOPE") }

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

-- It builds: typed against its own row table and admitted.
#guard verdict program1 = "built"
#guard (built? program1).map (fun b => (b.ty.answer, b.ty.error)) = some (.string, .prod .string .string)

/-! ## 3. The run under a scripted host -/

/-- The host's answer to the HTTP row, by call ordinal: `none` never answers (the host is still
working when the program gives up). -/
abbrev Script := Nat → Option Effect4.Api.HostSession.Answer

/-- `run-p1.ts`'s first scenario: attempt 1 hangs, attempt 2 answers 503, attempt 3 the body. -/
def ok503thenBody : Script
  | 0 => none
  | 1 => some (.ofExit (.failure (Cause.fail (.tagged "HttpError" "503"))))
  | _ => some (.ofExit (.success (.str "{\"symbol\":\"EFX\",\"price\":21}")))

/-- The probe's red control: attempt 2 answers 404, which is not retryable. -/
def ok404 : Script
  | 0 => none
  | 1 => some (.ofExit (.failure (Cause.fail (.tagged "HttpError" "404"))))
  | _ => some (.ofExit (.success (.str "unreachable")))

/-- `run-p1.ts`'s second scenario: every call answers 404. -/
def always404 : Script := fun _ => some (.ofExit (.failure (Cause.fail (.tagged "HttpError" "404"))))

/-- The host: the key-value rows answer at once, the HTTP row by the script. -/
def hostAnswer (b : Effect4.Api.Built) (script : Script) (httpCall allocated : Nat)
    (op : NativeOp) : Option Effect4.Api.HostSession.Answer :=
  match op with
  | .external i =>
    if some i = b.positionOf "Kv.make" then some (.ofExit (.success (.nat allocated)))
    else if some i = b.positionOf "get" then some (.ofExit (.success .none))
    else if some i = b.positionOf "set" then some (.ofExit (.success .unit))
    else if some i = b.positionOf "Http.getQuote" then script httpCall
    else some (.ofExit (.success .unit))
  | _ => none

structure Driver where
  run : Run
  httpCalls : Nat := 0
  /-- Calls the host received and does not answer: bound in the session, with no reply. -/
  hanging : List Effect4.Api.HostSession.Key := []

/-- One step of the probe's policy. The driver binds a fresh outstanding call at once (the host
has received it). The host answers it at once or never, and an unanswered call hangs. With nothing
to answer, the driver flushes; when that adds no trace event, it moves the clock by 100 ms. -/
def step (script : Script) (d : Driver) : Driver :=
  let s := d.run
  match s.outstanding.filter (fun a => !(d.hanging.contains ⟨a.fiber, a.token⟩)) with
  | a :: _ =>
    let key : Effect4.Api.HostSession.Key := ⟨a.fiber, a.token⟩
    let isHttp : Bool := match a.op with
      | .external i => some i == s.built.positionOf "Http.getQuote"
      | _ => false
    let calls := if isHttp then d.httpCalls + 1 else d.httpCalls
    match hostAnswer s.built script d.httpCalls s.machine.state.externals.allocated.length a.op with
    | none =>
      let bindOnly := match Effect4.Api.HostSession.Call.at s key with
        | some call => [Effect4.Api.Runner.Command.bind call key.token]
        | none => []
      { d with run := s.play bindOnly, hanging := d.hanging ++ [key], httpCalls := calls }
    | some answer => { d with run := s.answer key answer, httpCalls := calls }
  | [] =>
    let flushed := s.control Effect4.Api.flush
    if flushed.machine.trace.length == s.machine.trace.length then
      { d with run := flushed.control (.advance (ClockMillis.ofNat 100)) }
    else { d with run := flushed }

def drive (script : Script) : Nat → Driver → Driver
  | 0, d => d
  | n + 1, d => drive script n (step script d)

/-- What a run shows: the root's exit, the HTTP calls the host received, the replies applied,
and the calls the session retired with whether a reply was pending for each. -/
structure Shown where
  root : Option ExitV
  httpCalls : Nat
  applied : Nat
  retired : Nat
  retiredPending : List Bool
deriving DecidableEq

def runLive (m : Module NativeOp) (script : Script) : Option Shown :=
  (built? m).map fun b =>
    let d := drive script 400 { run := (Run.open b "p1").play Rows.start }
    ⟨d.run.exit, d.httpCalls, d.run.session.applied, d.run.session.retired.length,
      d.run.session.retired.map (·.pending.isSome)⟩

-- The first scenario: the timeout gives up on the hanging call, the form retries the 503, and
-- the third call answers. The root succeeds with the body after three HTTP calls, and the session
-- retired the abandoned call with no reply pending. rc.112 answers 42 here, the sum of the two
-- prices; this program keeps the body as text.
#guard (runLive program1 ok503thenBody).map (·.root) =
  some (some (.success (.str "{\"symbol\":\"EFX\",\"price\":21}")))
#guard (runLive program1 ok503thenBody).map (fun r => (r.httpCalls, r.retired, r.retiredPending)) =
  some (3, 1, [false])
-- The probe's red control: a 404 is not retryable, so it reaches the root after two calls.
#guard (runLive program1 ok404).map (·.root) =
  some (some (.failure (Cause.fail (.tagged "HttpError" "404"))))
#guard (runLive program1 ok404).map (fun r => (r.httpCalls, r.retired)) = some (2, 1)
-- `run-p1.ts`'s 404 run: `fetchQuote("NOPE")` fails after one call, as rc.112 does; its error
-- carries the status as text, where rc.112's carries `{status: 404, url}`.
#guard (runLive fetchModule always404).map (fun r => (r.root, r.httpCalls, r.retired)) =
  some (some (.failure (Cause.fail (.tagged "HttpError" "404"))), 1, 0)

/-! ## 4. Printing -/

/-- The forms alone, as closed programs: the retry form over a constant attempt, the timeout form
over a constant body. -/
def retryAlone : Option Effect4.Api.Program :=
  (elaborate (retryForm (succeed (str "ok")) (fun _ => bool true) 3 100 .string .string)).toOption
def timeoutAlone : Option Effect4.Api.Program :=
  (elaborate (timeoutForm (succeed (str "ok")) (nat 2000) (str "late"))).toOption

-- The program prints as TypeScript, and its printing does not read back.
#guard (built? program1).map (fun b => printedOf b) = some (true, false)
-- The reader refuses at the retry loop's cursor annotation: an annotated loop prints its type,
-- which no reader reads (DI-91; "no reader of types exists, by design", B19).
#guard (built? program1).map (fun b => match Effect4.Api.roundTrip b.program b.table with
    | .error (.annotation site) => site == "local const"
    | _ => false) = some true
-- The retry form alone types, and the reader refuses its printing at the same annotation.
#guard (retryAlone.bind (Effect4.Api.typeOf ·)).isSome
#guard retryAlone.map (Effect4.Api.readable ·) = some false
#guard retryAlone.map (fun p => match Effect4.Api.roundTrip p with
    | .error (.annotation site) => site == "local const"
    | _ => false) = some true
-- Green control: the timeout form alone reads back.
#guard timeoutAlone.map (Effect4.Api.readable ·) = some true

/-! ## 5. Which theorem reaches the program -/

-- In neither fragment, and with a non-empty row table: `run_eq_ref`, which holds at the empty row
-- table only, does not reach it either.
open Effect4.Program.Denote in
#guard (built? program1).map (fun b => (Straight b.program, Looped b.program, b.table.isEmpty)) =
  some (false, false, false)
-- `run_eq_ref` is stated for the run at the empty row table with no answers. There the program
-- stops at its first host call: a live frontier, with the root still running.
#guard (built? program1).map (fun b => ((Effect4.Api.run b.program 4000).outcome,
    (Effect4.Api.run b.program 4000).exit)) = some (Effect4.Api.Outcome.frontier, none)
-- Green control: a program with no host row finishes under the same entry point.
#guard retryAlone.map (fun p => (Effect4.Api.run p 4000).outcome) = some Effect4.Api.Outcome.finished

/-! ## 6. What the language refuses, and what it now admits -/

/-- `class HttpError extends Data.TaggedError("HttpError")<{ status: number; url: string }>`. -/
def httpErrorModule : Module NativeOp :=
  program (fail (record
    [("_tag", false, .lit "HttpError"), ("status", false, .nat), ("url", false, .string)]
    [("_tag", str "HttpError"), ("status", nat 404), ("url", str "https://api.example.com/quotes/NOPE")]))

/-- `interface Quote { symbol: string; price: number }`. -/
def quoteFields : List (String × Bool × Ty) := [("symbol", false, .string), ("price", false, .nat)]
/-- The quote fetch answering the decoded record (route A: the host decodes). -/
def getQuoteRecord : RowDef := Row.host "Http.getQuote" .string (.record quoteFields) (.prod .string .string)

/-- One quote stored in the key-value cache, as `Cache` stores the lookup's answer. -/
def cacheQuoteModule : Module NativeOp := Package.install [kv]
  { rows := [getQuoteRecord]
    main := eff do
      let store ← Row.call (kv.op "Kv.make") unit
      let quote ← Row.call getQuoteRecord (str "EFX")
      Row.call (kv.op "set") (app "pair" [store, app "pair" [str "EFX", quote]]) }

/-- `first.price + again.price` over two record answers, with no cache. -/
def sumPricesModule : Module NativeOp :=
  { rows := [getQuoteRecord]
    main := eff do
      let first ← Row.call getQuoteRecord (str "EFX")
      let again ← Row.call getQuoteRecord (str "EFX")
      succeed (app "add" [field first "price", field again "price"]) }

-- A typed failure carries no number (row 120, ratified, not landed).
#guard verdict httpErrorModule = "typing: errorNotAdmitted"
#guard verdict (program (fail (app "pair" [str "HttpError", nat 404]))) = "typing: errorNotAdmitted"
-- The key-value store's value column is `string` (DB-15), so the cache cannot hold a `Quote`.
#guard verdict cacheQuoteModule = "typing: requestNotSubtype"
-- Since the data wave, a host row may answer the `Quote` record, and its prices add.
#guard verdict { rows := [getQuoteRecord], main := Row.call getQuoteRecord (str "EFX") } = "built"
#guard verdict sumPricesModule = "built"

-- The form table admits none of the forms p1 uses: `retry` (DI-89), `catchTag` (DI-39, DI-89)
-- and `timeout` (post-Phase C's W6).
#guard ["Effect.retry", "Effect.catchTag", "Effect.timeout"].filter formAdmits = []

/-! ## 7. The stage -/

def measured : Reach :=
  { refused :=
      [ ("HttpError{status, url} as a typed failure", verdict httpErrorModule)
      , ("a Quote record in the key-value cache", verdict cacheQuoteModule) ]
    admitted := verdict program1 == "built"
    answer := match runLive program1 ok503thenBody with
      | some r => answerOf r.root (.success (.nat 42))
      | none => .notRun
    printed := ((built? program1).map fun b => (printedOf b).1) == some true
    readBack := ((built? program1).map fun b => (printedOf b).2) == some true }

/-- The stage p1 reaches today, as `Test/Dogfood/README.md` quotes it: admitted and run under the
scripted host, with the body text where rc.112 answers 42; printed, and not read back. -/
def stage : Reach :=
  { refused :=
      [ ("HttpError{status, url} as a typed failure", "typing: errorNotAdmitted")
      , ("a Quote record in the key-value cache", "typing: requestNotSubtype") ]
    admitted := true, answer := .differs, printed := true, readBack := false }

#guard measured = stage

end Test.Dogfood.P1HttpCache
