import Effect4.Api.Author
import Effect4.Api.HostSession
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.DenoteB

/-! Seat PROGRAMS (2026-09-30), probe 2 of 3: the part of program 1 (`ts/p1-http-cache.ts`) that
the authoring surface expresses today, run through the live keyed session (the coordinator's
`FetchDemo.lean` is the template).

What is here: an HTTP host row with a typed error; `timeout` and `retry` written as Lean
functions over existing constructors (forms in DI-89's sense, without the typing lemma or the
behaviour law DI-89 asks of a form); a key-value cache answered by the host. What is not: the
JSON body as a record, a numeric status in the error, the `Cache` module's own semantics
(shared misses, cached failures, time to live). Scratch, not in the tree. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Probe.Program1
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession

/-! ## The forms -/

/-- `Effect.timeout(body, millis)` as rc.112 builds it (`internal/effect.ts:3677-3727`:
`raceFirst(self, sleep(d) *> fail(TimeoutError))`, first *exit* wins). The language's race is
first *success* (`raceAll`, `:1477-1533`), and nothing re-raises a captured exit, so the form
forks both entrants, races their `await`s (an await never fails, so the first to finish wins),
interrupts the loser (which waits for it) and joins the winner, which re-raises its failure. -/
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
(`internal/schedule.ts:51-80`): the attempt runs once, and again after each retryable typed
failure while retries remain, sleeping `base · 2^k` before retry `k + 1`. Defects and
interruptions are not caught (`catchIf` retains the whole cause on a miss, `Eff.lean:314-318`),
as rc.112 retries typed failures only. The cursor is (retries so far, next delay, last answer
or error). `answerTy` and `errorTy` state the cursor's type, which no initial value spells. -/
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

/-! ## The program -/

/-- `GET /quotes/:symbol`: the host answers the body as text, or fails with (tag, message). -/
def getQuote : RowDef := Row.host "Http.getQuote" .string .string (.prod .string .string)

def kv : Package := Package.ofRows "kv" Packages.keyValueStoreMemory

/-- Retry network failures, timeouts and exactly "503": rc.112's `status >= 500` needs a number
in the error, which the error column cannot hold (`ProbeRefusals.lean`). -/
def retryable (e : TermSrc) : TermSrc :=
  app "or" [app "tagIs" [str "NetworkError", e],
    app "or" [app "tagIs" [str "Timeout", e], app "eq" [app "snd" [e], str "503"]]]

def fetchQuote (symbol : TermSrc) : Src NativeOp :=
  retryForm
    (timeoutForm (Row.call getQuote symbol) (nat 2000)
      (app "pair" [str "Timeout", str "2000 ms"]))
    retryable 3 100 .string (.prod .string .string)

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

def built? : Option Effect4.Api.Built := (Effect4.Api.Author.build program1).toOption

-- It builds: typed against its own table and admitted.
#guard built?.isSome
#guard (built?.map fun b => (b.ty.answer, b.ty.error)) = some (.string, .prod .string .string)

/-! ## A scripted host, through the live keyed session -/

/-- The host's script for the HTTP row, by call ordinal: `none` never answers (the host is
still working when the program gives up). -/
abbrev Script := Nat → Option (Completion Val Err Defect FiberId Ann)

def ok503thenBody : Script
  | 0 => none
  | 1 => some (.ofExit (.failure (Cause.fail (.tagged "HttpError" "503"))))
  | _ => some (.ofExit (.success (.str "{\"symbol\":\"EFX\",\"price\":21}")))

/-- The red control's script: the second attempt answers 404, which is not retryable. -/
def ok404 : Script
  | 0 => none
  | 1 => some (.ofExit (.failure (Cause.fail (.tagged "HttpError" "404"))))
  | _ => some (.ofExit (.success (.str "unreachable")))

def hostAnswer (b : Effect4.Api.Built) (script : Script) (httpCall : Nat) (allocated : Nat)
    (op : NativeOp) : Option (Completion Val Err Defect FiberId Ann) :=
  match op with
  | .external i =>
    if some i = b.positionOf "Kv.make" then some (.ofExit (.success (.nat allocated)))
    else if some i = b.positionOf "get" then some (.ofExit (.success .none))
    else if some i = b.positionOf "set" then some (.ofExit (.success .unit))
    else if some i = b.positionOf "Http.getQuote" then script httpCall
    else some (.ofExit (.success .unit))
  | _ => none

structure Driver (b : Effect4.Api.Built) where
  session : Session b.program b.table
  httpCalls : Nat := 0
  /-- Calls the host received and has not answered: bound in the session, no reply. -/
  hanging : List Key := []
  clockSteps : Nat := 0

/-- One step. A fresh outstanding call is bound at once (the host has received it); it is then
answered if the script answers it, and otherwise left hanging. With nothing to answer, the
scheduler runs; when that changes nothing, the clock moves by 100 ms. -/
def step (b : Effect4.Api.Built) (script : Script) (d : Driver b) : Driver b :=
  let s := d.session
  let fresh := (outstanding s).filter fun (fiber, token, _, _) => !(d.hanging.contains ⟨fiber, token⟩)
  match fresh with
  | (fiber, token, op, request) :: _ =>
    let isHttp : Bool := (match op with | .external i => some i == b.positionOf "Http.getQuote" | _ => false)
    let ordinal := d.httpCalls
    let call : Call := ⟨version, "p1", b.table, s.nextCall, fiber, op, request⟩
    let s1 := (bindCall s call token).session
    match hostAnswer b script ordinal s1.machine.state.externals.allocated.length op with
    | none =>
      { d with session := s1, hanging := d.hanging ++ [⟨fiber, token⟩],
               httpCalls := if isHttp then ordinal + 1 else ordinal }
    | some answer =>
      let reply : Reply := ⟨version, "p1", call.callId, ⟨fiber, token⟩, answer⟩
      let s2 := (submit s1 reply).session
      let s3 := (applyReply s2 reply.key 1000).session
      { d with session := s3, httpCalls := if isHttp then ordinal + 1 else ordinal }
  | [] =>
    let flushed := (advance s 1000 Api.flush).session
    if flushed.machine.trace.length == s.machine.trace.length then
      { d with session := (advance flushed 1000 (.advance (ClockMillis.ofNat 100))).session,
               clockSteps := d.clockSteps + 1 }
    else { d with session := flushed }

def drive (b : Effect4.Api.Built) (script : Script) : Nat → Driver b → Driver b
  | 0, d => d
  | n + 1, d => drive b script n (step b script d)

/-- What a run shows: the root's exit, the HTTP calls the host received, the host answers
applied, and the associations the session retired (calls whose fiber stopped waiting). -/
structure Shown where
  root : Option ExitV
  httpCalls : Nat
  applied : Nat
  retired : Nat
  retiredPending : List Bool

def runLive (script : Script) : Option Shown :=
  built?.bind fun b =>
    match start b.program b.table "p1" ⟨version, "p1", "p1", b.table⟩ 1000 with
    | .error _ => none
    | .ok s0 =>
      let d := drive b script 400 { session := (advance s0 1000 Api.evaluate).session }
      some ⟨(d.session.machine.fiber? Api.root).bind (·.exit), d.httpCalls, d.session.applied,
        d.session.retired.length, d.session.retired.map (·.pending.isSome)⟩

-- Green: the first call hangs and the timeout gives up on it; the 503 is retried; the third
-- call answers. The root succeeds with the body, after three HTTP calls; the abandoned first
-- call is retired with no reply pending. The host is told nothing: retirement is a session
-- record (`Api/HostSession.lean:191-199`), where rc.112 aborts the call's `AbortSignal`
-- (`internal/effect.ts:1115`, `:1131-1141`; `ts/hostruns.log`, "abort 1").
#guard (runLive ok503thenBody).map (·.root) =
  some (some (.success (.str "{\"symbol\":\"EFX\",\"price\":21}")))
#guard (runLive ok503thenBody).map (fun r => (r.httpCalls, r.retired, r.retiredPending)) =
  some (3, 1, [false])

-- Red control: a 404 is not retryable, so the failure reaches the root after two HTTP calls,
-- as rc.112's 404 run does (one call there, because nothing timed out first).
#guard (runLive ok404).map (·.root) =
  some (some (.failure (Cause.fail (.tagged "HttpError" "404"))))
#guard (runLive ok404).map (fun r => (r.httpCalls, r.retired)) = some (2, 1)

-- Which theorem could reach it: neither fragment, and a non-empty table, so `run_eq_ref`
-- (empty table only) does not apply either. Typing (`effTy_sound`/`effTy_complete`) and the
-- session's refusal lemmas are what reach this program today.
open Effect4.Program.Denote in
#guard built?.map (fun b => (Straight b.program, Looped b.program, b.table.isEmpty)) =
  some (false, false, false)

end Probe.Program1
