import Effect4.Author

/-! Program data shared by the battery and scenario fixtures. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.P1HttpCache

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The forms, with the one obligation that comes for free

A form is a Lean function over the authoring lifts (DI-89's third route). DI-89 asks of a form a
typing lemma and one behaviour law; requirement R10 adds lexical well-scoping, reader admission,
a readable expansion and a stable identity. These two forms meet lexical well-scoping only. -/

/-- `Effect.timeout(body, millis)` follows rc.112's first-exit race
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3677-3727`).
The machine observes the attempt and timer directly, retains the complete first exit,
and waits for loser cleanup before returning it. -/
def timeoutForm (body : Src NativeOp) (millis : TermSrc) (timedOut : TermSrc) : Src NativeOp :=
  withFiber (Action.raceAllFirst [body, andThen (Effect.sleep millis) (fail timedOut)])

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
        -- the delay doubles after a sleep, and not before the first one: the first sleep is the
        -- base, as rc.112's `exponential` gives it (`base · factor^(attempt - 1)`,
        -- `vendor/effect-4.0.0-rc.112/src/Schedule.ts`)
        step := fun c last =>
          app "pair" [app "succ" [app "fst" [c]],
            app "pair" [app "ite" [app "lt" [nat 0, app "fst" [c]],
              app "mul" [app "fst" [app "snd" [c]], nat 2], app "fst" [app "snd" [c]]], last]]
        result := fun c => app "snd" [app "snd" [c]] })
    fun last =>
      selectOption "retry.ok" (app "fst" [last])
        (selectOption "retry.err" (app "snd" [last])
          (failCause (Cause.die (str "retry: no attempt ran")))
          (fail (var "retry.err")))
        (succeed (var "retry.ok"))

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

/-! ## 5. Which theorem reaches the program -/

-- In neither fragment, and with a non-empty row table: `run_eq_ref`, which holds at the empty row
-- table only, does not reach it either.

end Test.Dogfood.P1HttpCache
