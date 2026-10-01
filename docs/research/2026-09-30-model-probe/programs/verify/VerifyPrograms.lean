import Effect4.Api.Author
import Effect4.Api.HostSession
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.DenoteB
import Effect4.Codegen.Forms

/-! Verifier for seat PROGRAMS (2026-09-30). Checks the seat did not run, over the seat's own
program definitions, copied verbatim from `../ProbeProgram1.lean` and `../ProbePrograms345.lean`
(hashes in `../verify.md`). Every check has a red control beside it. Scratch, not in the tree.

1. R8's face on full programs: does the printer's image of each expressible program read back
   exactly (`Api.readable`, K2 on the readable domain)? The seat did not print any program.
2. PROG-2: a red control for the seat's data-capture guard (the layer built under the
   re-provided value answers 2, so the guard's 1 discriminates build time from call time).
3. PROG-8: a red control for the spurious `nat` error column (the same pool without the
   deferred gate types at error `never`).
4. PROG-9: the seat's "the expressible version answers 0" was reading; here it runs.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Verify.Programs
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## The seat's definitions, verbatim -/

def timeoutForm (body : Src NativeOp) (millis : TermSrc) (timedOut : TermSrc) : Src NativeOp :=
  eff do
    let entrant ← fork body
    let timer ← fork (andThen (Effect.sleep millis) (fail timedOut))
    let winner ← withFiber (Action.raceAll
      [andThen (await entrant) (succeed (nat 0)), andThen (await timer) (succeed (nat 1))])
    ifElse (app "eq" [winner, nat 0])
      (andThen (withFiber (Action.interrupt timer)) (join entrant))
      (andThen (withFiber (Action.interrupt entrant)) (join timer))

def retryForm (attempt : Src NativeOp) (retryable : TermSrc → TermSrc) (times base : Nat)
    (answerTy errorTy : Ty) : Src NativeOp :=
  let cursorTy : Ty := .prod .nat (.prod .nat (.prod (.option answerTy) (.option errorTy)))
  bindName "retry.last"
    (iterateWith (app "pair" [nat 0, app "pair" [nat base, app "pair" [app "none" [], app "none" []]]])
      { cursorTy := some cursorTy
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

def getQuote : RowDef := Row.host "Http.getQuote" .string .string (.prod .string .string)

def kv : Package := Package.ofRows "kv" Packages.keyValueStoreMemory

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

def refill (used : TermSrc) : Src NativeOp :=
  iterateWith (bool true)
    { while_ := fun _ => bool true
      body := fun _ => andThen (Effect.sleep (nat 1000)) (Ref.set used (nat 0))
      step := fun c _ => c }

def request (yielding : Bool) (used admitted rejected : TermSrc) : Src NativeOp :=
  bindName "current" (Ref.get used) fun current =>
    andThen (if yielding then yieldNow 0 else succeed unit)
      (ifElse (app "lt" [current, nat 3])
        (andThen (Ref.update .incr used) (Ref.update .incr admitted))
        (Ref.update .incr rejected))

def limiter (yielding : Bool) : Src NativeOp := eff do
  let used ← Ref.make (nat 0)
  let admitted ← Ref.make (nat 0)
  let rejected ← Ref.make (nat 0)
  let daemonFiber ← daemon (refill used)
  let f1 ← fork (request yielding used admitted rejected)
  let f2 ← fork (request yielding used admitted rejected)
  let f3 ← fork (request yielding used admitted rejected)
  let f4 ← fork (request yielding used admitted rejected)
  let f5 ← fork (request yielding used admitted rejected)
  let _ ← join f1
  let _ ← join f2
  let _ ← join f3
  let _ ← join f4
  let _ ← join f5
  let _ ← withFiber (Action.interrupt daemonFiber)
  let a ← Ref.get admitted
  let r ← Ref.get rejected
  return app "pair" [a, r]

def limiterProgram (yielding : Bool) : Option Effect4.Api.Program :=
  (elaborate (limiter yielding)).toOption

def N : ServiceDef := { key := ⟨⟨15⟩, ⟨4⟩⟩, carrier := .nat }
def Svc : ServiceDef := { key := ⟨⟨16⟩, ⟨4⟩⟩, carrier := .nat }

def captureControl : Module NativeOp :=
  { services := [N, Svc]
    layers := [("svc", Svc.layer N.use)]
    main := N.give (nat 1) (provide (Layer.ref "svc") (eff do
      let captured ← N.give (nat 2) Svc.use
      let atCall ← N.give (nat 2) N.use
      return app "pair" [captured, atCall])) }

def take : RowDef := Row.host "Jobs.take" .unit .nat
def runJob : RowDef := Row.host "Jobs.run" .nat .unit (.prod .string .string)

def worker (closes count gate : TermSrc) (total : Nat) : Src NativeOp :=
  scope (eff do
    let _conn ← acquireRelease "conn" "exit" (succeed unit) (Ref.update .incr closes)
    iterateWith (bool true)
      { while_ := fun _ => bool true
        body := fun _ => eff do
          let job ← Row.call take unit
          let _ ← catchIf "e" (app "tagIs" [str "JobFailed", var "e"])
            (Row.call runJob job) (succeed unit)
          let n ← Ref.updateAndGet .incr count
          ifElse (app "eq" [n, nat total])
            (Deferred.succeed gate (nat 0)) (succeed (bool false))
        step := fun c _ => c })

def pool (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let closes ← Ref.make (nat 0)
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped (worker closes count gate total) childOptions)
        let _w2 ← withFiber (Action.forkScoped (worker closes count gate total) childOptions)
        let _w3 ← withFiber (Action.forkScoped (worker closes count gate total) childOptions)
        Deferred.await gate)
      let c ← Ref.get closes
      let n ← Ref.get count
      return app "pair" [c, n] }

/-! ## 1. R8's face: does each program read back from its own printing? -/

def built1 : Option Effect4.Api.Built := (Effect4.Api.Author.build program1).toOption
def builtPool : Option Effect4.Api.Built := (Effect4.Api.Author.build (pool 5)).toOption
def builtCapture : Option Effect4.Api.Built := (Effect4.Api.Author.build captureControl).toOption

/-- The forms alone, at their call site in program 1, as closed programs: the retry form over
a constant attempt, and the timeout form over a constant body. -/
def retryAlone : Option Effect4.Api.Program :=
  (elaborate (retryForm (succeed (str "ok")) (fun _ => bool true) 3 100 .string .string)).toOption
def timeoutAlone : Option Effect4.Api.Program :=
  (elaborate (timeoutForm (succeed (str "ok")) (nat 2000) (str "late"))).toOption

-- Green control: the limiter (no form, no host row) is in the printer's readable image.
#guard (limiterProgram false).map (Effect4.Api.readable ·) = some true
-- The capture control (a layer reference, no form) reads back.
#guard builtCapture.map (fun b => Effect4.Api.readable b.program b.table) = some true
-- The timeout form alone reads back exactly.
#guard timeoutAlone.map (Effect4.Api.readable ·) = some true
-- Red: the retry form alone does not. Its loop carries a cursor annotation (`cursorTy := some _`;
-- the option columns are typed by no initial value), and by DI-91's ruling an annotated loop
-- prints `ofTy t` and is not read: the reader refuses it at `annotation "local const"`
-- (`Codegen/Read.lean:433-434`, "no reader of types exists, by design (B19)").
#guard retryAlone.map (Effect4.Api.readable ·) = some false
#guard retryAlone.map (fun p => match Effect4.Api.roundTrip p with
    | .error (.annotation site) => site == "local const"
    | _ => false) = some true
-- The form types before printing, so the refusal is the face's, not the checker's.
#guard (retryAlone.bind (Effect4.Api.typeOf ·)).isSome
-- So program 1, which uses it, is outside the readable image.
#guard built1.map (fun b => Effect4.Api.readable b.program b.table) = some false
-- Printing program 1 and reading it back is refused at the same annotation.
#guard built1.map (fun b => match Effect4.Api.roundTrip b.program b.table with
    | .error (.annotation site) => site == "local const"
    | _ => false) = some true
-- The pool as the seat spelled it does not read back: its workers are forked with
-- `childOptions` (daemon false, start immediately), and the printer drops a scoped fork's
-- daemon flag (`Api.lean:160-162`). Located in `ScratchPoolRead.lean`.
#guard builtPool.map (fun b => Effect4.Api.readable b.program b.table) = some false

/-- The same pool with rc.112's `Effect.forkScoped` default options, as the form table spells
them (`Codegen/Forms.lean`, `forkScopedDefault`: daemon, not started immediately). -/
def poolDefault (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let closes ← Ref.make (nat 0)
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped (worker closes count gate total) (Effect4.Codegen.Forms.defaults true))
        let _w2 ← withFiber (Action.forkScoped (worker closes count gate total) (Effect4.Codegen.Forms.defaults true))
        let _w3 ← withFiber (Action.forkScoped (worker closes count gate total) (Effect4.Codegen.Forms.defaults true))
        Deferred.await gate)
      let c ← Ref.get closes
      let n ← Ref.get count
      return app "pair" [c, n] }

-- With rc.112's default options the pool reads back exactly.
#guard ((Effect4.Api.Author.build (poolDefault 5)).toOption.map fun b =>
    Effect4.Api.readable b.program b.table) = some true

/-! ## 1b. PROG-6: what `run_eq_ref` sees of program 1

`run_eq_ref` is stated for `Api.replay` at the default (empty) table and no answers. Program 1
there does not finish: its root is still live and the run ends at a frontier. Red control: the
row-free limiter finishes under the same entry point. -/

#guard built1.map (fun b => ((Effect4.Api.run b.program 4000).outcome,
    (Effect4.Api.run b.program 4000).exit)) = some (.frontier, none)
#guard (limiterProgram false).map (fun p => (Effect4.Api.run p 4000).outcome) = some .finished

/-! ## 2. PROG-2: the data-capture guard discriminates -/

/-- Red control: the same layer built where `N` is already re-provided reads 2, so the seat's
answer 1 is the build-time value, not an accident of the spelling. -/
def captureBuiltLate : Module NativeOp :=
  { services := [N, Svc]
    layers := [("svc", Svc.layer N.use)]
    main := N.give (nat 1) (N.give (nat 2) (provide (Layer.ref "svc") (eff do
      let captured ← Svc.use
      let atCall ← N.use
      return app "pair" [captured, atCall]))) }

#guard ((Effect4.Api.Author.build captureControl).toOption.map fun b =>
    (Effect4.Api.run b.program 4000).exit) = some (some (.success (.list [.nat 1, .nat 2])))
#guard ((Effect4.Api.Author.build captureBuiltLate).toOption.map fun b =>
    (Effect4.Api.run b.program 4000).exit) = some (some (.success (.list [.nat 2, .nat 2])))

/-! ## 3. PROG-8: the `nat` error column comes from the gate -/

/-- Red control: the pool's main without the deferred gate. -/
def poolNoGate (total : Nat) : Module NativeOp :=
  { rows := [take, runJob]
    main := eff do
      let closes ← Ref.make (nat 0)
      let count ← Ref.make (nat 0)
      let gate ← Deferred.make
      let _ ← scope (eff do
        let _w1 ← withFiber (Action.forkScoped (worker closes count gate total) childOptions)
        succeed unit)
      let c ← Ref.get closes
      return c }

#guard builtPool.map (fun b => b.ty.error) = some .nat
#guard ((Effect4.Api.Author.build (poolNoGate 5)).toOption.map fun b => b.ty.error) = some .never

/-! ## 4. PROG-9: subtraction truncates, run -/

def balance : Option Effect4.Api.Program := (elaborate (succeed (app "sub" [nat 10, nat 25]))).toOption

#guard balance.bind (fun p => (Effect4.Api.run p 100).exit) = some (.success (.nat 0))
-- red control: the same atom where the answer is representable
#guard ((elaborate (succeed (app "sub" [nat 25, nat 10]))).toOption.bind
    (fun p => (Effect4.Api.run p 100).exit)) = some (.success (.nat 15))

end Verify.Programs
