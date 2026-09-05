import Effect4.Api
import Effect4.Program.Wire

/-!
# Bridge — the Lean machine as a C-callable session (route 1 spike)

An OCaml process holds a `Session` (a program and its `RunMachine`) as an opaque Lean
object and steps it one host decision, or one bounded drive, at a time. Every intermediate
machine is a genuine machine value; the snapshot is read off the value, nothing is
instrumented. Strings in, strings out at the boundary; the machine never crosses it.

Exports (Lean's C ABI: `lean_object*` arguments are owned unless marked `@&`):

    e4_program_names : Unit → String                       -- newline-separated
    e4_load          : String → UInt32 → Session           -- program name, fuel
    e4_step          : Session → String → UInt32 → Session -- "evaluate" | "flush" | "fire:<id>"
    e4_drive         : Session → UInt32 → Session          -- drive [evaluate root, drainDue] with that fuel
    e4_snapshot      : Session → String
-/

namespace OCaml5.Bridge

open Effect4 Effect4.Api Effect4.Machine Effect4.Program

/-- One program and the machine it is running in. -/
structure Session where
  name : String
  program : Api.Program
  machine : Api.Machine

def forkOptions : Supervision.ForkOptions :=
  { startImmediately := false, daemon := false, maskMode := .inherit }

/-- `Effect.succeed(42)`. -/
def p42 : Api.Program := .succeed (.lit (.nat 42))

/-- `Effect.flatMap(Effect.succeed(1), a0 => Effect.succeed(succ(a0)))`. -/
def pBind : Api.Program :=
  .bind (.succeed (.lit (.nat 1))) (.succeed (.app "succ" (.cons (.var 0) .nil)))

/-- Fork a child that yields then succeeds with 7, and await it: the root parks, the child
runs from the dispatcher when the host fires it. -/
def pFork : Api.Program :=
  .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 7)))) forkOptions))
    (.awaitFiber (.var 0) .awaitValue)

/-- Two children, both awaited in order. -/
def pTwo : Api.Program :=
  .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 1)))) forkOptions))
    (.bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 2)))) forkOptions))
      (.bind (.awaitFiber (.var 1) .awaitValue) (.awaitFiber (.var 1) .awaitValue)))

/-- Park on a fresh Deferred: the root parks on a token and nothing inside the machine can
resume it. The resume is an external `answerAsync` decision — a message from another
machine, through the host. -/
def pAwait : Api.Program :=
  .bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0))

def programs : List (String × Api.Program) :=
  [("p42", p42), ("pBind", pBind), ("pFork", pFork), ("pTwo", pTwo), ("pAwait", pAwait)]

@[export e4_program_names]
def programNames (_ : Unit) : String :=
  "\n".intercalate (programs.map (·.1))

@[export e4_load]
def load' (name : String) (fuel : UInt32) : Session :=
  let program := (programs.lookup name).getD p42
  { name := name, program := program, machine := load program fuel.toNat }

/-! ## Programs as bytes: authored outside, decoded exactly, type-checked, then loaded -/

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def bytesOfHex : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | h :: l :: rest => do
    let hi ← hexDigit h
    let lo ← hexDigit l
    let tail ← bytesOfHex rest
    pure (UInt8.ofNat (hi * 16 + lo) :: tail)

def hexOfBytes (bs : List UInt8) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList (bs.foldr (fun b acc => digits[b.toNat / 16]! :: digits[b.toNat % 16]! :: acc) [])

/-- The session name: the program's table name, `bytes` for a decoded program, or
`!refused:<reason>` when `e4_load_hex` could not load (the machine is then `p42`'s). -/
@[export e4_name]
def name (s : Session) : String := s.name

/-- Load a program from its canonical bytes (hex): exact decode, then the typing check,
then load. A refusal is a session named `!refused:decode` or `!refused:ill-typed`. -/
@[export e4_load_hex]
def loadHex (hexText : String) (fuel : UInt32) : Session :=
  match bytesOfHex hexText.toList with
  | none => { name := "!refused:decode", program := p42, machine := load p42 fuel.toNat }
  | some bytes =>
    match Wire.decodeProgram bytes with
    | none => { name := "!refused:decode", program := p42, machine := load p42 fuel.toNat }
    | some program =>
      if wellTyped program then
        { name := "bytes", program := program, machine := load program fuel.toNat }
      else { name := "!refused:ill-typed", program := p42, machine := load p42 fuel.toNat }

/-- The canonical bytes (hex) of a table program, `""` for an unknown name. -/
@[export e4_program_hex]
def programHex (name : String) : String :=
  match programs.lookup name with
  | some p => hexOfBytes (Wire.encodeProgram p)
  | none => ""

def parseDecision (s : String) : Option Api.Decision :=
  if s == "evaluate" then some (RunDecision.evaluate root)
  else if s == "flush" then some RunDecision.flush
  else if s.startsWith "fire:" then
    (s.drop 5).toString.toNat?.map fun n => RunDecision.fire ⟨n⟩
  else if s.startsWith "evaluate:" then
    (s.drop 9).toString.toNat?.map fun n => RunDecision.evaluate ⟨n⟩
  else if s.startsWith "answer:" then
    -- answer:<fiber>:<token>:<nat> — an external resume with a success value
    match ((s.drop 7).toString.splitOn ":").map String.toNat? with
    | [some f, some t, some v] =>
      some (RunDecision.answerAsync ⟨f⟩ t (Prim.success (Val.nat v)))
    | _ => none
  else none

@[export e4_step]
def step' (s : Session) (decision : String) (fuel : UInt32) : Session :=
  match parseDecision decision with
  | some d => { s with machine := stepDecision (interpOf s.program) fuel.toNat s.machine d }
  | none => s

@[export e4_drive]
def drive' (s : Session) (fuel : UInt32) : Session :=
  { s with machine :=
      drive (interpOf s.program) fuel.toNat s.machine [Cmd.evaluate root, Cmd.drainDue] }

/-! ## The snapshot, read off the value -/

def eventTag : RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx → String
  | .forked p c d => s!"forked {p.value}->{c.value}{if d then " daemon" else ""}"
  | .started f => s!"started {f.value}"
  | .scheduledTask o p _ => s!"scheduledTask owner={o.value} prio={p}"
  | .ranTask o _ => s!"ranTask owner={o.value}"
  | .yieldInjected f n => s!"yieldInjected {f.value}@{n}"
  | .parkedOn f t => s!"parkedOn {f.value} token={t}"
  | .resumedWith f t _ => s!"resumedWith {f.value} token={t}"
  | .interruptRecorded _ t => s!"interruptRecorded {t.value}"
  | .interruptDeferred t => s!"interruptDeferred {t.value}"
  | .childrenInterrupted p cs => s!"childrenInterrupted {p.value} n={cs.length}"
  | .observerFired f _ => s!"observerFired {f.value}"
  | .frame f _ => s!"frame {f.value}"
  | .finalizerProgram f _ _ => s!"finalizerProgram {f.value}"
  | .scopeLinked _ sc k f => s!"scopeLinked scope={sc} key={k} fiber={f.value}"
  | .scopeClosedOnLink sc f => s!"scopeClosedOnLink scope={sc} fiber={f.value}"
  | .raceStarted r h n => s!"raceStarted {r} host={h.value} entrants={n}"
  | .raceLaunched r e => s!"raceLaunched {r} entrant={e.value}"
  | .raceSettled r _ => s!"raceSettled {r}"
  | .contextSet f _ => s!"contextSet {f.value}"
  | .callback k _ => s!"callback key={k}"
  | .exited f e => s!"exited {f.value} {exitTag e}"
where
  exitTag : ExitV → String
    | .success v => s!"success {valTag v}"
    | .failure _ => "failure"
  valTag : Val → String
    | .unit => "unit"
    | .nat n => s!"nat {n}"
    | .bool b => s!"bool {b}"
    | .fiber f => s!"fiber {f.value}"
    | .fibers fs => s!"fibers n={fs.length}"
    | _ => "value"

def fiberLine (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) : String :=
  let parked := match f.parked with
    | .notParked => "-"
    | .withGuard t => s!"token={t}"
  let exit := match f.exit with
    | none => "live"
    | some (.success v) => s!"exit=success({eventTag.valTag v})"
    | some (.failure _) => "exit=failure"
  let buckets := f.dispatcher.buckets.map fun b => s!"{b.priority}:{b.tasks.length}"
  s!"  fiber {f.id.value}: {exit} running={f.running} parked={parked} stack={f.frame.stack.length}"
    ++ s!" pending={f.pending.length} observers={f.observers.length} children={f.children.length}"
    ++ s!" ops={f.currentOpCount}/{f.maxOpsBeforeYield} dispatcher(armed={f.dispatcher.armed} {buckets})"

/-! ## Structured accessors — projections of the value, one fact each -/

/-- The fibers whose dispatcher is armed, in arming order, comma-separated. -/
@[export e4_armed]
def armed (s : Session) : String :=
  ",".intercalate (s.machine.armed.map fun f => toString f.value)

/-- 1 when every fiber has exited. -/
@[export e4_finished]
def finished (s : Session) : UInt8 :=
  if s.machine.finished then 1 else 0

/-- One line per fiber: `id<TAB>live|exited<TAB>token|-<TAB>success:<tag>|failure|-`. -/
@[export e4_fibers]
def fibers (s : Session) : String :=
  "\n".intercalate <| s.machine.fibers.map fun f =>
    let state := if f.exit.isSome then "exited" else "live"
    let token := match f.parked with
      | .notParked => "-"
      | .withGuard t => toString t
    let exit := match f.exit with
      | none => "-"
      | some (.success v) => s!"success:{eventTag.valTag v}"
      | some (.failure _) => "failure"
    s!"{f.id.value}\t{state}\t{token}\t{exit}"

@[export e4_trace_len]
def traceLen (s : Session) : UInt32 :=
  s.machine.trace.length.toUInt32

/-- The event rows from index `cursor`, newline-separated. -/
@[export e4_events]
def events (s : Session) (cursor : UInt32) : String :=
  "\n".intercalate ((s.machine.trace.drop cursor.toNat).map eventTag)

@[export e4_snapshot]
def snapshot (s : Session) : String :=
  let m := s.machine
  let head := s!"machine {s.name}: fibers={m.fibers.length} nextId={m.nextId} nextToken={m.nextToken}"
    ++ s!" armed={m.armed.map (·.value)} finished={m.finished} stuck={m.stuck.isSome} trace={m.trace.length}"
  let fibers := m.fibers.map fiberLine
  let store := s!"  store: refs={m.state.refs.length} deferreds={m.state.deferreds.cells.length}"
    ++ s!" due={m.state.deferreds.due.length} nextName={m.state.nextName}"
  let events := m.trace.map fun e => "  · " ++ eventTag e
  "\n".intercalate (head :: fibers ++ [store, "  trace:"] ++ events)

end OCaml5.Bridge
