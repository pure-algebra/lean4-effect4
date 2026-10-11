import Effects.Coalgebra

/-!
# The coalgebra contract battery

Packet: `test/contracts/coalgebra.contract.md`. Each line is a reader (a law applied at a real
carrier), a control (a red case showing why a premise stands or where a law stops), or a finite
evaluation that no theorem covers. The carriers are small: a signature with an `ask` that answers
a number and a `tell` that answers nothing, a counter host, and a program that asks twice and
tells the sum.
-/

namespace EffectsTest.Coalgebra

open Effects

/-- The operations of the battery's signature. -/
inductive Op where
  | ask
  | tell (n : Nat)

/-- `ask` answers a number; `tell` answers nothing. -/
def Ask : Signature.{0, 0} where
  Op := Op
  Answer
    | .ask => Nat
    | .tell _ => Unit

/-- Ask twice, tell the sum, end with it. -/
def askTwice : Program Ask Nat :=
  .vis Op.ask fun (a : Nat) => .vis Op.ask fun (b : Nat) => .vis (Op.tell (a + b)) fun _ => .pure (a + b)

/-- A counter host: `ask` answers the counter and increments it. -/
def counter : Comodel Ask Nat where
  answer
    | .ask, n => some (n, n + 1)
    | .tell _, n => some ((), n)

/-! ## Running against a host -/

-- finite evaluation: 5 then 6, so the sum is 11 and the counter ends at 7
#guard counter.run askTwice 5 == some (11, 7)

/-! ## The reply tape and recording -/

/-- A reply is a number; `tell` takes any reply. -/
def decode : (operation : Ask.Op) → Nat → Option (Ask.Answer operation)
  | .ask, n => some n
  | .tell _, _ => some ()

/-- A recorded reply: the number asked, or zero for a `tell`. -/
def encode : (operation : Ask.Op) → Ask.Answer operation → Nat
  | .ask, n => n
  | .tell _, _ => 0

theorem round : ∀ operation answer, decode operation (encode operation answer) = some answer
  | .ask, _ => rfl
  | .tell _, () => rfl

-- finite evaluation: the recording host writes 5, 6 and 0 beside the counter
#guard (counter.record encode).run askTwice (5, []) == some (11, (7, [5, 6, 0]))

-- finite evaluation: the reply host replays the recording, with nothing left
#guard (Comodel.replies decode).run askTwice [5, 6, 0] == some (11, [])

-- reader: what the recording host wrote, the reply host replays
example : ∃ recorded, [5, 6, 0] = ([] : List Nat) ++ recorded ∧
    ∀ rest, (Comodel.replies decode).run askTwice (recorded ++ rest) = some (11, rest) :=
  Comodel.run_record_replies decode encode round counter askTwice 5 []
    (by decide : (counter.record encode).run askTwice (5, []) = some (11, (7, [5, 6, 0])))

/-- A lossy encoding: every reply is written as zero. -/
def lossy : (operation : Ask.Op) → Ask.Answer operation → Nat := fun _ _ => 0

-- control: without the round trip, the replay is not the run (`round` stands)
#guard (counter.record lossy).run askTwice (5, []) == some (11, (7, [0, 0, 0]))
#guard (Comodel.replies decode).run askTwice [0, 0, 0] == some (0, [])

/-! ## Program in, program out -/

/-- A smaller signature: `read` answers a number. -/
def Read : Signature.{0, 0} where
  Op := Unit
  Answer _ := Nat

/-- `Ask` implemented by programs over `Read`: `ask` reads, `tell` does nothing. -/
def viaRead : Handler Ask (Program Read) where
  handle
    | .ask => .vis () .pure
    | .tell _ => .pure ()

/-- A host for `Read`: a counter. -/
def reader : Comodel Read Nat where
  answer _ n := some (n, n + 1)

-- reader: running through the implementation is running the translated program
example : (reader.through viaRead).run askTwice 5 = reader.run (interpret viaRead askTwice) 5 :=
  Comodel.run_through viaRead reader askTwice 5

#guard (reader.through viaRead).run askTwice 5 == some (11, 7)

/-! ## Routing and sharing -/

-- reader: a routed host runs a left program on the left state, the right state untouched
example : (counter.route reader).run (Program.inl (T := Read) askTwice) (5, 100) =
    (counter.run askTwice 5).map fun result => (result.1, (result.2, 100)) :=
  Comodel.run_route_inl counter reader askTwice 5 100

#guard (counter.route reader).run (Program.inl (T := Read) askTwice) (5, 100) == some (11, (7, 100))

/-! ## Admission -/

/-- Admit only even answers to `ask`. -/
def even : (operation : Ask.Op) → Ask.Answer operation → Bool
  | .ask, (n : Nat) => n % 2 == 0
  | .tell _, _ => true

-- control: the guarded counter refuses its first answer, 5, so the run stops with no answer
#guard (counter.guard even).run askTwice 5 == none
-- finite evaluation: from 4, the second answer is 5, refused
#guard (counter.guard even).run askTwice 4 == none

/-- A host that always answers an even number. -/
def evens : Comodel Ask Nat where
  answer
    | .ask, n => some (2 * n, n + 1)
    | .tell _, n => some ((), n)

theorem evens_meets : evens.Meets (fun operation answer => even operation answer = true) := by
  intro operation state answer state' h
  cases operation with
  | ask =>
    simp only [evens, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    show (2 * state % 2 == 0) = true
    rw [Nat.mul_mod_right]
    rfl
  | tell n => rfl

-- reader: guarding a host that meets the test changes nothing
example : evens.guard even = evens := Comodel.guard_of_meets evens_meets

/-! ## Systems, unfoldings and cuts -/

-- finite evaluation: depth one is a cut after the first answer, a live `none`, not an error
#guard Program.system.run counter 1 askTwice 5 == some (none, 6)
-- finite evaluation: depth four finishes
#guard Program.system.run counter 4 askTwice 5 == some (some 11, 7)

-- reader: a run that finished at one depth finishes the same way deeper
example (h : Program.system.run counter 4 askTwice 5 = some (some 11, 7)) :
    Program.system.run counter 9 askTwice 5 = some (some 11, 7) :=
  System.run_mono _ counter (by decide) h

-- reader: a program's own system finishes as the program does
example (h : Program.system.run counter 4 askTwice 5 = some (some 11, 7)) :
    counter.run askTwice 5 = some (11, 7) :=
  Program.run_system counter h

/-- A machine for `askTwice`: state `(2, _)` asks first, `(1, a)` asks second, `(0, s)` tells,
and any other state ends with its sum. -/
def machine : System Ask Nat (Nat × Nat)
  | (2, _) => some (.call Op.ask fun (a : Nat) => (1, a))
  | (1, a) => some (.call Op.ask fun (b : Nat) => (0, a + b))
  | (0, s) => some (.call (Op.tell s) fun _ => (3, s))
  | (_, s) => some (.done s)

/-- The relation: each machine state relates to the residual program it stands for. -/
inductive Related : Nat × Nat → Program Ask Nat → Prop
  | start (s : Nat) : Related (2, s) askTwice
  | second (a : Nat) :
      Related (1, a) (.vis Op.ask fun (b : Nat) => .vis (Op.tell (a + b)) fun _ => .pure (a + b))
  | tell (s : Nat) : Related (0, s) (.vis (Op.tell s) fun _ => .pure s)
  | done (s : Nat) : Related (3, s) (.pure s)

theorem machine_sim : IsSim machine Program.system Related := by
  intro x program hrel step hstep
  cases hrel with
  | start s =>
    simp only [machine, Option.some.injEq] at hstep
    subst hstep
    refine ⟨_, rfl, ?_⟩
    exact Step.Lift.call (S := Ask) Op.ask fun a => Related.second a
  | second a =>
    simp only [machine, Option.some.injEq] at hstep
    subst hstep
    refine ⟨_, rfl, ?_⟩
    exact Step.Lift.call (S := Ask) Op.ask fun (b : Nat) => Related.tell (a + b)
  | tell s =>
    simp only [machine, Option.some.injEq] at hstep
    subst hstep
    refine ⟨_, rfl, ?_⟩
    exact Step.Lift.call (S := Ask) (Op.tell s) fun _ => Related.done s
  | done s =>
    simp only [machine, Option.some.injEq] at hstep
    subst hstep
    exact ⟨_, rfl, .done s⟩

-- finite evaluation: the machine finishes against the counter at depth four
#guard machine.run counter 4 (2, 0) 5 == some (some 11, 7)

-- reader: one simulation, every host. Where the machine finishes, the program does
example (h : machine.run counter 4 (2, 0) 5 = some (some 11, 7)) :
    counter.run askTwice 5 = some (11, 7) :=
  Program.run_of_sim_program machine_sim (Related.start 0) counter h

example (h : machine.run (Comodel.replies decode) 4 (2, 0) [1, 2, 9] = some (some 3, [])) :
    (Comodel.replies decode).run askTwice [1, 2, 9] = some (3, []) :=
  Program.run_of_sim_program machine_sim (Related.start 0) _ h

/-- A wrong machine: it ends one step early, with its sum before telling it. -/
def early : System Ask Nat (Nat × Nat)
  | (0, sum) => some (.done sum)
  | (k + 1, sum) => some (.call Op.ask fun (a : Nat) => (k, sum + a))

-- control: the early machine finishes where the program has not, so no simulation relates them
#guard early.run counter 3 (2, 0) 5 == some (some 11, 7)
#guard Program.system.run counter 3 askTwice 5 == some (none, 7)

/-! ## Hiding an inner signature -/

/-- An inner signature with one operation that answers a number. -/
def Tick : Signature.{0, 0} where
  Op := Unit
  Answer _ := Nat

/-- The inner function: answer the state and increment it. -/
def tick : (operation : Tick.Op) → Nat → Tick.Answer operation × Nat := fun _ n => (n, n + 1)

/-- Tick, then ask, then end with the sum. -/
def tickAsk : Program (Tick ⊕ₛ Ask) Nat :=
  .vis (.inl ()) fun (t : Nat) => .vis (.inr Op.ask) fun (a : Nat) => .pure (t + a)

-- finite evaluation: the hiding system runs against the counter alone; the tick is hidden
#guard (System.peel tick).run counter 3 (tickAsk, 10) 5 == some (some (15, 11), 6)

-- reader: the hiding system's run is the routed run of the program
example (h : (System.peel tick).run counter 3 (tickAsk, 10) 5 = some (some (15, 11), 6)) :
    ((Comodel.ofTotal tick).route counter).run tickAsk (10, 5) = some (15, (11, 6)) :=
  System.run_peel tick counter 3 tickAsk 10 5 h

/-! ## Typed programs and typed handlers -/

/-- The upper protocol: `ask` answers an even number; `tell` answers anything. -/
def evenAsk : Protocol Ask
  | .ask => fun (n : Nat) => n % 2 = 0
  | .tell _ => fun _ => True

/-- `Ask` implemented over `Read` with doubled answers. -/
def doubled : Handler Ask (Program Read) where
  handle
    | .ask => .vis () fun (n : Nat) => .pure (2 * n)
    | .tell _ => .pure ()

/-- The doubling implementation is typed from `evenAsk` down to `Read` under any answer. -/
theorem doubled_typed : doubled.Typed evenAsk Protocol.top
  | .ask => fun n _ => Nat.mul_mod_right 2 n
  | .tell _ => trivial

/-- Asking twice under `evenAsk` ends even. -/
theorem askTwice_even : Program.Sat evenAsk (fun (n : Nat) => n % 2 = 0) askTwice :=
  fun (a : Nat) ha (b : Nat) hb _ _ => by
    show (a + b) % 2 = 0
    rw [Nat.add_mod, show a % 2 = 0 from ha, show b % 2 = 0 from hb]

-- reader: the counter behind the typed implementation meets the upper protocol
example : (reader.through doubled).Meets evenAsk :=
  Comodel.Meets.through doubled_typed fun _ _ _ _ _ => trivial

-- reader: the translated program is typed under the lower protocol, into the same postcondition
example : Program.Sat Protocol.top (fun (n : Nat) => n % 2 = 0) (interpret doubled askTwice) :=
  doubled_typed.interpret askTwice askTwice_even

-- reader: soundness at the counter, so the run's value is even
example (n : Nat) (h : reader.run (interpret doubled askTwice) 5 = some (n, 7)) : n % 2 = 0 :=
  Program.Sat.sound reader (fun _ _ _ _ _ => trivial) _ (doubled_typed.interpret askTwice
    askTwice_even) 5 n 7 h

#guard (reader.through doubled).run askTwice 5 == some (22, 7)

/-- `Read` implemented over `Ask`: a read asks. -/
def viaAsk : Handler Read (Program Ask) where
  handle _ := .vis Op.ask .pure

-- reader: typed layers compose; doubling over reading over asking is typed from `evenAsk` to `Ask`
example : (doubled.through viaAsk).Typed evenAsk Protocol.top :=
  Handler.Typed.through doubled_typed fun _ _ _ => trivial

-- control: the undoubled implementation is not typed, since its `ask` may answer an odd number
example : ¬ viaRead.Typed evenAsk Protocol.top :=
  fun h => absurd (show (5 : Nat) % 2 = 0 from h Op.ask (5 : Nat) trivial) (by decide)

-- control: behind it, the counter answers 5 at an `ask`, which `evenAsk` refuses
#guard ((reader.through viaRead).answer Op.ask 5).map (fun result => ((result.1 : Nat), result.2))
  == some (5, 6)

/-! ## A protocol of a higher order: promises

A world lists the codes of the open promises. Starting a job opens a promise, and awaiting it
answers a value of the code it recorded: the answer type of an operation depends on an earlier
answer. -/

/-- A code for a job's result: a number or a truth value. -/
inductive Code where
  | num
  | flag
  deriving DecidableEq

/-- The values a code admits. -/
abbrev Code.carrier : Code → Type
  | .num => Nat
  | .flag => Bool

/-- The operations of a world: start a job of a code, or await an open promise. -/
inductive AsyncOp (opened : List Code) where
  | async (code : Code)
  | await (promise : Fin opened.length)

/-- Promises as an indexed signature. -/
def Async : ISignature (List Code) where
  Op opened := AsyncOp opened
  Answer opened operation := match operation with
    | .async _ => Unit
    | .await promise => (opened.get promise).carrier
  next opened operation _ := match operation with
    | .async code => opened ++ [code]
    | .await _ => opened

/-- A job's result, from its position among the jobs started. -/
def job : (code : Code) → Nat → code.carrier
  | .num, n => 10 * (n + 1)
  | .flag, n => n % 2 == 1

/-- A host that records the codes of the jobs started and answers an await with its job's result. -/
def jobs : IComodel Async (List Code) where
  answer opened operation started := match operation with
    | .async code => some ((), started ++ [code])
    | .await promise =>
      if started[promise.val]? = some (opened.get promise) then
        some (job (opened.get promise) promise.val, started)
      else none

/-- Start a number job and a flag job, await both, and end with the number where the flag holds.
Each await's answer type is its promise's code. -/
def twoJobs : IProgram Async (fun _ => Nat) [] :=
  .vis (.async .num) fun _ =>
  .vis (.async .flag) fun _ =>
  .vis (.await ⟨0, Nat.zero_lt_succ _⟩) fun (n : Nat) =>
  .vis (.await ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩) fun (b : Bool) =>
  .pure (if b then n else 0)

-- finite evaluation: the number job gives 10, the flag job `true`, so the program ends with 10
#guard (jobs.run twoJobs []).map (fun result => (result.1, result.2.1, result.2.2)) ==
  some ([.num, .flag], 10, [.num, .flag])

/-- The protocol: a number that a promise answers is a multiple of ten. -/
def Code.tens : (code : Code) → code.carrier → Prop
  | .num, n => n % 10 = 0
  | .flag, _ => True

def tens : IProtocol Async := fun opened operation => match operation with
  | .async _ => fun _ => True
  | .await promise => Code.tens (opened.get promise)

theorem job_tens : (code : Code) → (n : Nat) → Code.tens code (job code n)
  | .num, n => Nat.mul_mod_right 10 (n + 1)
  | .flag, _ => trivial

theorem jobs_meets : jobs.Meets tens := by
  intro opened operation started answer started' h
  cases operation with
  | async code => exact trivial
  | await promise =>
    have h' : (if started[promise.val]? = some (opened.get promise) then
        some (job (opened.get promise) promise.val, started) else none) = some (answer, started') := h
    split at h'
    · cases h'
      exact job_tens (opened.get promise) promise.val
    · cases h'

theorem twoJobs_tens : twoJobs.Sat tens (fun _ (n : Nat) => n % 10 = 0) :=
  fun _ _ _ _ (n : Nat) (hn : n % 10 = 0) (b : Bool) _ => by
    cases b
    · exact rfl
    · exact hn

-- reader: soundness at the host, so the run ends with a multiple of ten
example (opened : List Code) (n : Nat) (state : List Code)
    (h : jobs.run twoJobs [] = some ⟨opened, n, state⟩) : n % 10 = 0 :=
  IProgram.Sat.sound jobs jobs_meets twoJobs twoJobs_tens [] opened n state h

/-- A wrong result: seven for a number. -/
def seven : (code : Code) → code.carrier
  | .num => 7
  | .flag => true

/-- A host whose number jobs answer seven. -/
def sevens : IComodel Async (List Code) where
  answer opened operation started := match operation with
    | .async code => some ((), started ++ [code])
    | .await promise => some (seven (opened.get promise), started)

-- control: a host outside the protocol runs the typed program to 7, outside its postcondition
#guard (sevens.run twoJobs []).map (fun result => result.2.1) == some 7

-- reader: the one-world case. A first-order host runs an embedded program as it runs the program
example : counter.toIndexed.run (IProgram.ofProgram askTwice) 5 =
    (counter.run askTwice 5).map fun result => ⟨(), result.1, result.2⟩ :=
  IComodel.run_ofProgram counter askTwice 5

-- reader: the embedding is exact
example : IProgram.toProgram (IProgram.ofProgram askTwice) = askTwice :=
  IProgram.toProgram_ofProgram askTwice

end EffectsTest.Coalgebra
