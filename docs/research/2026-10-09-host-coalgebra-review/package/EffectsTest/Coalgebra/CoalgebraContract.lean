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

end EffectsTest.Coalgebra
