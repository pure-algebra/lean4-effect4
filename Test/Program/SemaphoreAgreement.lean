import Effect4.Modules.Semaphore.Steps
import Effect4.Laws.Modules.Semaphore.Profile
import Effect4.Laws.Modules.Semaphore.Typing

/-!
# Semaphore's steps against the abstract model: the comparison (decisions row 265)

A comparison evaluates one step term of `src/Effect4/Modules/Semaphore/Steps.lean` on the
encoding of a model state, and compares the whole result with the encoding of the model's
transition (`src/Effect4/Laws/Modules/Semaphore/Model.lean`): the reply and the stored value.

The battery holds:

- the named controls C1 to C6, on the states of the contract's traces;
- every state of a finite universe of the profile, 225 states, with 23 moves on each;
- four states outside the profile: the comparison agrees there too, so no step goal needs the
  profile as a premise;
- the red controls M1 to M3: one part of an expected result changed, and nothing else;
- the faults F1 to F3 of the card's section 9 that a step can show. Each is a changed step
  term, red at its own property, and the checker types each as it types the library's step.

Placement. Each comparison is a finite instance of a step goal of Semaphore's refinement
(concept `translation-simulation`, requirement R10, a part of the proposed claim
`semaphore-expansion-agrees`). Every guard is a finite check. A state outside the universe is
not checked. No guard states delivery, a law of the wake across visits, a cancellation law or
liveness.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreAgreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Semaphore.Model (State Waiter Profile)

/-! ## The encoding

Model request `n` has the identity handle `i<n>` and a current hint `h<n>`. A take that enrols
its request sets that request's entry of the table, and no other. -/

def ids : List Nat := [1, 2, 3]
def idName (n : Nat) : String := s!"i{n}"
def hintName (n : Nat) : String := s!"h{n}"
def envNames : List String := ids.flatMap (fun n => [idName n, hintName n]) ++ ["fresh"]
def envVals : List Val :=
  ids.flatMap (fun n => [Val.promise ⟨n⟩, Val.promise ⟨1000 + n⟩]) ++ [Val.promise ⟨9999⟩]

/-- A term's value in the scope of the handles. -/
def evalAt (src : TermSrc) : Option Val :=
  (src { names := envNames } []).toOption.bind (evalTerm envVals ·)

def listOf (xs : List TermSrc) : TermSrc :=
  xs.foldr (fun x acc => app "cons" [x, acc]) Queue.nilT

/-- The table: a request's current hint. -/
abbrev Table := Nat → TermSrc
def table0 : Table := fun n => var (hintName n)
def Table.set (tb : Table) (id : Nat) (hint : TermSrc) : Table :=
  fun n => if n = id then hint else tb n

def waiterTerm (tb : Table) (w : Waiter) : TermSrc :=
  Semaphore.mkWaiter (var (idName w.id)) (nat w.need) (tb w.id) (nat w.stamp)

/-- The cell's value for a model state: it loses nothing of the state. -/
def stateTerm (tb : Table) (s : State) : TermSrc :=
  record Semaphore.cellFields [("permits", nat s.permits), ("taken", nat s.taken),
    ("waiters", listOf (s.waiters.map (waiterTerm tb))), ("next", nat s.next)]

/-! ## The comparison -/

inductive Verdict
  /-- The term's whole result is the encoding of the model's. -/
  | agrees
  | differs
  /-- A term has no value. -/
  | stuck (which : String)
  deriving DecidableEq

/-- One comparison: the step term's whole result against the encoding of the model's. -/
def judge (step expected : TermSrc) : Verdict :=
  match evalAt step, evalAt expected with
  | some got, some want => if got = want then .agrees else .differs
  | none, _ => .stuck "the step term"
  | _, none => .stuck "the expected term"

/-- A deliberate defect of an expected result, for a red control. -/
inductive Mutation
  | exact
  /-- The reply is the other Boolean. -/
  | flipReply
  /-- The table stays as it was: the enrolled request keeps its old hint. -/
  | keepHint
  /-- The selected waiter stays in the list. -/
  | keepSelected

def takeExpected (mutation : Mutation) (s : State) (id n : Nat) : TermSrc :=
  let r := Semaphore.Model.take s id n
  let reply := match mutation with
    | .flipReply => !r.2
    | _ => r.2
  let tb := match mutation with
    | .keepHint => table0
    | _ => table0.set id (var "fresh")
  app "pair" [bool reply, stateTerm tb r.1]

def takeTerm (s : State) (id n : Nat) : TermSrc :=
  Semaphore.takeStep (nat n) (var (idName id)) (var "fresh") (stateTerm table0 s)

def takeAgrees (s : State) (id n : Nat) : Verdict :=
  judge (takeTerm s id n) (takeExpected .exact s id n)

def takeIfAvailableAgrees (s : State) (n : Nat) : Verdict :=
  let r := Semaphore.Model.takeIfAvailable s n
  judge (Semaphore.takeIfAvailableStep (nat n) (stateTerm table0 s))
    (app "pair" [bool r.2, stateTerm table0 r.1])

def releaseAgrees (s : State) (n : Nat) : Verdict :=
  let r := Semaphore.Model.release s n
  judge (Semaphore.releaseStep (nat n) (stateTerm table0 s))
    (app "pair" [tuple [nat r.2.1, bool r.2.2], stateTerm table0 r.1])

def visitExpected (mutation : Mutation) (s : State) (cursor : Nat) : TermSrc :=
  let r := Semaphore.Model.visit s cursor
  let reply := match r.2 with
    | some w => app "some" [waiterTerm table0 w]
    | none => Queue.noneT
  let next := match mutation with
    | .keepSelected => s
    | _ => r.1
  app "pair" [reply, stateTerm table0 next]

def visitAgrees (s : State) (cursor : Nat) : Verdict :=
  judge (Semaphore.visitStep (nat cursor) (stateTerm table0 s)) (visitExpected .exact s cursor)

def withdrawAgrees (s : State) (id : Nat) : Verdict :=
  judge (Semaphore.withdrawStep (var (idName id)) (stateTerm table0 s))
    (app "pair" [unit, stateTerm table0 (Semaphore.Model.withdraw s id)])

/-! ## The named controls C1 to C6 -/

/-- A total of 2, both taken, and B and C enrolled for 2 and for 1: the state of P1 before the
release. -/
def held : State := { permits := 2, taken := 2, waiters := [⟨2, 2, 0⟩, ⟨3, 1, 1⟩], next := 2 }

/-- The same state after a release of 2. -/
def freed : State := { held with taken := 0 }

/-- The scan case at its visit: one permit is free, B needs 2 and C needs 1. -/
def scan : State := { held with taken := 1 }

-- C1. A take where the count fits takes, and a take where it does not enrols at the end with
-- the step's hint.
#guard (Semaphore.Model.take freed 1 2).2 = true && takeAgrees freed 1 2 = .agrees
#guard (Semaphore.Model.take held 1 1).2 = false && takeAgrees held 1 1 = .agrees
-- C2. A take by a request whose entry is present: the entry leaves first. B takes where its
-- count fits, and B enrols again, at the end with a new stamp, where it does not.
#guard (Semaphore.Model.take freed 2 2).1.waiters = [⟨3, 1, 1⟩] && takeAgrees freed 2 2 = .agrees
#guard (Semaphore.Model.take held 2 2).1.waiters = [⟨3, 1, 1⟩, ⟨2, 2, 2⟩] &&
  takeAgrees held 2 2 = .agrees
-- C3. The take that never waits.
#guard takeIfAvailableAgrees freed 2 = .agrees && takeIfAvailableAgrees held 1 = .agrees
-- C4. A release within what is taken, and a release of more than is taken.
#guard (Semaphore.Model.release held 2).2 = (2, true) && releaseAgrees held 2 = .agrees
#guard (Semaphore.Model.release held 5).2 = (2, true) && releaseAgrees held 5 = .agrees
#guard (Semaphore.Model.release { permits := 2 } 1).2 = (2, false) &&
  releaseAgrees { permits := 2 } 1 = .agrees
-- C5. The visits of the cases: the head where it fits; the later smaller request on the scan
-- case; nobody where no permit is free; nobody past the last stamp.
#guard (Semaphore.Model.visit freed 0).2 = some ⟨2, 2, 0⟩ && visitAgrees freed 0 = .agrees
#guard (Semaphore.Model.visit scan 0).2 = some ⟨3, 1, 1⟩ && visitAgrees scan 0 = .agrees
#guard (Semaphore.Model.visit held 0).2 = none && visitAgrees held 0 = .agrees
#guard (Semaphore.Model.visit freed 2).2 = none && visitAgrees freed 2 = .agrees
-- C6. The withdrawals: an enrolled request leaves, and a request with no entry changes nothing.
#guard withdrawAgrees held 2 = .agrees && withdrawAgrees held 1 = .agrees

/-! ## Every state of a finite universe of the profile

The universe: a total of one to three; each count of taken permits up to the total; no waiter,
one waiter or two waiters, of the identities 1 and 2 in each order, each for one to three
permits. The stamps are 1 and 3, and the next stamp is 5, so a cursor falls before, between and
after them. -/

inductive Move
  | take (id n : Nat) | takeIfAvailable (n : Nat) | release (n : Nat) | visit (cursor : Nat)
  | withdraw (id : Nat)
  deriving Repr

def moves : List Move :=
  [.take 1 1, .take 1 2, .take 2 1, .take 2 3, .take 3 1, .take 3 2,
   .takeIfAvailable 0, .takeIfAvailable 1, .takeIfAvailable 2, .takeIfAvailable 3,
   .release 0, .release 1, .release 2, .release 5,
   .visit 0, .visit 1, .visit 2, .visit 3, .visit 4, .visit 6,
   .withdraw 1, .withdraw 2, .withdraw 3]

def Move.verdict (s : State) : Move → Verdict
  | .take id n => takeAgrees s id n
  | .takeIfAvailable n => takeIfAvailableAgrees s n
  | .release n => releaseAgrees s n
  | .visit cursor => visitAgrees s cursor
  | .withdraw id => withdrawAgrees s id

def Move.next (s : State) : Move → State
  | .take id n => (Semaphore.Model.take s id n).1
  | .takeIfAvailable n => (Semaphore.Model.takeIfAvailable s n).1
  | .release n => (Semaphore.Model.release s n).1
  | .visit cursor => (Semaphore.Model.visit s cursor).1
  | .withdraw id => Semaphore.Model.withdraw s id

def needs : List Nat := [1, 2, 3]

/-- The waiter lists of the universe: 25 lists. -/
def waiterLists : List (List Waiter) :=
  [[]] ++
  ([1, 2].flatMap fun a => needs.map fun n => [(⟨a, n, 1⟩ : Waiter)]) ++
  ([(1, 2), (2, 1)].flatMap fun (a, b) => needs.flatMap fun n => needs.map fun m =>
    [(⟨a, n, 1⟩ : Waiter), ⟨b, m, 3⟩])

def profileStates : List State :=
  [1, 2, 3].flatMap fun permits =>
  (List.range (permits + 1)).flatMap fun taken =>
  waiterLists.map fun waiters =>
    ({ permits := permits, taken := taken, waiters := waiters, next := 5 } : State)

def inProfile (s : State) : Bool := decide (Profile s)

/-- Every state of the universe is of the profile, and each move leaves the profile true: a
finite instance of the proved closure. -/
def closed : Bool :=
  profileStates.all fun s => inProfile s && moves.all fun m => inProfile (m.next s)

/-- The states and moves whose verdict is not `agrees`. -/
def disagreements : List (State × Nat) :=
  profileStates.flatMap fun s => moves.zipIdx.filterMap fun (m, i) =>
    if m.verdict s = .agrees then none else some (s, i)

#guard waiterLists.length = 25 && profileStates.length = 225 && moves.length = 23
#guard closed
-- All 5,175 comparisons agree.
#guard disagreements.isEmpty && profileStates.length * moves.length = 5175

/-! ## Outside the profile the comparison still agrees

No step reads the profile: the term and the model compute the same truncated subtraction, the
same removal by identity and the same first fitting waiter. So a step goal carries no premise
on the state. -/

/-- More taken than the total; a stamp that does not rise; a stamp above the next stamp; two
waiters of one identity. -/
def outside : List State :=
  [{ permits := 2, taken := 3, waiters := [⟨1, 1, 1⟩], next := 5 },
   { permits := 2, taken := 1, waiters := [⟨1, 2, 3⟩, ⟨2, 1, 1⟩], next := 5 },
   { permits := 2, taken := 0, waiters := [⟨1, 1, 7⟩], next := 5 },
   { permits := 3, taken := 1, waiters := [⟨1, 3, 1⟩, ⟨1, 1, 3⟩], next := 5 }]

#guard outside.all fun s => !inProfile s
#guard outside.all fun s => moves.all fun m => m.verdict s = .agrees

/-! ## The red controls M1 to M3: one part of an expected result changed -/

-- M1. C1's expected result with the other reply.
#guard judge (takeTerm freed 1 2) (takeExpected .flipReply freed 1 2) = .differs
-- M2. A take that enrols, with the table left as it was: the stored hint is the step's.
#guard judge (takeTerm held 2 2) (takeExpected .keepHint held 2 2) = .differs
-- A take that takes does not read the table's change.
#guard judge (takeTerm freed 2 2) (takeExpected .keepHint freed 2 2) = .agrees
-- M3. A visit's expected result with the selected waiter kept in the list.
#guard judge (Semaphore.visitStep (nat 0) (stateTerm table0 freed))
  (visitExpected .keepSelected freed 0) = .differs

/-! ## The faults F1 to F3 of the card's section 9, as changed step terms

Each fault is red at its own property. The checker types each changed step at the type of the
library's step, so typing alone does not catch it. -/

open Effect4.Queue (len notT ifT noneOf)

/-- The checker's type of a source term at a scope, at the native signature. -/
def typeOf (names : List String) (types : List Ty) (src : TermSrc) : Option Ty :=
  Queue.Model.typeAt nativeSignature names types src

/-- A field of a step's stored value, as a number. -/
def storedNat (step : TermSrc) (name : String) : Option Val :=
  evalAt (field (tupleAt step 1) name)

/-- F1. The head of the list alone is woken. -/
def visitHeadStep (cursor s : TermSrc) : TermSrc :=
  let waiters := field s "waiters"
  Semaphore.visitFrom
    (foldWith (app "take" [waiters, nat 1]) (noneOf waiters) fun _ w =>
      ifT (Semaphore.eligibleT cursor s w) waiters (noneOf waiters))
    s

-- The property: the visit's agreement on the scan case, where C must proceed. The head-only
-- visit differs there: it selects nobody.
#guard judge (visitHeadStep (nat 0) (stateTerm table0 scan)) (visitExpected .exact scan 0) =
  .differs
#guard evalAt (tupleAt (visitHeadStep (nat 0) (stateTerm table0 scan)) 0) =
  some Store.Val.none
-- It agrees where the head fits: the scan case tells the two apart.
#guard judge (visitHeadStep (nat 0) (stateTerm table0 freed)) (visitExpected .exact freed 0) =
  .agrees
-- Over the universe it differs exactly where the model selects a waiter that is not the head.
#guard profileStates.all fun s => [0, 1, 2, 3, 4, 6].all fun cursor =>
  (judge (visitHeadStep (nat cursor) (stateTerm table0 s)) (visitExpected .exact s cursor)
      != .agrees) ==
    (match (Semaphore.Model.visit s cursor).2 with
      | some w => s.waiters.head? != some w
      | none => false)
-- Typing does not catch it.
#guard decide (typeOf ["cursor", "s"] [.nat, Semaphore.cellTy]
    (visitHeadStep (var "cursor") (var "s")) =
  typeOf ["cursor", "s"] [.nat, Semaphore.cellTy] (Semaphore.visitStep (var "cursor") (var "s")))

/-- F2. A resumed request takes without a second check. -/
def takeBlindStep (need id _hint s : TermSrc) : TermSrc :=
  app "pair" [bool true,
    recordSet (recordSet s "taken" (app "add" [field s "taken", need])) "waiters"
      (Semaphore.removeWaiter (field s "waiters") id)]

/-- P9's state at B's late take: C took 1 while B yielded, so one permit is free. -/
def late : State := { permits := 2, taken := 1, next := 2 }

-- The property: the accounting. The blind take stores 3 taken at a total of 2. The library's
-- take stores 1 taken, and it enrols B again.
#guard storedNat (takeBlindStep (nat 2) (var (idName 2)) (var "fresh") (stateTerm table0 late))
  "taken" = some (.nat 3)
#guard storedNat (takeTerm late 2 2) "taken" = some (.nat 1) && takeAgrees late 2 2 = .agrees
#guard !inProfile { late with taken := 3 }
-- Where the count fits, the blind take is the library's take: P9's path shows the fault.
#guard evalAt (takeBlindStep (nat 2) (var (idName 2)) (var "fresh") (stateTerm table0 freed)) =
  evalAt (takeTerm freed 2 2)
-- Typing does not catch it.
#guard decide (typeOf ["need", "id", "hint", "s"]
    [.nat, Queue.idTy, Queue.idTy, Semaphore.cellTy]
    (takeBlindStep (var "need") (var "id") (var "hint") (var "s")) =
  some (.prod .bool Semaphore.cellTy))

/-- The count of the first entry of a list of waiters, and zero for no entry. -/
def firstNeed (rest : TermSrc) : TermSrc :=
  foldWith (app "take" [rest, nat 1]) (nat 0) fun _ w => field w "need"

/-- F3. The wake commits the selected waiter's count before that waiter runs: the grant at the
wake. -/
def visitGrantStep (cursor s : TermSrc) : TermSrc :=
  let waiters := field s "waiters"
  let rest := Semaphore.fromFirst cursor s
  ifT (app "isZero" [Semaphore.freeT s])
    (app "pair" [app "get" [noneOf waiters, nat 0], s])
    (app "pair" [app "get" [rest, nat 0],
      recordSet
        (recordSet s "waiters"
          (app "append" [app "take" [waiters, app "sub" [len waiters, len rest]],
            app "drop" [rest, nat 1]]))
        "taken" (app "add" [field s "taken", firstNeed rest])])

/-- The overtaking case at its first visit: B and C wait for 1 each, and 2 are free. -/
def overtaking : State := { permits := 2, waiters := [⟨2, 1, 0⟩, ⟨3, 1, 1⟩], next := 2 }

-- The property: a wake reserves nothing. The library's visit stores `taken` as it was. The
-- grant stores one more.
#guard storedNat (Semaphore.visitStep (nat 0) (stateTerm table0 overtaking)) "taken" =
  some (.nat 0)
#guard storedNat (visitGrantStep (nat 0) (stateTerm table0 overtaking)) "taken" = some (.nat 1)
#guard judge (visitGrantStep (nat 0) (stateTerm table0 overtaking))
  (visitExpected .exact overtaking 0) = .differs
-- A visit that selects nobody is the library's visit under the grant too.
#guard judge (visitGrantStep (nat 0) (stateTerm table0 held)) (visitExpected .exact held 0) =
  .agrees
-- Typing does not catch it.
#guard decide (typeOf ["cursor", "s"] [.nat, Semaphore.cellTy]
    (visitGrantStep (var "cursor") (var "s")) =
  typeOf ["cursor", "s"] [.nat, Semaphore.cellTy] (Semaphore.visitStep (var "cursor") (var "s")))

end Test.Program.SemaphoreAgreement
