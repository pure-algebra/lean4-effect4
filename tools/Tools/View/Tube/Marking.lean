import Tools.View.CellSheet

/-!
# Tools.View.Tube.Marking — what the Queue's cell holds, at each command of a run

Each frame's cell (`CellSheet.Scene.run`, the Queue's own step terms evaluated) read into what the
tube picture places: the messages held, front first; the offers that wait, each with the messages
it still holds; the takers that wait; the takers that a step woke; and the message a step answered.
A message is its value, a request its numeral.
-/

namespace Tools.View.Tube
open Effect4 Effect4.Program
open Tools.View.CellSheet (Frame)

abbrev Val := Effect4.Store.Val

/-- **A marking**: what the cell holds after a command. -/
structure Marking where
  capacity : Nat
  held : List Nat
  offers : List (Nat × List Nat)
  takers : List Nat
  woken : List Nat := []
  answered : Option Nat := none
deriving Repr, Inhabited

/-- A field of a record value. -/
def field (v : Val) (name : String) : Option Val := (Machine.Record.entries v).bind (·.lookup name)

def nats : Val → List Nat
  | .list xs => xs.filterMap fun | .nat n => some n | _ => none
  | _ => []

def handleOf : Option Val → Option Nat
  | some (.handle _ n) => some n
  | _ => none

def records : Option Val → List Val
  | some (.list xs) => xs
  | _ => []

/-- **The marking of a frame.** -/
def marking (f : Frame) : Marking :=
  let c := f.cell
  let answer : Option Val := f.answer.map (·.2)
  let parts : List Val := match answer with | some (Store.Val.list xs) => xs | _ => []
  { capacity := match field c "cap" with | some (.nat n) => n | _ => 0
    held := ((field c "msgs").map nats).getD []
    offers := (records (field c "offers")).filterMap fun o =>
      (handleOf (field o "id")).map fun i => (i, ((field o "rest").map nats).getD [])
    takers := (records (field c "takers")).filterMap fun t => handleOf (field t "id")
    woken := (records (parts.getLast?)).filterMap fun t => handleOf (field t "id")
    answered := match parts.head? with | some (.some (.nat m)) => some m | _ => none }

/-- The messages that wait at the inlet, in the order they will enter. -/
def Marking.waiting (m : Marking) : List Nat := m.offers.flatMap (·.2)

end Tools.View.Tube
