import Effect4.Laws.Machine.Edits
import Effect4.Laws.Auto.Frames

/-!
Concept: reactive-scheduling, R11; consumer: machine-edits field and token-filter adapters.
These readers use the real machine and generated field rules.
The controls retain changed-field premises and the settlement subalphabet boundary.
Token removal checks are finite evaluations; they establish no runtime simulation.
-/
set_option autoImplicit false
namespace Test.Machine.EditFields
open Effect4 Effect4.Machine

abbrev M := RunMachine Unit Unit Nat Unit Unit Unit Unit Unit Nat
abbrev F := RunFiber Unit Unit Nat Unit Unit Unit Unit Unit
abbrev E := Edit Unit Unit Nat Unit Unit Unit Unit Unit Nat
  (Prim Unit Unit Nat Unit Unit Unit Unit) (FrameFiber Unit Unit Nat Unit Unit Unit Unit)
  (FrameEvent Unit Unit Nat Unit Unit Unit Unit)

def owner : F := {RunFiber.make ⟨0⟩ (.success 0) true (2048, false) () with
  observers := [.resumeAwait ⟨1⟩ 9 .awaitValue, .callback 3, .countdown ⟨1⟩ 9,
    .resumeAwait ⟨1⟩ 10 .awaitValue]}
def peer : F := {owner with id := ⟨1⟩, observers := [.countdown ⟨0⟩ 9, .untrackChild ⟨0⟩]}
def initial : M :=
  { fibers := [owner, peer], races := [], nextId := 2, nextToken := 0,
    nextRace := 0, middlewareInstalled := false, armed := [], state := 7, trace := [], stuck := none }

-- The real token cleanup removes both matching shapes globally and retains observer order.
#guard ((initial.dropToken 9).fibers.map (·.observers)) ==
  [[.callback 3, .resumeAwait ⟨1⟩ 10 .awaitValue], [.untrackChild ⟨0⟩]]
example : (applyFiberEdit (.dropToken 9) initial).1 = initial.dropToken 9 := rfl
example : ((Edit.dropToken 9 : E).apply initial).state = initial.state :=
  Edit.frame (.dropToken 9) .state initial (by intro impossible; cases impossible)
example : ((Edit.setState 8 : E).apply initial).trace = initial.trace :=
  Edit.frame (.setState 8) .trace initial (by intro impossible; cases impossible)
example : (initial.update peer).trace = initial.trace := RunMachine.update_keeps_trace peer initial

-- Both edit interpretations attach to the same current record and leave missing owners alone.
example : (applyFiberEdit (.observe ⟨0⟩ (.callback 8)) initial).1 =
    initial.observe ⟨0⟩ (.callback 8) := rfl
example : (Edit.observe ⟨0⟩ (.callback 8) : E).apply initial =
    initial.observe ⟨0⟩ (.callback 8) := rfl
#guard ((initial.observe ⟨0⟩ (.callback 8)).fibers.map (·.observers)) ==
  [owner.observers ++ [.callback 8], peer.observers]
#guard ((initial.observe ⟨9⟩ (.callback 8)).fibers.map (·.observers)) ==
  [owner.observers, peer.observers]

-- An emit misses stored fibers; a new fiber does not, and it is not a settlement write.
example : ((Edit.emit [] : E).apply initial).fibers = initial.fibers :=
  Edit.keeps_fibers (.emit []) (by intro impossible; cases impossible) initial
example : ¬ (Edit.appendFiber peer : E).missesFibers := by
  intro missing
  exact missing rfl
example : ¬ (Edit.appendFiber peer : E).settlementWrite := fun impossible => impossible

structure Phased (m : M) (token : Nat) : Prop where
  tokenMatch : m.nextToken = token
  clear : m.stuck = none

#frame_rules Phased (state := m)

example (held : Phased initial 0) : Phased {initial with state := 8} 0 :=
  Phased.frame_state initial 0 held 8
example (held : Phased initial 0) (token : Nat) (matching : token = 0) :
    Phased {initial with nextToken := token} 0 :=
  Phased.frame_nextToken initial 0 held token matching
example : Phased initial 0 := ⟨rfl, rfl⟩
example : ¬ Phased {initial with nextToken := 1} 0 := by
  intro held
  have impossible : (1 : Nat) = 0 := held.tokenMatch
  contradiction

end Test.Machine.EditFields
