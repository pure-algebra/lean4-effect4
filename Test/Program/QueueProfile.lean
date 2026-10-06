import Effect4.Laws.Modules.Queue.Profile
import ProofGraph.Plan

/-!
# The Queue's first profile: its pinned outputs and its finite controls

The predicate, its closure and the two closed forms are in
`src/Effect4/Laws/Modules/Queue/Profile.lean`. This battery pins the closure's axioms and its
plan status, and holds the finite controls: one red state for each condition of the predicate,
each first operation on one input, and the red controls of the premises.
-/

namespace Test.Program.QueueProfile
open Effect4.Queue.Model

/-- info: 'Effect4.Queue.Model.first_profile_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms first_profile_closed

-- The standing is derived from the proof. The counts are of this battery's tree, which holds
-- no step of the proof: the steps are in the law graph.
/--
info: Effect4.Queue.Model.first_profile_closed: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status first_profile_closed

/-! ## Controls: finite checks, one input each -/

/-- The profile on one state, as a Boolean. -/
def inProfile (s : State) : Bool := decide (FirstProfile s)

def T (id : Nat) : Taker := ⟨id, 1, 1⟩

-- The empty queue, and a state that the first operations reach.
#guard inProfile { capacity := some 2 }
#guard inProfile
  { capacity := some 1, messages := [1], takers := [T 1, T 2], offers := [⟨101, false, [2]⟩] }
-- Red controls, one for each condition. The phase, the strategy, the capacity.
#guard !inProfile { capacity := some 2, phase := .closing .ended }
#guard !inProfile { capacity := some 2, strategy := .sliding }
#guard !inProfile { capacity := some 0 }
#guard !inProfile {}
-- A stored taker with other bounds; a batch; an offer of two messages.
#guard !inProfile { capacity := some 2, takers := [⟨1, 2, 2⟩] }
#guard !inProfile { capacity := some 2, offers := [⟨7, true, [1]⟩] }
#guard !inProfile { capacity := some 2, offers := [⟨7, false, [1, 2]⟩] }
-- A peeker (Codex's witness: the model wakes it, and the cell's step names no peeker); an awaiter.
#guard !inProfile { capacity := some 2, takers := [T 1], peekers := [2] }
#guard !inProfile { capacity := some 2, awaiters := [3] }
-- One identity for two requests: two takers, and a taker with an offer.
#guard !inProfile { capacity := some 2, takers := [T 1, T 1] }
#guard !inProfile { capacity := some 2, takers := [T 1], offers := [⟨1, false, [5]⟩] }

/-- One step of the model from a state. -/
def next (s : State) (op : Op) : State := (step .none { s := s } op).s

def full : State := { capacity := some 1, messages := [1], takers := [T 1] }

-- The closed form of the accept pass: two of three single offers enter two free places.
#guard acceptLoop (some 2) [1] [⟨7, false, [5]⟩, ⟨8, false, [6]⟩, ⟨9, false, [7]⟩] =
  ([1, 5, 6], [⟨9, false, [7]⟩], [⟨7, .offered true⟩, ⟨8, .offered true⟩])
-- Red control of its premise: a batch enters in part, and the closed form says otherwise.
#guard acceptLoop (some 1) [1] [⟨7, true, [9, 8]⟩] !=
  entered (some 1) [1] [⟨7, true, [9, 8]⟩]
-- The wake: the earliest taker behind a message, and nobody at an empty buffer.
#guard wake full = [⟨1, .again⟩] && wake { full with messages := [] } = []
-- Red control of its premise: with a peeker the model wakes two requests.
#guard wake { full with peekers := [2] } = [⟨1, .again⟩, ⟨2, .again⟩]

-- Each first operation keeps the profile on one input.
#guard inProfile full && inProfile (next full (.take 1 1 1)) && inProfile (next full (.take 2 1 1))
#guard inProfile (next full (.offer 100 5)) && inProfile (next full .poll)
#guard inProfile (next full (.dropTake 1)) && inProfile (next full (.dropOffer 100))
-- Red control of the request's premise: an offer by a waiting taker's identity leaves the profile.
#guard !inProfile (next full (.offer 1 5))
-- Red controls of the first operations: a peek and a batch each leave the profile.
#guard !inProfile (next { capacity := some 1 } (.peek 2))
#guard !inProfile (next full (.offerAll 100 [5, 6]))

end Test.Program.QueueProfile
