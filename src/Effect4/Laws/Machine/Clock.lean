import Effect4.Machine.Timer
import Effect4.Store.Domain.Clock
import Effect4.Laws.Auto.Obligations

/-!
The exact-clock obligations: source statements and pending markers were checked before
proof attempts in docs/research/2026-09-20-m1-evidence/clock/{ClockWanted,TimerWanted}.lean.
The core keeps its small structural proofs; this law-side instrument checks their complete
statement list without importing proof search into the runtime root.
-/

namespace Effect4

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  ClockMillis.ofNat_toNat ClockMillis.toNat_ofNat ClockMillis.toNat_add

namespace ClockMillis.M1

def ofNat_toNat (a : ClockMillis) : ProofGraph.Obligation (ClockMillis.ofNat a.toNat = a) := ⟨⟩
def toNat_ofNat (n : Nat) : ProofGraph.Obligation ((ClockMillis.ofNat n).toNat = n) := ⟨⟩
def toNat_add (a b : ClockMillis) : ProofGraph.Obligation ((a + b).toNat = a.toNat + b.toNat) := ⟨⟩

#typed_state_obligations Effect4.ClockMillis.M1 ceiling 0 using aesop (rule_sets := [Effect4.Stores])

end ClockMillis.M1

namespace Machine.TimerStore
universe u

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  cancel_pending dueMin_first fireNext_none clockStep_finish
attribute [aesop safe forward (rule_sets := [Effect4.Stores])]
  dueMin_none_of_late dueMin_mem dueMin_le dueMin_min fireNext_now fireNext_owed clockStep_owed
attribute [aesop safe apply (rule_sets := [Effect4.Stores])]
  empty_wf empty_quiet sleep_wf cancel_wf fireNext_wf clockStep_wf

def M1Clock.empty_wf : ProofGraph.Obligation (empty.WF) := ⟨⟩

def M1Clock.empty_quiet : ProofGraph.Obligation (empty.Quiet) := ⟨⟩

def M1Clock.sleep_wf {self : TimerStore} (_h : self.WF) (fiber : FiberId) (token : Nat) (millis : ClockMillis) : ProofGraph.Obligation ((self.sleep fiber token millis).WF) := ⟨⟩

def M1Clock.cancel_wf {self : TimerStore} (_h : self.WF) (fiber : FiberId) (token : Nat) : ProofGraph.Obligation ((self.cancel fiber token).WF) := ⟨⟩

def M1Clock.cancel_pending (self : TimerStore) (fiber : FiberId) (token : Nat) : ProofGraph.Obligation ((self.cancel fiber token).wake.pending fiber token = false) := ⟨⟩

def M1Clock.dueMin_none_of_late (target : ClockMillis) : ProofGraph.Obligation (∀ (l : List (Waiter ClockMillis)), dueMin target l = none → ∀ w ∈ l, target < w.payload) := ⟨⟩

def M1Clock.dueMin_mem (target : ClockMillis) : ProofGraph.Obligation (∀ (l : List (Waiter ClockMillis)) (m : Waiter ClockMillis), dueMin target l = some m → m ∈ l) := ⟨⟩

def M1Clock.dueMin_le (target : ClockMillis) : ProofGraph.Obligation (∀ (l : List (Waiter ClockMillis)) (m : Waiter ClockMillis), dueMin target l = some m → m.payload ≤ target) := ⟨⟩

def M1Clock.dueMin_min (target : ClockMillis) : ProofGraph.Obligation (∀ (l : List (Waiter ClockMillis)) (m : Waiter ClockMillis), dueMin target l = some m →
      ∀ x ∈ l, x.payload ≤ target → m.payload ≤ x.payload) := ⟨⟩

def M1Clock.dueMin_first (target : ClockMillis) (w : Waiter ClockMillis) (rest : List (Waiter ClockMillis))
    (_hw : w.payload ≤ target) (_hrest : ∀ x ∈ rest, w.payload ≤ x.payload) : ProofGraph.Obligation (dueMin target (w :: rest) = some w) := ⟨⟩

def M1Clock.fireNext_none {κ : Type u} (self : TimerStore) (target : ClockMillis) (resume : κ)
    (_h : dueMin target self.wake.waiters = none) : ProofGraph.Obligation (self.fireNext target resume = (none, self)) := ⟨⟩

def M1Clock.fireNext_now {κ : Type u} (self : TimerStore) (target : ClockMillis) (resume : κ) (w : Waiter ClockMillis)
    (_h : dueMin target self.wake.waiters = some w) : ProofGraph.Obligation ((self.fireNext target resume).1 = some ⟨w.fiber, w.token, resume, WakeMode.now⟩ ∧
      (self.fireNext target resume).2.now = w.payload ∧
      (self.fireNext target resume).2.wake.waiters = self.wake.waiters.erase w) := ⟨⟩

def M1Clock.fireNext_owed {κ : Type u} (self : TimerStore) (target : ClockMillis) (resume : κ) (o : Owed κ)
    (_h : (self.fireNext target resume).1 = some o) : ProofGraph.Obligation (o.code = resume ∧ o.mode = WakeMode.now) := ⟨⟩

def M1Clock.fireNext_wf {κ : Type u} {self : TimerStore} (_hwf : self.WF) (target : ClockMillis) (resume : κ) : ProofGraph.Obligation ((self.fireNext target resume).2.WF) := ⟨⟩

def M1Clock.clockStep_finish {κ : Type u} (self : TimerStore) (millis : ClockMillis) (resume : κ)
    (_h : dueMin (self.target.getD (self.now + millis)) self.wake.waiters = none) : ProofGraph.Obligation (self.clockStep millis resume =
      (none, { self with now := self.target.getD (self.now + millis), target := none })) := ⟨⟩

def M1Clock.clockStep_owed {κ : Type u} (self : TimerStore) (millis : ClockMillis) (resume : κ) (o : Owed κ)
    (_h : (self.clockStep millis resume).1 = some o) : ProofGraph.Obligation (o.code = resume ∧ o.mode = WakeMode.now) := ⟨⟩

def M1Clock.clockStep_wf {κ : Type u} {self : TimerStore} (_hwf : self.WF) (millis : ClockMillis) (resume : κ) : ProofGraph.Obligation ((self.clockStep millis resume).2.WF) := ⟨⟩

#typed_state_obligations Effect4.Machine.TimerStore.M1Clock ceiling 0
  using aesop (rule_sets := [Effect4.Stores])

end Machine.TimerStore
end Effect4

/-! Decimal transport and the canonical store image. The pending source statements were
checked before the proofs in the clock evidence's decimal and canonical snapshots. -/
namespace Effect4

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  ClockMillis.Decimal.readBytes_digits ClockMillis.Decimal.readChars_core
  ClockMillis.Decimal.readBytes_repr ClockMillis.ofDecimal_toDecimal
  Store.ClockCanonical.ofVal_toVal Store.ClockCanonical.fits
attribute [aesop safe forward (rule_sets := [Effect4.Stores])]
  ClockMillis.ofDecimal_exact Store.ClockCanonical.ofVal_exact

namespace ClockMillis.M1Decimal

def readBytes_digits (chars : List Char) (initial : Nat)
    (_h : ∀ c ∈ chars, c.isDigit = true) : ProofGraph.Obligation
    (Decimal.readBytes (chars.flatMap String.utf8EncodeChar) initial = Nat.ofDigitChars 10 chars initial) := ⟨⟩

def readChars_core (fuel n : Nat) (tail : List Char) (_h : n < fuel) : ProofGraph.Obligation
    (Nat.ofDigitChars 10 (Nat.toDigitsCore 10 fuel n tail) 0 = Nat.ofDigitChars 10 tail n) := ⟨⟩

def readBytes_repr (n : Nat) : ProofGraph.Obligation
    (Decimal.readBytes (Nat.repr n).toByteArray.data.toList = n) := ⟨⟩

def ofDecimal_toDecimal (a : ClockMillis) : ProofGraph.Obligation
    (ClockMillis.ofDecimal a.toDecimal = some a) := ⟨⟩

def ofDecimal_exact (text : String) (a : ClockMillis) (_h : ClockMillis.ofDecimal text = some a) :
    ProofGraph.Obligation (text = a.toDecimal) := ⟨⟩

#typed_state_obligations Effect4.ClockMillis.M1Decimal ceiling 0
  using aesop (rule_sets := [Effect4.Stores])

end ClockMillis.M1Decimal

namespace Store.ClockCanonical.M1

def ofVal_toVal (value : ClockMillis) : ProofGraph.Obligation
    (ClockCanonical.ofVal (ClockCanonical.toVal value) = some value) := ⟨⟩

def ofVal_exact (value : Val) (clock : ClockMillis) (_h : ClockCanonical.ofVal value = some clock) :
    ProofGraph.Obligation (value = ClockCanonical.toVal clock) := ⟨⟩

def fits (value : ClockMillis) : ProofGraph.Obligation
    (ClockCanonical.shapeDoc.accepts (ClockCanonical.toVal value) = true) := ⟨⟩

#typed_state_obligations Effect4.Store.ClockCanonical.M1 ceiling 0
  using aesop (rule_sets := [Effect4.Stores])

end Store.ClockCanonical.M1
end Effect4
