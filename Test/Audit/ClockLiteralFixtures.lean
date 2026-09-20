import Effect4.Data.ClockMillis
import Effect4.Store.Val

/-! Three admitted clock construction routes beyond OCaml's native integer range.
The companion audit inspects their actual persisted mono-LCNF translations. -/
namespace Test.ClockLiteralFixtures
open Effect4

def direct : ClockMillis := ClockMillis.ofNat 4611686018427387904

def numeral : ClockMillis := 4611686018427387905

def positive : ClockMillis :=
  let predecessor := 4611686018427387904
  let same := predecessor
  ClockMillis.positive same

/-- Arithmetic on an already narrowed ordinary Nat must not silently become exact clock data. -/
def narrowed (n : Nat) : ClockMillis := ClockMillis.ofNat (n + 4611686018427387904)

@[noinline] def wrapper (n : Nat) : ClockMillis := ClockMillis.ofNat n
@[noinline] def nestedWrapper (n : Nat) : ClockMillis := wrapper n

def throughWrapper : ClockMillis := wrapper 4611686018427387904
def throughNestedWrapper : ClockMillis := nestedWrapper 4611686018427387904

/-- The bounded clock refusal must leave unrelated ordinary Nat lowering alone. -/
@[noinline] def hugeNat (_u : Unit) : Nat := 4611686018427387904
@[noinline] def nestedHugeNat (u : Unit) : Nat := hugeNat u
def throughFactory : ClockMillis := ClockMillis.ofNat (hugeNat ())
def throughNestedFactory : ClockMillis := ClockMillis.ofNat (nestedHugeNat ())
@[noinline] def throughUnknown (f : Nat → Nat) (n : Nat) : ClockMillis :=
  ClockMillis.ofNat (f n)
@[noinline] def applyClock (f : Nat → ClockMillis) (n : Nat) : ClockMillis := f n
def throughClockCallback : ClockMillis := applyClock ClockMillis.ofNat 4611686018427387904
@[noinline] def applyGeneric {α : Type} (f : Nat → α) (n : Nat) : α := f n
def throughGenericClockCallback : ClockMillis := applyGeneric ClockMillis.ofNat 4611686018427387904
@[noinline] def clockFromValue (value : Effect4.Store.Val) : ClockMillis :=
  match value with
  | .nat n => ClockMillis.ofNat n
  | _ => 0
def throughValue : ClockMillis := clockFromValue (.nat 4611686018427387904)
@[noinline] def scalarIdentity (n : Nat) : Nat := n
@[noinline] def applyNat (f : Nat → Nat) (n : Nat) : Nat := f n
def closedCallback : ClockMillis := ClockMillis.ofNat (applyNat scalarIdentity 7)
@[noinline] def hugeAdd (n : Nat) : Nat := n + 4611686018427387904
def throughKnownNatCallback : ClockMillis := ClockMillis.ofNat (applyNat hugeAdd 0)

structure CallbackBox where
  data : Nat
  read : Unit → Nat
@[noinline] def readCallback (box : CallbackBox) : Nat := box.read ()
def closedRecordCallback (n : Nat) : ClockMillis :=
  ClockMillis.ofNat (readCallback ⟨n, fun _ => n⟩)
@[noinline] def unknownRecordCallback (box : CallbackBox) : ClockMillis :=
  ClockMillis.ofNat (readCallback box)

structure NatBox where
  value : Nat
@[noinline] def unknownContainer (produce : Unit → NatBox) : ClockMillis :=
  ClockMillis.ofNat (produce ()).value

def unrelatedNat (n : Nat) : Nat := n + 4611686018427387904

#guard direct.toDecimal = "4611686018427387904"
#guard numeral.toDecimal = "4611686018427387905"
#guard positive.toDecimal = "4611686018427387905"

end Test.ClockLiteralFixtures
