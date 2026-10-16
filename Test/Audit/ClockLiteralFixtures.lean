import Effect4.Data.ClockMillis
import Effect4.Store.Carrier.Val
import Effect4.Run.Basic

/-! Three admitted clock construction routes beyond OCaml's native integer range.
The companion audit inspects their actual persisted mono-LCNF translations. The last section
holds the controls of a builtin callback's arity and of a host's reactor at a root. -/
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

/-! ### A builtin callback, and a host's reactor at a root -/

/-- A builtin passed as a callback (`List.appendTR._redArg` in mono LCNF, a declaration with no
kernel constant) is a known callable, so its result is known data. -/
@[noinline] def combine (op : List Nat → List Nat → List Nat) (a b : List Nat) : List Nat := op a b
def throughBuiltinCallback : ClockMillis := ClockMillis.ofNat (combine (· ++ ·) [1] [2]).length
/-- The same callback over a narrowed argument: its result still carries the narrowing. -/
def throughBuiltinCallbackNarrowed : ClockMillis :=
  ClockMillis.ofNat ((combine (· ++ ·) [4611686018427387904] []).headD 0)

/-- A host's reactor at a root: its answer is host ingress (decisions row 394 (1)), so a natural
of it reaches the clock as a checked answer of the tape does. -/
@[noinline] def reactorClock (r : Effect4.Run.Reactor Nat) (row : Effect4.Program.Row) :
    ClockMillis :=
  match r row .unit 0 with
  | some (.ofExit (.success (.nat n)), _) => ClockMillis.ofNat n
  | _ => 0
/-- A callback of another type at a root stays unknown production. -/
@[noinline] def otherCallbackClock
    (f : Effect4.Program.Row → Effect4.Store.Val → Option Effect4.Store.Val)
    (row : Effect4.Program.Row) : ClockMillis :=
  match f row .unit with
  | some (.nat n) => ClockMillis.ofNat n
  | _ => 0
/-- A reactor beside a second relevant field: a record, not unboxed to its reactor. -/
structure ReactorBox where
  reactor : Effect4.Run.Reactor Nat
  label : Nat
/-- A reactor inside other data at a root stays unknown production. (A structure with the reactor
as its one relevant field is unboxed to it, and so is a reactor.) -/
@[noinline] def boxedReactorClock (box : ReactorBox) (row : Effect4.Program.Row) : ClockMillis :=
  match box.reactor row .unit 0 with
  | some (.ofExit (.success (.nat n)), _) => ClockMillis.ofNat n
  | _ => 0
/-- A function of a reactor's shape whose two states differ is no reactor: unknown production. -/
@[noinline] def mixedStateClock
    (f : Effect4.Program.Row → Effect4.Store.Val → Nat → Option (Effect4.Api.HostSession.Answer × Bool))
    (row : Effect4.Program.Row) : ClockMillis :=
  match f row .unit 0 with
  | some (.ofExit (.success (.nat n)), _) => ClockMillis.ofNat n
  | _ => 0

/-- A typed host at a root (decisions row 405): a record of methods `A → σ → B × σ` over the
host's state, `Effect4.Run.Reactor.method`'s shape. Two fields, so the compiler keeps the record. -/
structure NatHost (σ : Type) where
  read : Unit → σ → Nat × σ
  bump : Nat → σ → Bool × σ
/-- A typed host's answer reaches the clock as a reactor's does. -/
@[noinline] def hostClock (h : NatHost Nat) : ClockMillis := ClockMillis.ofNat (h.read () 0).1
/-- A record of functions that thread no state is no host. -/
structure NatFns where
  read : Unit → Nat
  other : Unit → Nat
/-- A record of other functions at a root stays unknown production. -/
@[noinline] def fnsClock (f : NatFns) : ClockMillis := ClockMillis.ofNat (f.read ())

#guard direct.toDecimal = "4611686018427387904"
#guard numeral.toDecimal = "4611686018427387905"
#guard positive.toDecimal = "4611686018427387905"

end Test.ClockLiteralFixtures
