import Effect4.Data.ClockMillis
import Effect4.Data.Ascii
import Effect4.Store.Canonical
import Effect4.Laws.Auto.Obligations

set_option autoImplicit false
namespace Effect4.ClockMillis.DecimalPlan

/-- A decimal fold on UTF-8 bytes; the canonical spelling check below supplies admission. -/
def readBytes (bytes : List UInt8) (initial : Nat := 0) : Nat :=
  bytes.foldl (fun n byte => 10 * n + (byte.toNat - 48)) initial

def read (text : String) : Option ClockMillis :=
  let bytes := text.toByteArray.data.toList
  let n := readBytes bytes
  if bytes = (Nat.repr n).toByteArray.data.toList then some (ofNat n) else none

namespace Wanted

def readBytes_digits (chars : List Char) (initial : Nat)
    (_h : ∀ c ∈ chars, c.isDigit = true) : ProofGraph.Obligation
    (readBytes (chars.flatMap String.utf8EncodeChar) initial = Nat.ofDigitChars 10 chars initial) := ⟨⟩
#proof_wanted readBytes_digits

def readChars_core (fuel n : Nat) (tail : List Char) (_h : n < fuel) : ProofGraph.Obligation
    (Nat.ofDigitChars 10 (Nat.toDigitsCore 10 fuel n tail) 0 = Nat.ofDigitChars 10 tail n) := ⟨⟩
#proof_wanted readChars_core

def readBytes_repr (n : Nat) : ProofGraph.Obligation
    (readBytes (Nat.repr n).toByteArray.data.toList = n) := ⟨⟩
#proof_wanted readBytes_repr

def read_toDecimal (a : ClockMillis) : ProofGraph.Obligation (read a.toDecimal = some a) := ⟨⟩
#proof_wanted read_toDecimal

def read_exact (text : String) (a : ClockMillis) (_h : read text = some a) :
    ProofGraph.Obligation (text = a.toDecimal) := ⟨⟩
#proof_wanted read_exact

end Wanted

end Effect4.ClockMillis.DecimalPlan
namespace Effect4.Store.ClockPlan

def toVal (value : ClockMillis) : Val := .str value.toDecimal

def ofVal : Val → Option ClockMillis
  | .str text => ClockMillis.DecimalPlan.read text
  | _ => none

def shape : ShapeDoc := ⟨.named "ClockMillis", [("ClockMillis", .string)]⟩

namespace Wanted

def ofVal_toVal (value : ClockMillis) : ProofGraph.Obligation (ofVal (toVal value) = some value) := ⟨⟩
#proof_wanted ofVal_toVal

def ofVal_exact (value : Val) (clock : ClockMillis) (_h : ofVal value = some clock) :
    ProofGraph.Obligation (value = toVal clock) := ⟨⟩
#proof_wanted ofVal_exact

def fits (value : ClockMillis) : ProofGraph.Obligation (shape.accepts (toVal value) = true) := ⟨⟩
#proof_wanted fits

end Wanted
end Effect4.Store.ClockPlan
