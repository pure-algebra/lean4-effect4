import Effect4.Data.ClockMillis
import Effect4.Store.Canonical

/-!
# Canonical logical milliseconds

The exact wire image is a canonical nonnegative decimal string. Reading rejects any
other spelling and never routes large values through a bounded host-number payload.
-/

set_option autoImplicit false

namespace Effect4.Store
namespace ClockCanonical

def toVal (value : ClockMillis) : Val := .str value.toDecimal

def ofVal : Val → Option ClockMillis
  | .str text => ClockMillis.ofDecimal text
  | _ => none

def shapeDoc : ShapeDoc := ⟨.named "ClockMillis", [("ClockMillis", .string)]⟩

theorem ofVal_toVal (value : ClockMillis) : ofVal (toVal value) = some value :=
  ClockMillis.ofDecimal_toDecimal value

theorem ofVal_exact {value : Val} {clock : ClockMillis} (h : ofVal value = some clock) :
    value = toVal clock := by
  cases value
  case str text => exact congrArg Val.str (ClockMillis.ofDecimal_exact h)
  all_goals exact nomatch h

theorem fits (value : ClockMillis) : shapeDoc.accepts (toVal value) = true := rfl

end ClockCanonical

instance instCanonicalClockMillis : Canonical ClockMillis where
  shape := ClockCanonical.shapeDoc
  toVal := ClockCanonical.toVal
  ofVal := ClockCanonical.ofVal
  ofVal_toVal := ClockCanonical.ofVal_toVal
  ofVal_exact := ClockCanonical.ofVal_exact
  fits := ClockCanonical.fits

end Effect4.Store
