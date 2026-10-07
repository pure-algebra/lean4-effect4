module

public import Effect4.Machine.Alphabets

/-!
# Machine.Integers — the evaluation of the integer rows

The rows `plus` and `minus`, and `lt` and `eq` widened to `int` (decisions rows 108, 121 and
309; `docs/research/2026-10-07-packet-integers.md`, slice 5). An integer's image is a natural
(`Val.nat`) or a negative integer (`Store.Val.negInt n` is `-(n + 1)`), so one integer has one
image. The rows compute exactly and with no bound: the bound is the target profile's refusal,
written once at `Profile.grow` (DI-56; the packet's slices 6 and 7). Their statements against
the integers are `intAdd_spec`, `intSub_spec`, `intLt_spec` and `intEq_spec`
(`src/Effect4/Laws/Machine/Integers.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- **The one addition of two magnitudes that can leave the profile.** In the reference it is
plain addition. A target lowers it to its refusal outside the bound (DI-56, decisions row 108). -/
@[noinline] def Profile.grow (a b : Nat) : Nat := a + b

/-- `-x` on an integer image. Zero has one image, so `-0` is `nat 0`. -/
def intNeg : Val → Option Val
  | .nat 0 => some (.nat 0)
  | .nat (n + 1) => some (.negInt n)
  | .negInt n => some (.nat (n + 1))
  | _ => none

/-- `x + y` on two integer images. Two magnitudes of one sign grow; two of different signs do
not. -/
def intAdd : Val → Val → Option Val
  | .nat a, .nat b => some (.nat (Profile.grow a b))
  | .nat a, .negInt b => some (if b < a then .nat (a - (b + 1)) else .negInt (b - a))
  | .negInt a, .nat b => some (if a < b then .nat (b - (a + 1)) else .negInt (a - b))
  | .negInt a, .negInt b => some (.negInt (Profile.grow (a + 1) (b + 1) - 1))
  | _, _ => none

/-- `x - y`: the sum of `x` and `-y`. Exact, where `sub` on naturals stops at zero. -/
def intSub (x y : Val) : Option Val := (intNeg y).bind (intAdd x)

/-- `x < y` on two integer images. -/
def intLt : Val → Val → Option Val
  | .nat a, .nat b => some (.bool (decide (a < b)))
  | .nat _, .negInt _ => some (.bool false)
  | .negInt _, .nat _ => some (.bool true)
  | .negInt a, .negInt b => some (.bool (decide (b < a)))
  | _, _ => none

/-- `x = y` on two integer images: one value has one image, so the test compares frames. -/
def intEq : Val → Val → Option Val
  | .nat a, .nat b => some (.bool (decide (a = b)))
  | .negInt a, .negInt b => some (.bool (decide (a = b)))
  | .nat _, .negInt _ => some (.bool false)
  | .negInt _, .nat _ => some (.bool false)
  | _, _ => none

end Effect4.Program
