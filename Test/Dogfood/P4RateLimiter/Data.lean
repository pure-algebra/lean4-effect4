import Test.Dogfood.StageData
import Effect4.Author

/-! Program data shared by the battery and scenario fixtures. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.P4RateLimiter

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The program -/

/-- `interface Window { used, admitted, rejected }`, every field a number. -/
def windowFields : List (String × Bool × Ty) :=
  [("used", false, .nat), ("admitted", false, .nat), ("rejected", false, .nat)]

/-- The type of the window, its fields in canonical order. -/
def windowTy : Ty :=
  .record [("admitted", false, .nat), ("rejected", false, .nat), ("used", false, .nat)]

/-- `{ used, admitted, rejected }` as a value, its fields in canonical order. -/
def windowVal (used admitted rejected : Nat) : Val :=
  recordOf ["admitted", "rejected", "used"] [.nat admitted, .nat rejected, .nat used]

/-- `{ used: 0, admitted: 0, rejected: 0 }`. -/
def window0 : TermSrc :=
  record windowFields [("used", nat 0), ("admitted", nat 0), ("rejected", nat 0)]

/-- The decision of one request over the window `w` (`p4-rate-limiter.ts`, `request`):
`w.used < 3 ? [true, { ...w, used: w.used + 1, admitted: w.admitted + 1 }] :
[false, { ...w, rejected: w.rejected + 1 }]`. `ite` evaluates both arms, and both are pure. -/
def decision (w : TermSrc) : TermSrc :=
  app "ite" [app "lt" [field w "used", nat 3],
    app "pair" [bool true,
      recordSet (recordSet w "used" (app "succ" [field w "used"]))
        "admitted" (app "succ" [field w "admitted"])],
    app "pair" [bool false, recordSet w "rejected" (app "succ" [field w "rejected"])]]

/-- The refill daemon (`p4-rate-limiter.ts`, `refill`): forever, sleep a window, then reset the
count with `Ref.update(state, w => ({ ...w, used: 0 }))`. `Effect.forever` is an `iterate` whose
test is the constant `true`. -/
def refill (state : TermSrc) : Src NativeOp :=
  iterateWith (bool true)
    { while_ := fun _ => bool true
      body := fun _ => andThen (Effect.sleep (nat 1000))
        (Ref.update "w" (recordSet (var "w") "used" (nat 0)) state)
      step := fun c _ => c }

-- `Straight` and `Looped` are the fragments of `run_eq_meaning` and `loopAgreement`. The whole
-- limiter is in neither.
-- The request alone is in both: one store step.
-- The refill daemon parks on the clock: in neither fragment.

end Test.Dogfood.P4RateLimiter
