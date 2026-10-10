import Effect4.Laws.Program.TypeAlgebra
import Effect4.Program.Polarity

set_option autoImplicit false

namespace Test.PolarityMembershipOverwatch
open Effect4.Program

def witnesses : List Ty := [
  .refOf (.var 0),
  .app "Opaque" [.var 0],
  .app "Opaque" [.refOf (.var 0)],
  .refOf (.app "Opaque" [.var 0])]

#guard witnesses.map Ty.valueVars == [false, true, true, false]

def readings : List Var4 := [.bi, .co, .contra, .inv]
def readAt (cell app : Var4) : HeadReading :=
  { HeadReading.sub with refOf := cell, app := fun _ _ => app }

def agreesOnWitnesses (cell app : Var4) : Bool :=
  witnesses.all fun t =>
    Var4.le (t.polarity (readAt cell app) 0) .co == t.valueVars

-- All relevant scalar readings fail the proposed exact connector.
#guard readings.all fun cell => readings.all fun app => !agreesOnWitnesses cell app
#eval (readings.length * readings.length, witnesses.map Ty.valueVars)

-- Positive fragment: invariant cell positions and ignored opaque arguments agree
-- on the first three specimens. The fourth needs the structural-occurrence bit.
#guard (witnesses.take 3).all fun t =>
  Var4.le (t.polarity (readAt .inv .bi) 0) .co == t.valueVars
#guard (witnesses.drop 3).map (fun t =>
  Var4.le (t.polarity (readAt .inv .bi) 0) .co) == [true]

-- The existing paired summary retains the information that the scalar fold loses.
#guard (cata_ty Ty.valueVarsAlg (.app "Opaque" [.var 0])) == (false, true)
#guard (cata_ty Ty.valueVarsAlg (.app "Opaque" [.nat])) == (true, true)
#guard Ty.valueVars (.refOf (.app "Opaque" [.var 0])) == false
#guard Ty.valueVars (.refOf (.app "Opaque" [.nat])) == true

end Test.PolarityMembershipOverwatch
