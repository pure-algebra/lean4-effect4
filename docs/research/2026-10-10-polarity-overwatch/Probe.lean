import Test.Program.RowPolarity

set_option autoImplicit false

namespace Test.PolarityOverwatch
open Effect4.Program

-- Finite instantiation controls for the existing planned claim.
-- The probe never applies the planned theorem.
def samples : List Ty := [
  .var 0, .var 1, .var 3, .nat, .unknown,
  .option (.var 0), .list (.var 0), .causeOf (.var 0),
  .refOf (.var 0), .deferredOf (.var 0) (.var 1),
  .fiberOf (.var 0) (.var 1), .prod (.var 0) (.var 1),
  .except (.var 0) (.var 1), .exitOf (.var 0) (.var 1),
  .map (.var 0) (.var 1), .tuple [.var 0, .var 3],
  .app "ReadonlyArray" [.var 0], .app "Function" [.var 0, .var 1],
  .app "UnknownHead" [.var 0, .var 3],
  .union (.var 0) (.var 1), .union .unknown (.refOf (.var 0)),
  .record [("z", false, .var 0), ("a", true, .var 3)],
  .record [("x", false, .nat), ("x", false, .refOf (.var 0))],
  .refOf (.map (.var 0) (.list (.var 1)))]

def substitutions : List Ty.Subst := [
  [], [(0, .nat)], [(0, .int)], [(0, .number)], [(0, .unknown)],
  [(0, .nat), (1, .int), (3, .bool)],
  [(0, .int), (1, .number), (3, .unknown)],
  [(0, .union .nat .int), (1, .number), (3, .bool)],
  [(0, .nat), (0, .int), (3, .bool)]]

def premise (t : Ty) (a b : Ty.Subst) : Bool :=
  t.varsOf.all fun i => (t.polarity .sub i).select
    (Ty.sub (a.at i) (b.at i)) (Ty.sub (b.at i) (a.at i))

def conclusion (t : Ty) (a b : Ty.Subst) : Bool :=
  Ty.sub (Ty.instantiate a t) (Ty.instantiate b t)

def casesChecked : List (Ty × Ty.Subst × Ty.Subst) :=
  samples.flatMap fun t => substitutions.flatMap fun a => substitutions.map fun b => (t, a, b)

def admittedCases := casesChecked.filter fun (t, a, b) => premise t a b
def counterexamples := admittedCases.filter fun (t, a, b) => !conclusion t a b

#guard !admittedCases.isEmpty
#guard admittedCases.length < casesChecked.length
#guard counterexamples.isEmpty
#eval (samples.length, substitutions.length, casesChecked.length, admittedCases.length, counterexamples.length)

-- Invariance is a real premise for a cell. A one-way numeric relation is insufficient.
#guard Ty.sub .nat .int
#guard !(Ty.sub .int .nat)
#guard !(premise (.refOf (.var 0)) [(0, .nat)] [(0, .int)])
#guard !(conclusion (.refOf (.var 0)) [(0, .nat)] [(0, .int)])
#guard premise (.list (.var 0)) [(0, .nat)] [(0, .int)]
#guard conclusion (.list (.var 0)) [(0, .nat)] [(0, .int)]

-- A sufficient polarity condition is not necessary on raw types.
#guard (Ty.union .unknown (.refOf (.var 0))).polarity .sub 0 == Var4.inv
#guard !(premise (.union .unknown (.refOf (.var 0))) [(0, .nat)] [(0, .int)])
#guard conclusion (.union .unknown (.refOf (.var 0))) [(0, .nat)] [(0, .int)]
#guard conclusion (.union .unknown (.refOf (.var 0))) [(0, .int)] [(0, .nat)]

-- Every parameter in today's source tables is inside the battery's fixed range.
open Test.Program.RowPolarity in
#guard (rowTmpls ++ atomTmpls).all fun t =>
  (t.answer.varsOf ++ t.request.flatMap Ty.varsOf).all params.contains

-- The fixed range misses an invariant occurrence at a later parameter.
def later : Test.Program.RowPolarity.Tmpl :=
  ⟨"later", [.var 3], .refOf (.var 3)⟩
#guard !Test.Program.RowPolarity.answerAboveCo later
#guard !Var4.le (later.answer.polarity .sub 3) .co

-- Source-derived indices remove this extra census assumption.
def answerAboveCoDerived (t : Test.Program.RowPolarity.Tmpl) : Bool :=
  t.answer.varsOf.any fun i => !Var4.le (t.answer.polarity .sub i) .co
#guard answerAboveCoDerived later
open Test.Program.RowPolarity in
#guard (rowTmpls ++ atomTmpls).all fun t => answerAboveCoDerived t == answerAboveCo t
open Test.Program.RowPolarity in
#eval (rowTmpls.length, atomTmpls.length,
  (rowTmpls ++ atomTmpls).flatMap (fun t => t.answer.varsOf ++ t.request.flatMap Ty.varsOf) |>.eraseDups)

end Test.PolarityOverwatch
