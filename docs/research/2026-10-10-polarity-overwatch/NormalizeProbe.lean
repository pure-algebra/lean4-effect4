import Effect4.Laws.Program.Template
import Effect4.Program.Polarity

set_option autoImplicit false

namespace Test.PolarityNormalizeOverwatch
open Effect4.Program

-- The proposed bridge keeps binding order and duplicate precedence.
def normalizeBindings (s : Ty.Subst) : Ty.Subst :=
  s.map fun (i, t) => (i, t.normalize)

def at_ (s : Ty.Subst) (i : Nat) : Ty := (s.lookup i).getD .never
def substitutions : List Ty.Subst := [
  [], [(0, .nat)], [(0, .union .nat .int)],
  [(0, .union .nat .int), (0, .bool)],
  [(3, .prod (.union .nat .bool) .string)],
  [(0, .record [("x", false, .nat), ("x", false, .bool)])]]

def templates : List Ty := [.var 0, .var 3, .list (.var 0),
  .union (.var 0) (.var 3), .refOf (.var 0),
  .record [("z", false, .var 3), ("a", true, .var 0)]]

#guard substitutions.all fun s => [0, 1, 3, 9].all fun i =>
  at_ (normalizeBindings s) i == (at_ s i).normalize
#guard substitutions.all fun s => templates.all fun t =>
  (Ty.instantiate (normalizeBindings s) t).normalize == (Ty.instantiate s t).normalize

-- subN cannot be replaced by raw sub on the original bindings.
def unnormalized : Ty := .prod (.union .nat .bool) .string
#guard Ty.subN unnormalized unnormalized.normalize
#guard !(Ty.sub unnormalized unnormalized.normalize)

-- After normalization the required raw comparison holds.
#guard Ty.sub unnormalized.normalize unnormalized.normalize
#eval (substitutions.length * 4, substitutions.length * templates.length)

end Test.PolarityNormalizeOverwatch
