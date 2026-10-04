import Effect4.Program.Ty

/-! Exact positional projection for decisions rows 159 and 197.
The checker normalizes the target once, then checks every union alternative.
A list type supplies no fixed positions. -/

namespace Effect4.Program.Tuple

/-- Select one column, with exact bounds on every inhabited alternative.
Products are the canonical two-column tuple image. Bottom supplies no value. -/
def project (index : Nat) : Ty → Option Ty
  | .tuple items => items[index]?
  | .prod first second => [first, second][index]?
  | .union left right => do
    let a ← project index left
    let b ← project index right
    some (Ty.join a b)
  | .never => some .never
  | _ => none

/-- Normalize only the checked type; preserve the stored term and its exact index. -/
def typeAt (target : Ty) (index : Nat) : Option Ty := project index target.normalize

end Effect4.Program.Tuple
