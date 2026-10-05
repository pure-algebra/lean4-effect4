import Effect4

/-!
# The traversal census's fixture

Planted definitions over `Ty`, one per way a definition can read a family value, whose rows
`#traversal_census` (`src/Effect4/Laws/Auto/Traversals.lean`) must get exactly right, pinned by
`#guard_msgs` in `Test/Audit/TraversalCensus.lean` (`under Test.Audit.TraversalFixture`). They
exist to be read by that command and have no other consumer. Four are shapes the instrument
missed until 2026-10-01 (organization verifier, `verify.md` §3 M1):

- `wfPair`: well-founded recursion on two arguments, compiled through a `_unary` helper over
  `WellFounded.Nat.fix` — `wf` (was `opaque`: the fixpoint is in the helper);
- `fuelWalk`: well-founded recursion on a fuel argument, the `Ty` destructed at each step —
  `wf` (was `opaque`);
- `privateDepth`: a private structural traversal — a row marked `[private]` (was no row);
- `notUnion`: a one-level `match` with a catch-all, compiled through a sparse `casesOn` named
  after another definition — `one-level` (was `opaque`).

And the shapes it must keep, or now classes by what the code does rather than by how the
compiler encoded the `match`:

- `isOption`: a one-level `match` naming every constructor, compiled through `Ty.casesOn` —
  `one-level` (was `structural`);
- `depth`: structural recursion on the family — `structural`;
- `fuelDepth`: structural recursion on a fuel argument, the `Ty` destructed in step —
  `structural`;
- `viaDepth`: hands the value to `depth` — `delegates`;
- `pairUp`: neither looks inside nor hands it on — `opaque`.
-/

namespace Test.Audit.TraversalFixture

open Effect4.Program (Ty)

/-- Two arguments, a `Nat` measure: the compiler packs them into a `_unary` helper. -/
def wfPair (a b : Ty) : Bool :=
  match a, b with
  | .option x, .option y => wfPair x y
  | .list x, .list y => wfPair x y
  | .never, _ => true
  | _, _ => false
termination_by sizeOf a + sizeOf b

/-- Recursion on fuel; the `Ty` it recurses with is rebuilt, not a child. -/
def fuelWalk (fuel : Nat) (t : Ty) : Nat :=
  match fuel, t with
  | 0, _ => 0
  | n + 1, .option u => fuelWalk n (.list u) + 1
  | n + 1, .list u => fuelWalk n u
  | _ + 1, _ => 0
termination_by fuel

/-- Private: a row under the name it was written with. -/
private def privateDepth : Ty → Nat
  | .option t => privateDepth t + 1
  | _ => 0

/-- A catch-all: the `match` compiles through a sparse `casesOn`. -/
def notUnion : Ty → Bool
  | .union _ _ => false
  | _ => true

/-- Every constructor named: the `match` compiles through `Ty.casesOn`. -/
def isOption : Ty → Bool
  | .option _ => true
  | .never | .unit | .nat | .int | .string | .bool | .handle _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _ | .union _ _ | .lit _ | .refOf _
  | .deferredOf _ _ | .var _ | .unknown | .record _ | .map _ _ | .tuple _ | .app _ _ | .null
  | .undefined | .number | .bytes => false

/-- Structural recursion on the family. -/
def depth : Ty → Nat
  | .option t => depth t + 1
  | .prod a b => max (depth a) (depth b) + 1
  | _ => 0

/-- Structural recursion on the fuel: `.list u` is not a child of `.option u`, so the recursion
cannot be on the `Ty`. -/
def fuelDepth : Nat → Ty → Nat
  | 0, _ => 0
  | n + 1, .option u => fuelDepth n (.list u) + 1
  | n + 1, .list u => fuelDepth n u
  | _ + 1, _ => 0

def viaDepth (t : Ty) : Nat := depth t + 1

def pairUp (t : Ty) : Ty × Ty := (t, t)

end Test.Audit.TraversalFixture
