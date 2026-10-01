import QCheck.ValElim
import QCheck.JsonElim
import ProbeQ.Ty
import Effect4.Program.Ty

/-!
# Q1 controls: the generated nested companions against the hand-written ones

Seat Q probe (2026-10-01). The emission `--kind <Type>=elim` of the copy
`Q/tools/Effect4Gen/Fold.lean` was run on the two families whose companions the tree wrote by
hand, under the prefix `QCheck` so they sit beside the originals:

1. The generated eliminator of `Store.Val` has exactly the statement of the hand
   `Store.Val.ind` (`Store/Carrier/Val.lean:270`): the two constants are equal by `rfl`, which
   elaborates only if their types agree.
2. The generated Boolean equality of `Store.Val` is the hand `Val.beq` (`Val.lean:1112`), as a
   function: proved from the two `beq_iff`s.
3. `Json`'s hand companions are private (`Data/Json.lean:312`, `:369`); the generated equality
   decides the same relation as the public instance `instDecidableEqJson`, proved.
4. The generated structural `Repr` of `ProbeQ.Ty` prints, on record-free values, the text Lean's
   derived `Repr` of today's `Effect4.Program.Ty` prints (constructor prefix renamed; compared at
   an unbounded width, since the shorter probe names move the formatter's line breaks); and at
   the default width, line-broken values and records included, exactly what the `partial`
   derived `Repr` of `ProbeQ.Ty` itself prints.
-/

set_option autoImplicit false

namespace Q1

/-- 1. Same statement as the hand eliminator. -/
example : @Effect4.Store.QCheck.Val.ind = @Effect4.Store.Val.ind := rfl

/-- 2. The generated equality is the hand one. -/
theorem val_beq_agrees (a b : Effect4.Store.Val) :
    Effect4.Store.QCheck.Val.beq a b = Effect4.Store.Val.beq a b := by
  rw [Bool.eq_iff_iff, Effect4.Store.QCheck.Val.beq_iff, Effect4.Store.Val.beq_iff]

/-- 3. The generated equality on `Json` decides equality, as the public instance does. -/
theorem json_beq_decides (a b : Effect4.Json) :
    Effect4.QCheck.Json.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Effect4.QCheck.Json.beq_iff, decide_eq_true_iff]

/-! ### 4. The structural `Repr` -/

/-- A record-free probe type as today's `Ty`; `none` at a record. -/
def toReal : ProbeQ.Ty → Option Effect4.Program.Ty
  | .never => some .never
  | .unit => some .unit
  | .nat => some .nat
  | .int => some .int
  | .string => some .string
  | .bool => some .bool
  | .handle s => some (.handle s)
  | .option t => (toReal t).map .option
  | .list t => (toReal t).map .list
  | .prod a b => do pure (.prod (← toReal a) (← toReal b))
  | .except a b => do pure (.except (← toReal a) (← toReal b))
  | .exitOf a b => do pure (.exitOf (← toReal a) (← toReal b))
  | .causeOf t => (toReal t).map .causeOf
  | .fiberOf a b => do pure (.fiberOf (← toReal a) (← toReal b))
  | .union a b => do pure (.union (← toReal a) (← toReal b))
  | .lit s => some (.lit s)
  | .refOf t => (toReal t).map .refOf
  | .deferredOf a b => do pure (.deferredOf (← toReal a) (← toReal b))
  | .var i => some (.var i)
  | .unknown => some .unknown
  | .record _ => none

def generated (t : ProbeQ.Ty) : String := Std.Format.pretty (ProbeQ.Ty.repr t 0)

/-- At a width no sample reaches, so no line is broken. -/
def flat (f : Std.Format) : String := Std.Format.pretty f 100000

def deep : Nat → ProbeQ.Ty
  | 0 => .lit "a long literal that forces the formatter to break the line"
  | n + 1 => .union (.prod (.option (deep n)) (.handle "Scope.Scope")) (.deferredOf (.var n) (deep n))

def samples : List ProbeQ.Ty :=
  [ .never, .unit, .nat, .int, .string, .bool, .handle "Context.Context<unknown>", .option .nat,
    .list (.lit "x\"y"), .prod .nat .string, .except .never .bool, .exitOf .unit .never,
    .causeOf (.lit "E"), .fiberOf .nat .never, .union .nat .string, .lit "", .refOf .nat,
    .deferredOf .nat .string, .var 0, .var 7, .unknown, deep 1, deep 3, deep 5 ]

-- On every record-free sample, the generated text is the derived text of today's `Ty`.
#guard samples.all fun t =>
  match toReal t with
  | some r => (flat (ProbeQ.Ty.repr t 0)).replace "ProbeQ.Ty." "Effect4.Program.Ty." == flat (repr r)
  | none => false

-- The samples do exercise line breaking at the default width.
#guard (generated (deep 5)).contains '\n'

end Q1

namespace Q1Derived

/-! The `partial` derived `Repr` of the nested probe type, for the record values: what an
`#eval` would print, compared with the structural one. -/
deriving instance Repr for ProbeQ.Ty

def derived (t : ProbeQ.Ty) : String := Std.Format.pretty (repr t)

def records : List ProbeQ.Ty :=
  [ .record [], .record [("a", .nat)], .record [("b", .nat), ("a", .record [("c", .lit "z")])],
    .option (.record [("x", .union .nat .string), ("y", .list (.record []))]) ]

#guard records.all fun t => Q1.generated t == derived t
#guard Q1.samples.all fun t => Q1.generated t == derived t

end Q1Derived

#print axioms Q1.val_beq_agrees
#print axioms Q1.json_beq_decides
