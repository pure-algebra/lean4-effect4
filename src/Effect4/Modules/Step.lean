module

public import Effect4.Schema.FieldRef
public import Effect4.Modules.Words

/-!
# Modules.Step — a module's step as first-order data over `Ty`

A **step** is the pure part of one operation of a composed module: a term over the operation's
inputs that answers a value (decisions row 330, slice L2). Here a step is data:

- **The sort** is `Step Γ t`: a step over inputs of the types `Γ` that answers a value of type
  `t`. An input is a position in `Γ` (`Input`), and a field is a position in a record's field
  list (`Schema.FieldRef`). The syntax holds no function.
- **The signature**: an input, the literals `bool`, `nat` and `unit`, the Boolean words `not`,
  `and`, `or` and `ite`, the numeric words `add`, `sub`, `lt`, `eq` and `isZero`, the product
  words `pair`, `fst` and `snd`, `some`, a field's read `get` and overwrite `set`, and the list
  words `emptyLike`, `len`, `snoc`, `append`, `take`, `drop` and `head`.
- **The algebra and its fold** (`StepAlgebra`, `Step.cata`): one field per constructor, and the
  one map out of the syntax. Every interpretation below is an algebra.

The arrows out of a step, each a fold:

| Arrow | Kind | Answers |
| --- | --- | --- |
| `Step.term` | translation | the source term, with the builder words of `src/Effect4/Modules/Words.lean` |
| `Step.eval` | denotation | the value on the carriers of an identity context (`Schema.Model.CarrierAt`) |
| `Step.writes` | footprint | the names of the fields that its overwrites name |
| `Step.spine` | footprint | the input whose record it updates, when it is an update spine |
| `Step.canonical` | check | whether each record it reads or writes has ascending names |
| `Step.normal` | check | whether each type where the checker needs a normal form is certified to have one |

The laws are proved once for the language (`src/Effect4/Laws/Modules/Step.lean`). A step's term
reads the encoding of its value, at every scope. It types at the step's type, at every scope.
On an update spine, a field that no overwrite names keeps its value. A module's step written as
data inherits the three, with no proof of its own.
-/

@[expose] public section

namespace Effect4.Modules
open Effect4.Program Effect4.Program.Authoring Effect4.Store Effect4.Schema Effect4.Schema.Model

/-- **An input of a step, by position** in the list of its input types. -/
inductive Input : List Ty → Ty → Type where
  | here (t : Ty) (rest : List Ty) : Input (t :: rest) t
  | there (u : Ty) {rest : List Ty} {t : Ty} : Input rest t → Input (u :: rest) t

namespace Input

/-- The input's position. -/
def index : {Γ : List Ty} → {t : Ty} → Input Γ t → Nat
  | _, _, .here _ _ => 0
  | _, _, .there _ x => x.index + 1

/-- The caller's term at the input's position, from a list of terms; `unit` past its end. -/
def source {Γ : List Ty} {t : Ty} (srcs : List TermSrc) (x : Input Γ t) : TermSrc :=
  srcs.getD x.index unit

end Input

/-- The values of a list of inputs on the carriers of an identity context, one per input. -/
def Inputs (L : Leaves) : List Ty → Type
  | [] => Unit
  | t :: rest => CarrierAt L t × Inputs L rest

/-- The value of one input. -/
def Input.get {L : Leaves} : {Γ : List Ty} → {t : Ty} → Input Γ t → Inputs L Γ → CarrierAt L t
  | _, _, .here _ _, vs => vs.1
  | _, _, .there _ x, vs => x.get vs.2

/-- **A step over inputs of the types `Γ` that answers a value of type `t`.** -/
inductive Step (Γ : List Ty) : Ty → Type where
  | var {t : Ty} : Input Γ t → Step Γ t
  | bool (b : Bool) : Step Γ .bool
  | nat (n : Nat) : Step Γ .nat
  | unit : Step Γ .unit
  | not : Step Γ .bool → Step Γ .bool
  | and : Step Γ .bool → Step Γ .bool → Step Γ .bool
  | or : Step Γ .bool → Step Γ .bool → Step Γ .bool
  | ite {t : Ty} : Step Γ .bool → Step Γ t → Step Γ t → Step Γ t
  | add : Step Γ .nat → Step Γ .nat → Step Γ .nat
  | sub : Step Γ .nat → Step Γ .nat → Step Γ .nat
  | lt : Step Γ .nat → Step Γ .nat → Step Γ .bool
  | eq : Step Γ .nat → Step Γ .nat → Step Γ .bool
  | isZero : Step Γ .nat → Step Γ .bool
  | pair {a b : Ty} : Step Γ a → Step Γ b → Step Γ (.prod a b)
  | fst {a b : Ty} : Step Γ (.prod a b) → Step Γ a
  | snd {a b : Ty} : Step Γ (.prod a b) → Step Γ b
  | some {t : Ty} : Step Γ t → Step Γ (.option t)
  | get {fs : List (String × Bool × Ty)} {t : Ty} : Step Γ (.record fs) → FieldRef fs t → Step Γ t
  | set {fs : List (String × Bool × Ty)} {t : Ty} :
      Step Γ (.record fs) → FieldRef fs t → Step Γ t → Step Γ (.record fs)
  | emptyLike {t : Ty} : Step Γ (.list t) → Step Γ (.list t)
  | len {t : Ty} : Step Γ (.list t) → Step Γ .nat
  | snoc {t : Ty} : Step Γ (.list t) → Step Γ t → Step Γ (.list t)
  | append {t : Ty} : Step Γ (.list t) → Step Γ (.list t) → Step Γ (.list t)
  | take {t : Ty} : Step Γ (.list t) → Step Γ .nat → Step Γ (.list t)
  | drop {t : Ty} : Step Γ (.list t) → Step Γ .nat → Step Γ (.list t)
  | head {t : Ty} : Step Γ (.list t) → Step Γ (.option t)

/-- **The step algebra**: a carrier at each type, and one field per constructor. -/
structure StepAlgebra (Γ : List Ty) (R : Ty → Type) where
  var : {t : Ty} → Input Γ t → R t
  bool : Bool → R .bool
  nat : Nat → R .nat
  unit : R .unit
  not : R .bool → R .bool
  and : R .bool → R .bool → R .bool
  or : R .bool → R .bool → R .bool
  ite : {t : Ty} → R .bool → R t → R t → R t
  add : R .nat → R .nat → R .nat
  sub : R .nat → R .nat → R .nat
  lt : R .nat → R .nat → R .bool
  eq : R .nat → R .nat → R .bool
  isZero : R .nat → R .bool
  pair : {a b : Ty} → R a → R b → R (.prod a b)
  fst : {a b : Ty} → R (.prod a b) → R a
  snd : {a b : Ty} → R (.prod a b) → R b
  some : {t : Ty} → R t → R (.option t)
  get : {fs : List (String × Bool × Ty)} → {t : Ty} → R (.record fs) → FieldRef fs t → R t
  set : {fs : List (String × Bool × Ty)} → {t : Ty} → R (.record fs) → FieldRef fs t → R t →
    R (.record fs)
  emptyLike : {t : Ty} → R (.list t) → R (.list t)
  len : {t : Ty} → R (.list t) → R .nat
  snoc : {t : Ty} → R (.list t) → R t → R (.list t)
  append : {t : Ty} → R (.list t) → R (.list t) → R (.list t)
  take : {t : Ty} → R (.list t) → R .nat → R (.list t)
  drop : {t : Ty} → R (.list t) → R .nat → R (.list t)
  head : {t : Ty} → R (.list t) → R (.option t)

namespace Step

variable {Γ : List Ty}

/-- **The fold**: the one map out of the syntax into an algebra. -/
def cata {R : Ty → Type} (alg : StepAlgebra Γ R) : {t : Ty} → Step Γ t → R t
  | _, .var x => alg.var x
  | _, .bool b => alg.bool b
  | _, .nat n => alg.nat n
  | _, .unit => alg.unit
  | _, .not a => alg.not (cata alg a)
  | _, .and a b => alg.and (cata alg a) (cata alg b)
  | _, .or a b => alg.or (cata alg a) (cata alg b)
  | _, .ite c a b => alg.ite (cata alg c) (cata alg a) (cata alg b)
  | _, .add a b => alg.add (cata alg a) (cata alg b)
  | _, .sub a b => alg.sub (cata alg a) (cata alg b)
  | _, .lt a b => alg.lt (cata alg a) (cata alg b)
  | _, .eq a b => alg.eq (cata alg a) (cata alg b)
  | _, .isZero a => alg.isZero (cata alg a)
  | _, .pair a b => alg.pair (cata alg a) (cata alg b)
  | _, .fst p => alg.fst (cata alg p)
  | _, .snd p => alg.snd (cata alg p)
  | _, .some a => alg.some (cata alg a)
  | _, .get r f => alg.get (cata alg r) f
  | _, .set r f v => alg.set (cata alg r) f (cata alg v)
  | _, .emptyLike xs => alg.emptyLike (cata alg xs)
  | _, .len xs => alg.len (cata alg xs)
  | _, .snoc xs x => alg.snoc (cata alg xs) (cata alg x)
  | _, .append xs ys => alg.append (cata alg xs) (cata alg ys)
  | _, .take xs n => alg.take (cata alg xs) (cata alg n)
  | _, .drop xs n => alg.drop (cata alg xs) (cata alg n)
  | _, .head xs => alg.head (cata alg xs)

/-! ## The translation into source terms -/

/-- The term algebra: each constructor's builder word, at the caller's terms for the inputs. -/
def termAlg (src : {t : Ty} → Input Γ t → TermSrc) : StepAlgebra Γ (fun _ => TermSrc) where
  var x := src x
  bool b := Authoring.bool b
  nat n := Authoring.nat n
  unit := Authoring.unit
  not a := notT a
  and a b := andT a b
  or a b := orT a b
  ite c a b := ifT c a b
  add a b := app "add" [a, b]
  sub a b := app "sub" [a, b]
  lt a b := app "lt" [a, b]
  eq a b := app "eq" [a, b]
  isZero a := app "isZero" [a]
  pair a b := app "pair" [a, b]
  fst p := app "fst" [p]
  snd p := app "snd" [p]
  some a := app "some" [a]
  get r f := field r f.name
  set r f v := recordSet r f.name v
  emptyLike xs := noneOf xs
  len xs := Modules.len xs
  snoc xs x := Modules.snoc xs x
  append xs ys := app "append" [xs, ys]
  take xs n := app "take" [xs, n]
  drop xs n := app "drop" [xs, n]
  head xs := app "get" [xs, Authoring.nat 0]

/-- **The step's source term**, at the caller's terms for its inputs. -/
def term (src : {t : Ty} → Input Γ t → TermSrc) {t : Ty} (e : Step Γ t) : TermSrc :=
  cata (termAlg src) e

/-! ## The denotation on carriers -/

/-- The value algebra at an identity context and the inputs' values. -/
def evalAlg (L : Leaves) (vs : Inputs L Γ) : StepAlgebra Γ (CarrierAt L) where
  var x := x.get vs
  bool b := (b : Bool)
  nat n := (n : Nat)
  unit := ()
  not := fun (a : Bool) => !a
  and := fun (a b : Bool) => a && b
  or := fun (a b : Bool) => a || b
  ite := fun {_} (c : Bool) a b => if c then a else b
  add := fun (a b : Nat) => a + b
  sub := fun (a b : Nat) => a - b
  lt := fun (a b : Nat) => decide (a < b)
  eq := fun (a b : Nat) => decide (a = b)
  isZero := fun (a : Nat) => decide (a = 0)
  pair a b := (a, b)
  fst p := p.1
  snd p := p.2
  some a := (Option.some a : Option _)
  get r f := f.get r
  set r f v := f.set r v
  emptyLike := fun {t} _ => ([] : List (CarrierAt L t))
  len := fun {t} (xs : List (CarrierAt L t)) => xs.length
  snoc := fun {t} (xs : List (CarrierAt L t)) x => xs ++ [x]
  append := fun {t} (xs ys : List (CarrierAt L t)) => xs ++ ys
  take := fun {t} (xs : List (CarrierAt L t)) (n : Nat) => xs.take n
  drop := fun {t} (xs : List (CarrierAt L t)) (n : Nat) => xs.drop n
  head := fun {t} (xs : List (CarrierAt L t)) => xs.head?

/-- **The step's value** at an identity context and the inputs' values. -/
def eval (L : Leaves) (vs : Inputs L Γ) {t : Ty} (e : Step Γ t) : CarrierAt L t :=
  cata (evalAlg L vs) e

/-! ## Footprints and checks -/

/-- The footprint algebra: the names that the overwrites name. -/
def writesAlg : StepAlgebra Γ (fun _ => List String) where
  var _ := []
  bool _ := []
  nat _ := []
  unit := []
  not a := a
  and a b := a ++ b
  or a b := a ++ b
  ite c a b := c ++ a ++ b
  add a b := a ++ b
  sub a b := a ++ b
  lt a b := a ++ b
  eq a b := a ++ b
  isZero a := a
  pair a b := a ++ b
  fst p := p
  snd p := p
  some a := a
  get r _ := r
  set r f v := r ++ v ++ [f.name]
  emptyLike xs := xs
  len xs := xs
  snoc xs x := xs ++ x
  append xs ys := xs ++ ys
  take xs n := xs ++ n
  drop xs n := xs ++ n
  head xs := xs

/-- **The names of the fields that the step's overwrites name.** -/
def writes {t : Ty} (e : Step Γ t) : List String := cata writesAlg e

/-- The spine algebra: the position of the input whose record the step updates, or `none`. -/
def spineAlg : StepAlgebra Γ (fun _ => Option Nat) where
  var x := Option.some x.index
  bool _ := none
  nat _ := none
  unit := none
  not _ := none
  and _ _ := none
  or _ _ := none
  ite _ a b := if a = b then a else none
  add _ _ := none
  sub _ _ := none
  lt _ _ := none
  eq _ _ := none
  isZero _ := none
  pair _ _ := none
  fst _ := none
  snd _ := none
  some _ := none
  get _ _ := none
  set r _ _ := r
  emptyLike _ := none
  len _ := none
  snoc _ _ := none
  append _ _ := none
  take _ _ := none
  drop _ _ := none
  head _ := none

/-- **The update spine**: the input whose record the step answers, with some fields overwritten.
An input, a choice between two spines of one input, and an overwrite of a spine are spines. -/
def spine {t : Ty} (e : Step Γ t) : Option Nat := cata spineAlg e

/-- A check algebra: the conjunction of the children's checks, and a node's own test at a field's
read and overwrite. -/
def checkAlg (atRecord : List (String × Bool × Ty) → Bool) (atType : Ty → Bool) :
    StepAlgebra Γ (fun _ => Bool) where
  var _ := true
  bool _ := true
  nat _ := true
  unit := true
  not a := a
  and a b := a && b
  or a b := a && b
  ite {t} c a b := atType t && (c && (a && b))
  add a b := a && b
  sub a b := a && b
  lt a b := a && b
  eq a b := a && b
  isZero a := a
  pair a b := a && b
  fst p := p
  snd p := p
  some a := a
  get := fun {fs} {_} r _ => atRecord fs && r
  set := fun {fs} {_} r _ v => atRecord fs && (r && v)
  emptyLike xs := xs
  len xs := xs
  snoc {t} xs x := atType t && (xs && x)
  append {t} xs ys := atType t && (xs && ys)
  take xs n := xs && n
  drop xs n := xs && n
  head xs := xs

/-- **The reading check**: each record that the step reads or writes has strictly ascending
names, so the machine's read and overwrite are the field's. -/
def canonical {t : Ty} (e : Step Γ t) : Bool :=
  cata (checkAlg (fun fs => decide (Field.Ascending Field.bytesKey fs)) (fun _ => true)) e

/-- **The typing check**: each record that the step reads or writes is certified to be its own
normal form, and so is the type of each selection and of each list it extends
(`Ty.certNormal`, `src/Effect4/Program/TyNormal.lean`). It reduces by evaluation. -/
def normal {t : Ty} (e : Step Γ t) : Bool :=
  cata (checkAlg (fun fs => (Ty.record fs).certNormal) (fun t => t.certNormal)) e

end Step
end Effect4.Modules
