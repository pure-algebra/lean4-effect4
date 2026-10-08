module

public import Effect4.Schema.FieldRef
public import Effect4.Modules.Words
public import Effect4.Program.Authoring.Tuples

/-!
# Modules.Step — a module's step as first-order data over `Ty`

A **step** is the pure part of one operation of a composed module: a term over the operation's
inputs that answers a value (decisions row 330, slice L2). Here a step is data:

- **The sort** is `Step Γ t`: a step over inputs of the types `Γ` that answers a value of type
  `t`. An input is a position in `Γ` (`Input`), and a field is a position in a record's field
  list (`Schema.FieldRef`). The syntax holds no function.
- **The signature**: an input, the literals `bool`, `nat` and `unit`, the Boolean words `not`,
  `and`, `or` and `ite`, the numeric words `add`, `sub`, `lt`, `eq` and `isZero`, the product
  words `pair`, `tuple2`, `fst` and `snd`, `some`, a field's read `get` and overwrite `set`, and
  the list words `emptyLike`, `len`, `snoc`, `append`, `take`, `drop` and `head`. `pair` and
  `tuple2` answer one value, and differ in their atom and in their typing rule.
- **The algebra and its fold** (`StepAlgebra`, `Step.cata`): one field per constructor, and the
  one map out of the syntax. Every interpretation below is an algebra. The two are written by
  hand: the fold generator (`tools/Effect4Gen/Fold.lean`) writes the algebras of the free objects,
  and its support of a family indexed by `Ty`, like `Step Γ t`, is not established. `Step.cata`
  is the one hand recursion over a step.

The arrows out of a step, each a fold:

| Arrow | Kind | Answers |
| --- | --- | --- |
| `Step.term` | translation | the source term, with the builder words of `src/Effect4/Modules/Words.lean` |
| `Step.eval` | denotation | the value on the carriers of an identity context (`Schema.Model.CarrierAt`) |
| `Step.writes` | footprint | the names of the fields that its overwrites name |
| `Step.spine` | footprint | the input whose record it updates, when it is an update spine |
| `Step.canonical` | check | whether each record it reads or writes has ascending names |
| `Step.normal` | check | whether each type where the checker needs a normal form is certified to have one |
| `Step.Facts` | proposition | the normal forms that the checker needs, as facts a caller may prove |

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
inductive Step : List Ty → Ty → Type where
  | var {Γ : List Ty} {t : Ty} : Input Γ t → Step Γ t
  | bool {Γ : List Ty} (b : Bool) : Step Γ .bool
  | nat {Γ : List Ty} (n : Nat) : Step Γ .nat
  | unit {Γ : List Ty} : Step Γ .unit
  | not {Γ : List Ty} : Step Γ .bool → Step Γ .bool
  | and {Γ : List Ty} : Step Γ .bool → Step Γ .bool → Step Γ .bool
  | or {Γ : List Ty} : Step Γ .bool → Step Γ .bool → Step Γ .bool
  | ite {Γ : List Ty} {t : Ty} : Step Γ .bool → Step Γ t → Step Γ t → Step Γ t
  | add {Γ : List Ty} : Step Γ .nat → Step Γ .nat → Step Γ .nat
  | sub {Γ : List Ty} : Step Γ .nat → Step Γ .nat → Step Γ .nat
  | lt {Γ : List Ty} : Step Γ .nat → Step Γ .nat → Step Γ .bool
  | eq {Γ : List Ty} : Step Γ .nat → Step Γ .nat → Step Γ .bool
  | isZero {Γ : List Ty} : Step Γ .nat → Step Γ .bool
  | pair {Γ : List Ty} {a b : Ty} : Step Γ a → Step Γ b → Step Γ (.prod a b)
  | tuple2 {Γ : List Ty} {a b : Ty} : Step Γ a → Step Γ b → Step Γ (.prod a b)
  | fst {Γ : List Ty} {a b : Ty} : Step Γ (.prod a b) → Step Γ a
  | snd {Γ : List Ty} {a b : Ty} : Step Γ (.prod a b) → Step Γ b
  | some {Γ : List Ty} {t : Ty} : Step Γ t → Step Γ (.option t)
  | get {Γ : List Ty} {fs : List (String × Bool × Ty)} {t : Ty} : Step Γ (.record fs) → FieldRef fs t → Step Γ t
  | set {Γ : List Ty} {fs : List (String × Bool × Ty)} {t : Ty} :
      Step Γ (.record fs) → FieldRef fs t → Step Γ t → Step Γ (.record fs)
  | emptyLike {Γ : List Ty} {t : Ty} : Step Γ (.list t) → Step Γ (.list t)
  | len {Γ : List Ty} {t : Ty} : Step Γ (.list t) → Step Γ .nat
  | snoc {Γ : List Ty} {t : Ty} : Step Γ (.list t) → Step Γ t → Step Γ (.list t)
  | append {Γ : List Ty} {t : Ty} : Step Γ (.list t) → Step Γ (.list t) → Step Γ (.list t)
  | take {Γ : List Ty} {t : Ty} : Step Γ (.list t) → Step Γ .nat → Step Γ (.list t)
  | drop {Γ : List Ty} {t : Ty} : Step Γ (.list t) → Step Γ .nat → Step Γ (.list t)
  | head {Γ : List Ty} {t : Ty} : Step Γ (.list t) → Step Γ (.option t)
  | fold {Γ : List Ty} {acc item : Ty} : Step Γ (.list item) → Step Γ acc →
      Step (acc :: item :: Γ) acc → Step Γ acc

/-- **The step algebra**: a carrier at each type, and one field per constructor. -/
structure StepAlgebra (R : List Ty → Ty → Type) where
  var : {Γ : List Ty} → {t : Ty} → Input Γ t → R Γ t
  bool : {Γ : List Ty} → Bool → R Γ .bool
  nat : {Γ : List Ty} → Nat → R Γ .nat
  unit : {Γ : List Ty} → R Γ .unit
  not : {Γ : List Ty} → R Γ .bool → R Γ .bool
  and : {Γ : List Ty} → R Γ .bool → R Γ .bool → R Γ .bool
  or : {Γ : List Ty} → R Γ .bool → R Γ .bool → R Γ .bool
  ite : {Γ : List Ty} → {t : Ty} → R Γ .bool → R Γ t → R Γ t → R Γ t
  add : {Γ : List Ty} → R Γ .nat → R Γ .nat → R Γ .nat
  sub : {Γ : List Ty} → R Γ .nat → R Γ .nat → R Γ .nat
  lt : {Γ : List Ty} → R Γ .nat → R Γ .nat → R Γ .bool
  eq : {Γ : List Ty} → R Γ .nat → R Γ .nat → R Γ .bool
  isZero : {Γ : List Ty} → R Γ .nat → R Γ .bool
  pair : {Γ : List Ty} → {a b : Ty} → R Γ a → R Γ b → R Γ (.prod a b)
  tuple2 : {Γ : List Ty} → {a b : Ty} → R Γ a → R Γ b → R Γ (.prod a b)
  fst : {Γ : List Ty} → {a b : Ty} → R Γ (.prod a b) → R Γ a
  snd : {Γ : List Ty} → {a b : Ty} → R Γ (.prod a b) → R Γ b
  some : {Γ : List Ty} → {t : Ty} → R Γ t → R Γ (.option t)
  get : {Γ : List Ty} → {fs : List (String × Bool × Ty)} → {t : Ty} → R Γ (.record fs) → FieldRef fs t → R Γ t
  set : {Γ : List Ty} → {fs : List (String × Bool × Ty)} → {t : Ty} → R Γ (.record fs) → FieldRef fs t → R Γ t →
    R Γ (.record fs)
  emptyLike : {Γ : List Ty} → {t : Ty} → R Γ (.list t) → R Γ (.list t)
  len : {Γ : List Ty} → {t : Ty} → R Γ (.list t) → R Γ .nat
  snoc : {Γ : List Ty} → {t : Ty} → R Γ (.list t) → R Γ t → R Γ (.list t)
  append : {Γ : List Ty} → {t : Ty} → R Γ (.list t) → R Γ (.list t) → R Γ (.list t)
  take : {Γ : List Ty} → {t : Ty} → R Γ (.list t) → R Γ .nat → R Γ (.list t)
  drop : {Γ : List Ty} → {t : Ty} → R Γ (.list t) → R Γ .nat → R Γ (.list t)
  head : {Γ : List Ty} → {t : Ty} → R Γ (.list t) → R Γ (.option t)

  fold : {Γ : List Ty} → {acc item : Ty} → R Γ (.list item) → R Γ acc →
    R (acc :: item :: Γ) acc → R Γ acc

namespace Step

variable {Γ : List Ty}

/-- **The fold**: the one map out of the syntax into an algebra. -/
def cata {R : List Ty → Ty → Type} (alg : StepAlgebra R) : {Γ : List Ty} → {t : Ty} → Step Γ t → R Γ t
  | _, _, .var x => alg.var x
  | _, _, .bool b => alg.bool b
  | _, _, .nat n => alg.nat n
  | _, _, .unit => alg.unit
  | _, _, .not a => alg.not (cata alg a)
  | _, _, .and a b => alg.and (cata alg a) (cata alg b)
  | _, _, .or a b => alg.or (cata alg a) (cata alg b)
  | _, _, .ite c a b => alg.ite (cata alg c) (cata alg a) (cata alg b)
  | _, _, .add a b => alg.add (cata alg a) (cata alg b)
  | _, _, .sub a b => alg.sub (cata alg a) (cata alg b)
  | _, _, .lt a b => alg.lt (cata alg a) (cata alg b)
  | _, _, .eq a b => alg.eq (cata alg a) (cata alg b)
  | _, _, .isZero a => alg.isZero (cata alg a)
  | _, _, .pair a b => alg.pair (cata alg a) (cata alg b)
  | _, _, .tuple2 a b => alg.tuple2 (cata alg a) (cata alg b)
  | _, _, .fst p => alg.fst (cata alg p)
  | _, _, .snd p => alg.snd (cata alg p)
  | _, _, .some a => alg.some (cata alg a)
  | _, _, .get r f => alg.get (cata alg r) f
  | _, _, .set r f v => alg.set (cata alg r) f (cata alg v)
  | _, _, .emptyLike xs => alg.emptyLike (cata alg xs)
  | _, _, .len xs => alg.len (cata alg xs)
  | _, _, .snoc xs x => alg.snoc (cata alg xs) (cata alg x)
  | _, _, .append xs ys => alg.append (cata alg xs) (cata alg ys)
  | _, _, .take xs n => alg.take (cata alg xs) (cata alg n)
  | _, _, .drop xs n => alg.drop (cata alg xs) (cata alg n)
  | _, _, .head xs => alg.head (cata alg xs)
  | _, _, .fold xs init body => alg.fold (cata alg xs) (cata alg init) (cata alg body)

/-! ## The translation into source terms -/

/-- A term input resolved at the original scope, lifted past two fold slots. -/
def capturedSource (src : TermSrc) (env : Env) (path : List Nat) : TermSrc :=
  fun _ _ => do
    let t ← src env path
    .ok (Term.weaken (env.names.length + 1) (Term.weaken env.names.length t))

/-- The fold body's inputs: its two binder slots and frozen outer inputs. -/
def foldSources {Γ : List Ty} {acc item : Ty}
    (src : {t : Ty} → Input Γ t → TermSrc) (env : Env) (path : List Nat) :
    {t : Ty} → Input (acc :: item :: Γ) t → TermSrc
  | _, .here _ _ => fun _ _ => .ok (.var env.names.length)
  | _, .there _ (.here _ _) => fun _ _ => .ok (.var (env.names.length + 1))
  | _, .there _ (.there _ x) => capturedSource (src x) env path

/-- The term algebra; a fold captures used outer sources at their original scope. -/
def termAlg : StepAlgebra (fun Γ _ => ({t : Ty} → Input Γ t → TermSrc) → TermSrc) where
  var x := fun src => src x
  bool b := fun _ => Authoring.bool b
  nat n := fun _ => Authoring.nat n
  unit := fun _ => Authoring.unit
  not a := fun src => notT (a src)
  and a b := fun src => andT (a src) (b src)
  or a b := fun src => orT (a src) (b src)
  ite c a b := fun src => ifT (c src) (a src) (b src)
  get r f := fun src => field (r src) f.name
  set r f v := fun src => recordSet (r src) f.name (v src)
  emptyLike xs := fun src => noneOf (xs src)
  len xs := fun src => Modules.len (xs src)
  snoc xs x := fun src => Modules.snoc (xs src) (x src)
  head xs := fun src => app "get" [xs src, Authoring.nat 0]
  tuple2 a b := fun src => tuple [a src, b src]
  add a b := fun src => app "add" [a src, b src]
  sub a b := fun src => app "sub" [a src, b src]
  lt a b := fun src => app "lt" [a src, b src]
  eq a b := fun src => app "eq" [a src, b src]
  pair a b := fun src => app "pair" [a src, b src]
  append a b := fun src => app "append" [a src, b src]
  take a b := fun src => app "take" [a src, b src]
  drop a b := fun src => app "drop" [a src, b src]
  isZero a := fun src => app "isZero" [a src]
  fst a := fun src => app "fst" [a src]
  snd a := fun src => app "snd" [a src]
  some a := fun src => app "some" [a src]
  fold xs init body := fun src env path => do
    let l ← xs src env path
    let i ← init src env path
    let b ← body (foldSources src env path)
      (env.push [env.mint "acc", env.mint "item"]) path
    .ok (.fold none l i b)

/-- The source term; fold bodies never re-resolve a caller source at their extended scope. -/
def term (src : {t : Ty} → Input Γ t → TermSrc) {t : Ty} (e : Step Γ t) : TermSrc :=
  cata termAlg e src

/-! ## The denotation on carriers -/

/-- The value algebra at an identity context and the inputs' values. -/
def evalAlg (L : Leaves) : StepAlgebra (fun Γ t => Inputs L Γ → CarrierAt L t) where
  var x := fun vs => x.get vs
  bool b := fun _ => b
  nat n := fun _ => n
  unit := fun _ => ()
  not a := fun vs => !(a vs)
  and a b := fun vs => a vs && b vs
  or a b := fun vs => a vs || b vs
  ite c a b := fun vs => (fun (test : Bool) x y => if test then x else y) (c vs) (a vs) (b vs)
  add a b := fun vs => (fun (x y : Nat) => x + y) (a vs) (b vs)
  sub a b := fun vs => (fun (x y : Nat) => x - y) (a vs) (b vs)
  lt a b := fun vs => (fun (x y : Nat) => decide (x < y)) (a vs) (b vs)
  eq a b := fun vs => (fun (x y : Nat) => decide (x = y)) (a vs) (b vs)
  isZero a := fun vs => (fun (x : Nat) => decide (x = 0)) (a vs)
  pair a b := fun vs => (a vs, b vs)
  tuple2 a b := fun vs => (a vs, b vs)
  fst p := fun vs => (p vs).1
  snd p := fun vs => (p vs).2
  some a := fun vs => Option.some (a vs)
  get r f := fun vs => f.get (r vs)
  set r f v := fun vs => f.set (r vs) (v vs)
  emptyLike _ := fun _ => []
  len xs := fun vs => (xs vs).length
  snoc {_Γ} {t} xs x := fun vs => (fun (l : List (CarrierAt L t)) x => l ++ [x]) (xs vs) (x vs)
  append {_Γ} {t} xs ys := fun vs => (fun (l r : List (CarrierAt L t)) => l ++ r) (xs vs) (ys vs)
  take xs n := fun vs => (xs vs).take (n vs)
  drop xs n := fun vs => (xs vs).drop (n vs)
  head xs := fun vs => (xs vs).head?
  fold xs init body := fun vs => (xs vs).foldl (fun acc item => body (acc, (item, vs))) (init vs)

/-- The value at the identity context and the inputs. -/
def eval (L : Leaves) (vs : Inputs L Γ) {t : Ty} (e : Step Γ t) : CarrierAt L t :=
  cata (evalAlg L) e vs

/-! ## Footprints and checks -/

/-- The footprint algebra: the names that the overwrites name. -/
def writesAlg : StepAlgebra (fun _ _ => List String) where
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
  tuple2 a b := a ++ b
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
  fold xs init body := xs ++ init ++ body

/-- **The names of the fields that the step's overwrites name.** -/
def writes {t : Ty} (e : Step Γ t) : List String := cata writesAlg e

/-- The spine algebra: the position of the input whose record the step updates, or `none`. -/
def spineAlg : StepAlgebra (fun _ _ => Option Nat) where
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
  tuple2 _ _ := none
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
  fold _ _ _ := none

/-- **The update spine**: the input whose record the step answers, with some fields overwritten.
An input, a choice between two spines of one input, and an overwrite of a spine are spines. -/
def spine {t : Ty} (e : Step Γ t) : Option Nat := cata spineAlg e

/-- A check algebra: the conjunction of the children's checks, and a node's own test at a field's
read and overwrite. -/
def checkAlg (atRecord : List (String × Bool × Ty) → Bool) (atType : Ty → Bool) :
    StepAlgebra (fun _ _ => Bool) where
  var _ := true
  bool _ := true
  nat _ := true
  unit := true
  not a := a
  and a b := a && b
  or a b := a && b
  ite {_Γ} {t} c a b := atType t && (c && (a && b))
  add a b := a && b
  sub a b := a && b
  lt a b := a && b
  eq a b := a && b
  isZero a := a
  pair a b := a && b
  tuple2 {_Γ} {a b} x y := atType (.prod a b) && (x && y)
  fst p := p
  snd p := p
  some a := a
  get := fun {_Γ} {fs} {_} r _ => atRecord fs && r
  set := fun {_Γ} {fs} {_} r _ v => atRecord fs && (r && v)
  emptyLike xs := xs
  len xs := xs
  snoc {_Γ} {t} xs x := atType t && (xs && x)
  append {_Γ} {t} xs ys := atType t && (xs && ys)
  take xs n := xs && n
  drop xs n := xs && n
  head xs := xs
  fold xs init body := xs && init && body

/-- **The reading check**: each record that the step reads or writes has strictly ascending
names, so the machine's read and overwrite are the field's. -/
def canonical {t : Ty} (e : Step Γ t) : Bool :=
  cata (checkAlg (fun fs => decide (Field.Ascending Field.bytesKey fs)) (fun _ => true)) e

/-- **The typing check**: each record that the step reads or writes is certified to be its own
normal form, and so is the type of each selection and of each list it extends
(`Ty.certNormal`, `src/Effect4/Program/TyNormal.lean`). It reduces by evaluation. -/
def normal {t : Ty} (e : Step Γ t) : Bool :=
  cata (checkAlg (fun fs => (Ty.record fs).certNormal) (fun t => t.certNormal)) e

/-- The facts algebra: the normal forms that the checker's rules ask for, as propositions. A
selection and a list it extends ask for their type's normal form, a tuple for its two items' and
that neither is a union, and a field's read and overwrite for the record's. -/
def factsAlg : StepAlgebra (fun _ _ => Prop) where
  var _ := True
  bool _ := True
  nat _ := True
  unit := True
  not a := a
  and a b := a ∧ b
  or a b := a ∧ b
  ite {_Γ} {t} c a b := t.normalize = t ∧ c ∧ a ∧ b
  add a b := a ∧ b
  sub a b := a ∧ b
  lt a b := a ∧ b
  eq a b := a ∧ b
  isZero a := a
  pair a b := a ∧ b
  tuple2 {_Γ} {a b} x y :=
    (a.normalize = a ∧ b.normalize = b ∧ a.isFactor = true ∧ b.isFactor = true) ∧ x ∧ y
  fst p := p
  snd p := p
  some a := a
  get := fun {_Γ} {fs} {_} r _ => Ty.normalize (.record fs) = .record fs ∧ r
  set := fun {_Γ} {fs} {_} r _ v => Ty.normalize (.record fs) = .record fs ∧ r ∧ v
  emptyLike xs := xs
  len xs := xs
  snoc {_Γ} {t} xs x := t.normalize = t ∧ xs ∧ x
  append {_Γ} {t} xs ys := t.normalize = t ∧ xs ∧ ys
  take xs n := xs ∧ n
  drop xs n := xs ∧ n
  head xs := xs
  fold xs init body := xs ∧ init ∧ body

/-- **The typing facts**: the normal forms that the checker needs for the step, as one
proposition. The typing check (`normal`) proves them by evaluation; a caller proves them from
premises where a type is a parameter. -/
def Facts {t : Ty} (e : Step Γ t) : Prop := cata factsAlg e

end Step
end Effect4.Modules

namespace Effect4.Modules.Step
open Effect4.Program Effect4.Program.Authoring
/-- Whether a step needs binder slots in its caller's scope. -/
def bindsAlg : StepAlgebra (fun _ _ => Bool) where
  var _ := false
  bool _ := false
  nat _ := false
  unit := false
  not a := a
  and a b := a || b
  or a b := a || b
  ite  c a b := c || a || b
  add a b := a || b
  sub a b := a || b
  lt a b := a || b
  eq a b := a || b
  isZero a := a
  pair a b := a || b
  tuple2  x y := x || y
  fst p := p
  snd p := p
  some a := a
  get r _ := r
  set r _ v := r || v
  emptyLike xs := xs
  len xs := xs
  snoc  xs x := xs || x
  append  xs ys := xs || ys
  take xs n := xs || n
  drop xs n := xs || n
  head xs := xs
  fold _ _ _ := true

def binds {Γ : List Ty} {t : Ty} (e : Step Γ t) : Bool := cata bindsAlg e

/-- Scope alignment is required only for a step containing a fold. -/
def ScopeFacts {Γ : List Ty} {t : Ty} (e : Step Γ t) (env : Effect4.Program.Authoring.Env)
    (length : Nat) : Prop := if e.binds then length = env.names.length else True
end Effect4.Modules.Step
