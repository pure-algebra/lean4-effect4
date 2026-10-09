import Effect4.Laws.Step

/-! Captured fold controls for step-language-sound and step-language-typed:
nested captures, caller trees with binders, empty element carriers, unused sources and alignment. -/

set_option autoImplicit false
open Effect4.Program Effect4.Program.Authoring Effect4.Store Effect4.Schema Effect4.Schema.Model
open Effect4.Modules
namespace Test.Program.StepFolds

abbrev Γ : List Ty := [.list .nat, .nat]
def xs : Input Γ (.list .nat) := .here _ _
def number : Input Γ .nat := .there _ (.here _ _)
def acc : Input (.nat :: .nat :: Γ) .nat := .here _ _
def item : Input (.nat :: .nat :: Γ) .nat := .there _ (.here _ _)
def outerNumber : Input (.nat :: .nat :: Γ) .nat := .there _ (.there _ number)
def body : Step (.nat :: .nat :: Γ) .nat :=
  .add (.var acc) (.add (.var item) (.var outerNumber))
def sum : Step Γ .nat := .fold (.var xs) (.nat 0) body

def innerList : Input (.nat :: .nat :: Γ) (.list .nat) := .there _ (.there _ xs)
def innerAcc : Input (.nat :: .nat :: .nat :: .nat :: Γ) .nat := .here _ _
def innerItem : Input (.nat :: .nat :: .nat :: .nat :: Γ) .nat := .there _ (.here _ _)
def innerNumber : Input (.nat :: .nat :: .nat :: .nat :: Γ) .nat :=
  .there _ (.there _ outerNumber)
def nestedBody : Step (.nat :: .nat :: Γ) .nat :=
  .add (.var acc) (.fold (.var innerList) (.nat 0)
    (.add (.var innerAcc) (.add (.var innerItem) (.var innerNumber))))
def nested : Step Γ .nat := .fold (.var xs) (.nat 0) nestedBody

def scope : Env := { names := ["xs", "n"] }
def values : List Val := [.list [.nat 1, .nat 2], .nat 7]
def carrier : Inputs Leaves.opaque Γ := (([1, 2] : List Nat), ((7 : Nat), ()))
def listSource : TermSrc := fun _ _ => .ok (.var 0)
-- This source deliberately inspects the scope. The fold must freeze its original answer.
def inspecting : TermSrc := fun env path => nat (if env.names.length = 2 then 7 else 99) env path

def run {Δ : List Ty} {t : Ty} (e : Step Δ t) (srcs : List TermSrc)
    (env : Env) (vals : List Val) : Option Val :=
  match e.term (Input.source srcs) env [] with
  | .ok tree => evalTerm vals tree
  | .error _ => none

#guard sum.normal && nested.normal
#guard
  let first : Nat := sum.eval Leaves.opaque carrier
  let second : Nat := nested.eval Leaves.opaque carrier
  first == 17 && second == 34
#guard run sum [listSource, inspecting] scope values == some (.nat 17)
#guard run nested [listSource, inspecting] scope values == some (.nat 34)

-- A caller tree itself contains a fold. Its internal binder positions must move too.
def foldedSource : TermSrc := foldWith (Effect4.Modules.snoc (Effect4.Modules.snoc nilT (nat 1)) (nat 2))
  (nat 0) (fun a i => app "add" [app "add" [a, i], var "n"])
#guard run sum [listSource, foldedSource] scope values == some (.nat 37)
#guard run nested [listSource, foldedSource] scope values == some (.nat 74)

-- Reader of the shared law at concrete, inhabited inputs.
example : Reads (sum.term (Input.source [listSource, inspecting])) scope [] values (.nat 17) := by
  have inputs : ∀ {t : Ty} (x : Input Γ t),
      Reads (Input.source [listSource, inspecting] x) scope [] values
        ((imageAt Leaves.opaque t).toVal (x.get carrier)) := by
    intro t x
    cases x with
    | here => exact ⟨_, rfl, rfl⟩
    | there _ x =>
      cases x with
      | here => exact ⟨_, rfl, rfl⟩
      | there _ x => nomatch x
  exact Step.sound Leaves.opaque carrier inputs sum rfl rfl

-- The scoped law cannot apply to a value environment longer than its names.
#guard sum.binds && scope.names.length != 3
example : ¬sum.ScopeFacts scope 3 := by
  intro h
  change 3 = 2 at h
  contradiction
#guard run sum [listSource, inspecting] scope (values ++ [.nat 100]) == some (.nat 214)

-- Empty is the carrier of the unsupported int leaf, yet an empty list has a body tree.
def emptyFold : Step [.list .int] .nat :=
  .fold (.var (.here _ _)) (.nat 3) (.var (.here _ _))
#guard run emptyFold [listSource] { names := ["empty"] } [.list []] == some (.nat 3)
example : Reads (emptyFold.term (Input.source [listSource])) { names := ["empty"] } []
    [.list []] (.nat 3) := by
  have inputs : ∀ {t : Ty} (x : Input [.list .int] t),
      Reads (Input.source [listSource] x) { names := ["empty"] } [] [.list []]
        ((imageAt Leaves.opaque t).toVal (x.get (([], ()) : Inputs Leaves.opaque [.list .int]))) := by
    intro t x
    cases x with
    | here => exact ⟨_, rfl, rfl⟩
    | there _ x => nomatch x
  exact Step.sound (Γ := [.list .int]) Leaves.opaque (([], ()) : Inputs Leaves.opaque [.list .int])
    inputs emptyFold rfl rfl

-- The corresponding typing reader has no inhabitance premise.
example {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {src : {t : Ty} → Input [.list .int] t → TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (depth : types.length = env.names.length)
    (inputs : ∀ {t : Ty} (x : Input [.list .int] t), TypesEach sig (src x) env path types t) :
    TypesEach sig (emptyFold.term src) env path types .nat :=
  Step.typed_of_normal sig atoms inputs emptyFold rfl depth

-- An unused caller source can refuse; translation never asks it for a tree.
def unusedFold : Step [.list .nat, .unit] .nat :=
  .fold (.var (.here _ _)) (.nat 3) (.var (.here _ _))
def failing : TermSrc := fun _ path => .error ⟨path, .unbound "unused"⟩
#guard run unusedFold [listSource, failing] { names := ["xs"] } [.list [.nat 1]] == some (.nat 3)
end Test.Program.StepFolds
