import Effect4.Laws.Modules.Reading

/-!
Finite design-review controls only. No semantic theorem is stated.
Claim challenged: MODULES design section 6.1's frame property from Step.writes.
Placement: translation-simulation, proposed step-language-sound's metadata consequence.
Reach: arbitrary Enc and Field accepted by the proposed Step constructors; model state fields.
Not established: encoded-value Reads agreement is unchanged; typing and runs are outside scope.
Consumer: owner ruling before M1's first-order signature and M2's deriving contract are frozen.
-/

set_option autoImplicit false
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Store (Val)
namespace ModulesStepReview
class Enc (α : Type) where enc : α → Val
export Enc (enc)
instance encBool : Enc Bool := ⟨Val.bool⟩
instance encNat : Enc Nat := ⟨Val.nat⟩
instance encList {α : Type} [Enc α] : Enc (List α) := ⟨fun xs => Val.list (xs.map enc)⟩
instance encProd {α β : Type} [Enc α] [Enc β] : Enc (α × β) := ⟨fun p => Val.tuple [enc p.1, enc p.2]⟩

/-- A field of a record carrier: its spelling, its Lean view, and its two record lemmas. -/
structure Field (σ φ : Type) [Enc σ] [Enc φ] where
  name : String
  get : σ → φ
  set : σ → φ → σ
  read : ∀ x, Machine.Record.read false (enc x) name = some (enc (get x))
  write : ∀ x y, Machine.Record.set (enc x) name (enc y) = some (enc (set x y))

/-- A field found by its Lean name; a generator writes one instance per field. -/
class FieldOf (σ : Type) (n : String) (φ : outParam Type) [Enc σ] [Enc φ] where
  field : Field σ φ


def union (a b : List String) : List String := a ++ b.filter (!a.contains ·)
inductive Step (ι : Type) (ei : Enc ι) : (α : Type) → Enc α → Type 1 where
  | input : Step ι ei ι ei
  | bool : Bool → Step ι ei Bool encBool
  | ite {α : Type} {e : Enc α} : Step ι ei Bool encBool → Step ι ei α e → Step ι ei α e →
      Step ι ei α e
  | pair {α β : Type} {ea : Enc α} {eb : Enc β} : Step ι ei α ea → Step ι ei β eb →
      Step ι ei (α × β) (@encProd α β ea eb)
  | get {σ φ : Type} {es : Enc σ} {ef : Enc φ} : Step ι ei σ es → @Field σ φ es ef → Step ι ei φ ef
  | set {σ φ : Type} {es : Enc σ} {ef : Enc φ} : Step ι ei σ es → @Field σ φ es ef →
      Step ι ei φ ef → Step ι ei σ es
  | emptyLike {α : Type} {e : Enc α} : Step ι ei (List α) (@encList α e) →
      Step ι ei (List α) (@encList α e)

variable {ι : Type} {ei : Enc ι}

/-- The term: a fold. -/
def Step.term (src : TermSrc) : {α : Type} → {e : Enc α} → Step ι ei α e → TermSrc
  | _, _, .input => src
  | _, _, .bool b => Authoring.bool b
  | _, _, .ite c t f => ifT (c.term src) (t.term src) (f.term src)
  | _, _, .pair a b => app "pair" [a.term src, b.term src]
  | _, _, .get s f => field (s.term src) f.name
  | _, _, .set s f r => recordSet (s.term src) f.name (r.term src)
  | _, _, .emptyLike xs => noneOf (xs.term src)

/-- The model's function: a fold. -/
def Step.eval (v : ι) : {α : Type} → {e : Enc α} → Step ι ei α e → α
  | _, _, .input => v
  | _, _, .bool b => b
  | _, _, .ite c t f => if c.eval v then t.eval v else f.eval v
  | _, _, .pair a b => (a.eval v, b.eval v)
  | _, _, .get s f => f.get (s.eval v)
  | _, _, .set s f r => f.set (s.eval v) (r.eval v)
  | _, _, .emptyLike _ => []

/-- The fields a step writes: a fold. -/
def Step.writes : {α : Type} → {e : Enc α} → Step ι ei α e → List String
  | _, _, .input => []
  | _, _, .bool _ => []
  | _, _, .ite c t f => union c.writes (union t.writes f.writes)
  | _, _, .pair a b => union a.writes b.writes
  | _, _, .get s _ => s.writes
  | _, _, .set s f r => union (union s.writes r.writes) [f.name]
  | _, _, .emptyLike xs => xs.writes


structure Visible where
  flag : Bool
  count : Nat

-- Machine.Record.set canonicalizes by field-name bytes: count precedes flag.
instance : Enc Visible :=
  ⟨fun s => .ctor 0 [.list [.str "count", .str "flag"], .list [enc s.count, enc s.flag]]⟩

def visibleFlag : Field Visible Bool :=
  { name := "flag", get := (·.flag), set := fun s b => { s with flag := b },
    read := fun _ => rfl, write := fun _ _ => rfl }

def positive : Step Visible inferInstance Visible inferInstance :=
  .set .input visibleFlag (.bool false)

#guard positive.writes == ["flag"]
#guard (positive.eval ⟨true, 17⟩).count == 17

structure Hidden where
  flag : Bool
  secret : Bool

-- The proposed Enc admits loss of a model field.
instance : Enc Hidden :=
  ⟨fun s => .ctor 0 [.list [.str "flag"], .list [enc s.flag]]⟩

-- Both required descriptor laws hold, although the updater also changes secret.
def hiddenFlag : Field Hidden Bool :=
  { name := "flag", get := (·.flag),
    set := fun s b => { flag := b, secret := !s.secret },
    read := fun _ => rfl, write := fun _ _ => rfl }

def negative : Step Hidden inferInstance Hidden inferInstance :=
  .set .input hiddenFlag (.bool false)

#guard negative.writes == ["flag"]
#guard !negative.writes.contains "secret"
#guard (negative.eval ⟨true, false⟩).secret
#guard enc (Hidden.mk true false) == enc (Hidden.mk true true)

-- The same emitted term and footprint cannot distinguish these model update functions.
def ordinaryFlag : Field Hidden Bool :=
  { name := "flag", get := (·.flag), set := fun s b => { s with flag := b },
    read := fun _ => rfl, write := fun _ _ => rfl }

def ordinary : Step Hidden inferInstance Hidden inferInstance :=
  .set .input ordinaryFlag (.bool false)

#guard negative.writes == ordinary.writes
#guard (negative.term (var "state")) { names := ["state"] } [] ==
  (ordinary.term (var "state")) { names := ["state"] } []
#guard (negative.eval ⟨true, false⟩).secret != (ordinary.eval ⟨true, false⟩).secret

end ModulesStepReview
