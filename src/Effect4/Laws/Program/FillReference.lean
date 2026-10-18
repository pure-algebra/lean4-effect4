import Effect4.Program.Typing.FillSet
import Effect4.Laws.Program.Typing.Sound
/-!
Reference observations for the retired raw certification and materialization algorithms.
These definitions retain their old bodies and refusal order for D1-D9's fragment proofs.
They are Laws-only observations. The production feed owns certification and publication.
-/
namespace Effect4.Program.FillReference
open Effect4 Effect4.Program
open Conform.Effect4.Typing (HasTy)
def certifiedB (s : Sketch) (app : SigApp) (p : List Nat) (q : NativeEff) : Bool :=
  !p.isEmpty &&
  match s.focusAt app p with
  | none => false
  | some f => decide (Checker.check (s.sigAt app p) f.env p q = .ok f.ty)

/-- Why a fill set does not materialize. -/
inductive MaterializeRefusal where
  /-- two different fillings at this address -/
  | conflict (path : List Nat)
  /-- a fill names the root, which an ordinary document commit replaces -/
  | root
  /-- a fill names an address at which the base holds no program -/
  | unknownAddress
  /-- the fills do not apply in the base's address order -/
  | notApplicable
  /-- the result does not check through its references -/
  | refused (why : TypeRefusal)
  /-- the document is another one than the set was opened at -/
  | foreignDoc (expected actual : DocId)
  /-- the document has moved past the revision the set was opened at -/
  | staleRevision (expected actual : Nat)
  /-- the document at the set's identity and revision holds another base or application -/
  | foreignBase
deriving DecidableEq

/-- The first address with two different fillings. -/
def conflictAt (fs : List (List Nat × NativeEff)) : Option (List Nat) :=
  (fs.find? fun x => fs.any fun y => decide (y.1 = x.1) && decide (y.2 ≠ x.2)).map (·.1)

/-- **Materialize**: refuse a root fill, a fill where the base holds no program, and a conflict;
apply the fills in the base's address order, and check the result through its references. -/
def materialize (app : SigApp) (base : Sketch) (fs : List (List Nat × NativeEff)) :
    Except MaterializeRefusal Sketch :=
  match fs.any (fun x => x.1.isEmpty), fs.any (fun x => !holdsProgram base x.1) with
  | true, _ => .error .root
  | false, true => .error .unknownAddress
  | false, false =>
    match conflictAt fs with
    | some p => .error (.conflict p)
    | none =>
      match applyFills base (ordered base fs) with
      | none => .error .notApplicable
      | some s' =>
        match s'.sourceCheck app with
        | .ok _ => .ok s'
        | .error why => .error (.refused why)

/-- A fill certified against a sketch: below the root, at a focus that the sketch answers, typed
at the focus's type in its environment at the address's signature. -/
def Certified (s : Sketch) (app : SigApp) (x : List Nat × NativeEff) : Prop :=
  x.1 ≠ [] ∧ ∃ f, s.focusAt app x.1 = some f ∧ HasTy (s.sigAt app x.1) f.env x.2 f.ty


end Effect4.Program.FillReference
