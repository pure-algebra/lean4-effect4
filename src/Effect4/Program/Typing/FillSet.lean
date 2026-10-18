import Effect4.Program.Typing.SourceDocument
import Effect4.Program.Typing.CheckCache

/-!
# Program.Typing.FillSet — fixed-base parallel fills and deterministic materialization

Slice D of `docs/research/2026-10-17-proof-scout/README.md` (§7.4).

* `Incomparable`, `incomparableB`, `certifiedB`: address incomparability and base focus certification.
* `AddRefusal`, `AddOutcome`, `FillSet`, `FillSet.empty`, `FillSet.ofDoc`, `FillSet.view`,
  `FillSet.addOne`, `FillSet.add`: a set of fills against a fixed base sketch and application,
  populated only through `FillSet.add` (F1). Each submitted fill is either applied, collapsed (if an
  identical filling is already present), or refused at its address (`root`, `unknownAddress`,
  `notCertified`, `conflict`, or `overlap`).
* `applyFills`, `lookup`, `uniq`, `ordered`, `holdsProgram`, `conflictAt`, `MaterializeRefusal`,
  `materialize`: deterministic materialization in the base's address order, followed by the source
  check through layer references (`Sketch.sourceCheck`). `materialize` refuses a root fill and a fill
  at an address where the base holds no program, so a list that bypasses `FillSet.add` loses no fill
  in silence. Its refusals there carry no address: the answer depends on the fills' members only.
* `FillSet.materializeSketch`, `FillSet.materializeDoc`: a set's materialization, at its own base;
  `materializeDoc` publishes it only on the document, revision, base and application it was opened
  at.

The laws (D1–D9 and the construction invariant `FillSet.add_wf`) are in
`Effect4.Laws.Program.FillSet`.
-/

set_option autoImplicit false

deriving instance DecidableEq for Effect4.Program.Sketch

namespace Effect4.Program

open Effect4

/-! ## Address incomparability and base certification -/

/-- Two addresses are incomparable when neither is in the subtree of the other. -/
def Incomparable (a b : List Nat) : Prop :=
  Table.under a b = false ∧ Table.under b a = false

/-- Decidable check for `Incomparable a b`. -/
def incomparableB (a b : List Nat) : Bool :=
  !Table.under a b && !Table.under b a

/-- Decidable check that a fill `(p, q)` is below the root, targets a focus that `s.focusAt app p`
answers, and types at the focus's exact type (`f.ty`) in `f.env` at `s.sigAt app p`. -/
def certifiedB (s : Sketch) (app : SigApp) (p : List Nat) (q : NativeEff) : Bool :=
  !p.isEmpty &&
  match s.focusAt app p with
  | none => false
  | some f => decide (Checker.check (s.sigAt app p) f.env p q = .ok f.ty)

/-! ## Applying fills, address-ordered set view, and materialization -/

/-- Apply fills in order. -/
def applyFills (s : Sketch) : List (List Nat × NativeEff) → Option Sketch
  | [] => some s
  | (p, q) :: rest => (s.fillAt p q).bind fun s' => applyFills s' rest

/-- The filling a set of fills gives an address: the first member at the address. -/
def lookup (fs : List (List Nat × NativeEff)) (a : List Nat) : Option NativeEff :=
  (fs.find? fun x => decide (x.1 = a)).map (·.2)

/-- A list of addresses with each address once, the last occurrence kept. -/
def uniq : List (List Nat) → List (List Nat)
  | [] => []
  | a :: l => if a ∈ l then uniq l else a :: uniq l

/-- The fills of a set, in the base's address order, each address once. -/
def ordered (base : Sketch) (fs : List (List Nat × NativeEff)) : List (List Nat × NativeEff) :=
  (uniq (Node.addresses (.eff base.program))).filterMap fun a => (lookup fs a).map fun q => (a, q)

/-- Whether the base holds a program at an address: the addresses `FillSet.add` admits, the root
aside. -/
def holdsProgram (base : Sketch) (p : List Nat) : Bool :=
  match (Node.eff base.program).at_ p with
  | some (.eff _) => true
  | _ => false

/-- Why a fill set does not materialize. -/
inductive MaterializeRefusal where
  /-- two different fillings at this address -/
  | conflict (path : List Nat)
  /-- a fill names the root, which an ordinary `Doc.commit` replaces -/
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

/-! ## `FillSet`: constructor-guarded fixed-base fill set (F1) -/

/-- Why a single fill submission is refused by `FillSet.add`. -/
inductive AddRefusal where
  /-- The address is the root `[]` (root replacement stays an ordinary `Doc.commit`). -/
  | root
  /-- The address does not name a program node in the base sketch. -/
  | unknownAddress
  /-- The fill does not type at the base focus's exact type (`keepExactType`). -/
  | notCertified
  /-- Another filling is already recorded at this address. -/
  | conflict
  /-- The address is an ancestor or descendant of an address `existing` already in the set. -/
  | overlap (existing : List Nat)
deriving DecidableEq, Repr

/-- The outcome for one submitted fill in `FillSet.add`. -/
inductive AddOutcome where
  | applied (path : List Nat)
  | collapsed (path : List Nat)
  | refused (path : List Nat) (why : AddRefusal)
deriving DecidableEq, Repr

/-- A fixed-base set of certified, conflict-free, pairwise-incomparable fills. Its constructor is
private so every `FillSet` is built from `FillSet.empty` (or `FillSet.ofDoc`) via `FillSet.add`. -/
structure FillSet where
  private mk ::
  app : SigApp
  base : Sketch
  doc : DocId
  revision : Nat
  entries : List (List Nat × NativeEff)
deriving DecidableEq

namespace FillSet

/-- An empty `FillSet` for `app` and `base`, optionally tagged with a document identity and revision. -/
def empty (app : SigApp) (base : Sketch) (doc : DocId := ⟨"", 0⟩) (revision : Nat := 0) : FillSet :=
  ⟨app, base, doc, revision, []⟩

/-- An empty `FillSet` anchored to a `Doc` at its current revision. -/
def ofDoc (d : Doc) : FillSet :=
  empty d.session.app d.session.sketch d.id d.revision

/-- The fills in the set, in the base's address order. -/
def view (fs : FillSet) : List (List Nat × NativeEff) :=
  ordered fs.base fs.entries

/-- Submit one fill `(p, q)` to `fs`. -/
def addOne (fs : FillSet) (p : List Nat) (q : NativeEff) : FillSet × AddOutcome :=
  if p.isEmpty then
    (fs, .refused p .root)
  else
    match (Node.eff fs.base.program).at_ p with
    | some (.eff _) =>
      match fs.entries.find? (fun x => decide (x.1 = p)) with
      | some (_, q0) =>
        if decide (q0 = q) then
          (fs, .collapsed p)
        else
          (fs, .refused p .conflict)
      | none =>
        match fs.entries.find? (fun x => !incomparableB p x.1) with
        | some (other, _) =>
          (fs, .refused p (.overlap other))
        | none =>
          if certifiedB fs.base fs.app p q then
            ({ fs with entries := (p, q) :: fs.entries }, .applied p)
          else
            (fs, .refused p .notCertified)
    | _ =>
      (fs, .refused p .unknownAddress)

/-- Submit a batch of fills to `fs` in order, returning the updated `FillSet` and the outcome of each
submitted fill. -/
def add (fs : FillSet) : List (List Nat × NativeEff) → FillSet × List AddOutcome
  | [] => (fs, [])
  | (p, q) :: rest =>
    let (fs1, out1) := fs.addOne p q
    let (fs2, outs) := fs1.add rest
    (fs2, out1 :: outs)

/-- Materialize `fs` into a new `Sketch` via `Program.materialize`, at the set's own base. -/
def materializeSketch (fs : FillSet) : Except MaterializeRefusal Sketch :=
  Program.materialize fs.app fs.base fs.entries

/-- Materialize `fs` against `d` as a new document revision. It verifies that `d` is the document,
the revision, the base and the application the set was opened at, materializes the set at its own
base (`materializeSketch`), and advances the document revision by one. -/
def materializeDoc (fs : FillSet) (d : Doc) : Except MaterializeRefusal Doc :=
  if d.id != fs.doc then
    .error (.foreignDoc fs.doc d.id)
  else if d.revision != fs.revision then
    .error (.staleRevision fs.revision d.revision)
  else if d.session.sketch != fs.base || d.session.app != fs.app then
    .error .foreignBase
  else do
    let s' ← fs.materializeSketch
    .ok ⟨d.id, SourceSession.open fs.app s', d.revision + 1⟩

end FillSet

end Effect4.Program
