import Effect4.Program.Typing.SourceDocument

/-!
# Program.Typing.FillSet — pending fills against one document snapshot, published as one commit

**The question.** An agent fills several holes of one program independently, then publishes them
at once. Each filling is certified when it is added, against the snapshot the set was opened at.
Publication changes the document only through `Doc.step`, so the document has one owner.

## The face

| Operation | It takes | It answers |
| --- | --- | --- |
| `FillSet.open_` | a sealed document | an empty set anchored at the document's snapshot and session |
| `FillSet.add` | an oracle, a set and submissions | the next set and one outcome per submission |
| `FillSet.pending` | a set | its fillings in the base's address order |
| `FillSet.publication` | a set | one `commit` of kept-exact items, or `empty` |

A set is built only by `open_` and `add`: its proof field is an uncached submission fold
(`FillSet.constructed`). Each submission is refused at the root, at an address with no program, at a
conflicting or overlapping address, or where the anchor's `keepExact` feed refuses it. The feed's
next session is discarded: certification checks, and nothing is applied until publication.

The tool steps the publication at the anchor's snapshot, so a moved document refuses `stale`. The
laws are in `Laws/Program/FillSet.lean`; the old certification and materialization stay as their
reference in `Laws/Program/FillReference.lean`.
-/

deriving instance DecidableEq for Effect4.Program.Sketch
set_option autoImplicit false
namespace Effect4.Program
open Effect4 Check
/-- Two addresses are incomparable when neither is in the subtree of the other. -/
def Incomparable (a b : List Nat) : Prop :=
  Table.under a b = false ∧ Table.under b a = false

/-- Decidable check for `Incomparable a b`. -/
def incomparableB (a b : List Nat) : Bool :=
  !Table.under a b && !Table.under b a

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

/-- Why a single fill submission is refused by `FillSet.add`. -/
inductive AddRefusal where
  /-- The address is the root `[]`: root replacement stays an ordinary document commit. -/
  | root
  /-- The address does not name a program node in the base sketch. -/
  | unknownAddress
  /-- The anchor's `keepExact` feed refuses the filling. -/
  | notCertified
  /-- Another filling is already recorded at this address. -/
  | conflict
  /-- The address is an ancestor or descendant of an address `existing` already in the set. -/
  | overlap (existing : List Nat)
deriving DecidableEq, Repr

/-- The outcome for one submitted fill in `FillSet.add`. -/
inductive AddOutcome where
  /-- the filling is certified and recorded -/
  | applied (path : List Nat)
  /-- the same filling is already recorded at the address -/
  | collapsed (path : List Nat)
  /-- the submission is refused at its address -/
  | refused (path : List Nat) (why : AddRefusal)
deriving DecidableEq, Repr


namespace FillSetInternal
/-- Placement: R14, initial-algebras-folds; helper of kept_eq_certified.
The anchor feed certifies candidates; this establishes no admission or progress claim. -/
def addEntry (o : Oracle) (anchor : SourceSession) (entries : List (List Nat × NativeEff))
    (p : List Nat) (q : NativeEff) : Checked (List (List Nat × NativeEff) × AddOutcome) := do
  if p.isEmpty then return (entries, .refused p .root)
  if !holdsProgram anchor.sketch p then return (entries, .refused p .unknownAddress)
  match entries.find? (fun x => decide (x.1 = p)) with
  | some (_, q0) =>
    if q0 = q then return (entries, .collapsed p)
    else return (entries, .refused p .conflict)
  | none =>
    match entries.find? (fun x => !incomparableB p x.1) with
    | some (other, _) => return (entries, .refused p (.overlap other))
    | none =>
      match ← anchor.feed o .keepExact (.fill p q) with
      | .error _ => return (entries, .refused p .notCertified)
      | .ok _ => return ((p,q) :: entries, .applied p)

/-- **The uncached submission fold**: the entries a list of submissions leaves, from none. It is
the witness of `FillSet.constructed`. -/
def addRaw (anchor : SourceSession) (submissions : List (List Nat × NativeEff)) :
    List (List Nat × NativeEff) :=
  submissions.foldl (fun entries x => (addEntry Oracle.uncached anchor entries x.1 x.2).value.1) []
end FillSetInternal

/-- Sealed pending fills, certified at the opened document's source session. -/
structure FillSet where
  private mk ::
  anchor : Snap
  source : SourceSession
  entries : List (List Nat × NativeEff)
  constructed : ∃ submissions, FillSetInternal.addRaw source submissions = entries

/-- **Why a set does not publish.** -/
inductive PublishRefusal where
  /-- the set holds no filling -/
  | empty

namespace FillSet

/-- **Open** an empty set at a document's snapshot and session. -/
def open_ (d : Doc) : FillSet := ⟨d.snap, d.session, [], ⟨[], rfl⟩⟩

/-- The base sketch: the anchor session's. -/
def base (fs : FillSet) : Sketch := fs.source.sketch
/-- The application: the anchor session's. -/
def app (fs : FillSet) : SigApp := fs.source.app
/-- **The pending fillings**, in the base's address order. -/
def pending (fs : FillSet) : List (List Nat × NativeEff) := ordered fs.base fs.entries

/-- Placement: R14, initial-algebras-folds; add_wf's constructor helper.
Every witness extends an uncached submission fold. This proves no host behavior. -/
def addOne (o : Oracle) (fs : FillSet) (p : List Nat) (q : NativeEff) :
    Checked (FillSet × AddOutcome) :=
  let c := FillSetInternal.addEntry o fs.source fs.entries p q
  let next : FillSet := ⟨fs.anchor, fs.source, c.value.1, by
    obtain ⟨submissions, hs⟩ := fs.constructed
    refine ⟨submissions ++ [(p,q)], ?_⟩
    simp only [FillSetInternal.addRaw, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (FillSetInternal.addEntry Oracle.uncached fs.source
      (FillSetInternal.addRaw fs.source submissions) p q).value.1 = _
    rw [hs]
    dsimp only [c]
    rw [Oracle.eq_uncached o]⟩
  c.bind' fun _ => pure (next, c.value.2)

/-- **Add submissions** in order, each through `addOne`: the next set and one outcome each. -/
def add (o : Oracle) (fs : FillSet) : List (List Nat × NativeEff) →
    Checked (FillSet × List AddOutcome)
  | [] => pure (fs, [])
  | (p,q) :: rest => do
    let (next, outcome) ← fs.addOne o p q
    let (last, outcomes) ← next.add o rest
    pure (last, outcome :: outcomes)

/-- **The publication**: one kept-exact `commit` of the pending fillings, each at its address with
the base's sub-program there as its expected program. -/
def publication (fs : FillSet) : Except PublishRefusal DocAction := do
  if fs.entries.isEmpty then throw .empty
  let items := fs.pending.filterMap fun (p,q) =>
    match (Node.eff fs.base.program).at_ p with
    | some (.eff expected) => some (Place.at_ p expected, Change.fill q)
    | _ => none
  pure (.commit items .keepExact)
end FillSet

end Effect4.Program
