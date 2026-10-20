module

public import Effect4.Program.Profile
public import Effect4.Program.LayerView
public import Effect4.Data.Located
public import Effect4.Store.Carrier.Fold

/-!
# Program.ProfileSupport — profile support, one judgment

Profile support is one of the seven judgments (`docs/core/controlled-english.md` §4): does a
profile support a value, or a program? The profile is data (`ProfileData`). Its bound on naturals
has one owner, `ProfileData.natBound`, and `ProfileData.admitsNat` is the judgment's leaf.

- **A value** is supported when every number of its tree is inside the bound: a natural, a
  negative integer's magnitude `n + 1`, a constructor's index and a handle's key. The judgment is
  an algebra of the value tree's generated fold (`ProfileData.valueAlgebra`, `cata_val`). Its
  refusal is located at the path of the first number outside the bound: the child indices from
  the root, each placed by `Located.under`.
- **A host's answer** is supported when its value tree is (`answerTree`): an exit as the machine
  reifies it, and a reference read as its cell's handle.
- **A program** is supported when every natural literal it states is. The literal fold
  `natLiterals` lists them, each node's read by the generated argument readers (`readArgs_eff`
  and its siblings). The judgment (`ProfileData.literalRefusal`) reads the same literals through
  the generated path fold, so its refusal is located at the address of the node that states the
  first literal above the bound.

Consumers: the TypeScript face's emission and reading boundary (`Codegen/Checked.lean`,
`Codegen/Admit.lean`), the tool's JSON profile (`Tool/CodecProfile.lean`, `Tool/Native.lean`),
and, lowered through `ocaml/gen/roots.json`, the engine's ingress (`E4_engine`'s `ingress` and
`literal_refusal`), which the host driver and the kit call where they call reply admission.
The bound is the ingress rule: DI-56, decisions rows 108 and 417 (1). The run stays exact, and
the profile is a datum checked at ingress (the coherence plan's D3).

Placement: concept translation-simulation (`docs/core/semantics.md` §2.10), the property that a
face refuses outside its profile. Claim `profile-support-located`, whose pointer is
`ProfileData.valueRefusal_eq_none_iff` (`Laws/Program/ProfileSupport.lean`); requirement R8.
Not established: which face reads a supported value, and arithmetic inside a run, which the
builtin rows' crossing refuses until M4.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- **Why a profile does not support a value or a program**: a number outside its bound. -/
inductive ProfileReason where
  /-- A natural above the bound: a natural, a constructor's index, a handle's key or a program's
  literal. -/
  | aboveBound (n : Nat)
  /-- A negative integer `-(n + 1)` whose magnitude `n + 1` is above the bound. The reason names
  the stored `n`, so no sum is taken: the lowered `Nat` wraps at `2^62` until M4 (row 417 (1)). -/
  | belowBound (n : Nat)
deriving DecidableEq, Repr

/-- **A profile-support refusal**: the reason at a path. The path is the child indices from a
value's root, or the address of the program node that states the literal. -/
abbrev ProfileRefusal := Located (List Nat) ProfileReason

/-! ## The literal fold -/

/-- The natural literals of a term, by the generated term fold. -/
def termNatLiterals (term : Term) : List Nat :=
  foldMap_term [] (· ++ ·) term (f_term := fun
    | .lit (.nat n) => [n]
    | _ => [])

/-- The natural literals of a cause, by the generated cause fold. -/
def causeNatLiterals (cause : CauseTerm) : List Nat :=
  cata_cause (R := fun _ => List Nat) {
    cause_fail := termNatLiterals
    cause_die := termNatLiterals
    cause_interrupt := fun who => who.toList.flatMap termNatLiterals
    cause_both := (· ++ ·) } cause

/-- The natural literals of a literal argument. -/
def litNatLiterals : Lit → List Nat
  | .nat n => [n]
  | _ => []

/-- **The natural literals of one argument**, as the generated argument reader reads a node
(`ArgReader`, `readArgs_eff` and its siblings): a term's, a cause's, an optional term's, an
operation's binder term's and a literal argument's. A child is the fold's, not the reader's. The
reader reads no dependent field, so it lowers where the program view does not. -/
def literalReader {Op : Type} [ScopedOp Op] : ArgReader Op (List Nat) where
  child _ _ := []
  term _ t := termNatLiterals t
  cause _ c := causeNatLiterals c
  op _ o := (ScopedOp.term? o).toList.flatMap termNatLiterals
  nat _ _ := []
  mode _ _ := []
  bool _ _ := []
  key _ _ := []
  decision _ _ := []
  optTy _ _ := []
  decls _ _ := []
  forkOptions _ _ := []
  optTerm _ t := t.toList.flatMap termNatLiterals
  keys _ _ := []
  lit _ l := litNatLiterals l
  path _ _ := []

/-- **Every natural literal a program states**, by the generated program fold, each node's own
literals read by the generated argument readers. -/
def natLiterals {Op : Type} [ScopedOp Op] (program : Eff Op) : List Nat :=
  foldMap_eff [] (· ++ ·) program
    (fun n => (readArgs_eff literalReader n).flatten)
    (fun n => (readArgs_stmt literalReader n).flatten)
    (fun n => (readArgs_stmts literalReader n).flatten)
    (fun n => (readArgs_effs literalReader n).flatten)
    (fun n => (readArgs_action literalReader n).flatten)
    (fun n => (readArgs_layer literalReader n).flatten)
    (fun n => (readArgs_layers literalReader n).flatten)

/-! ## The judgment -/

namespace ProfileData

/-- **The leaf**: a natural inside the profile (`admitsNat`), or its refusal at the leaf. -/
def natRefusal (profile : ProfileData) (n : Nat) : Option ProfileRefusal :=
  if profile.admitsNat n then none else some ⟨[], .aboveBound n⟩

/-- The first refusal among the children, from index `i` on, each placed under its index. -/
def firstUnder : Nat → List (Option ProfileRefusal) → Option ProfileRefusal
  | _, [] => none
  | i, r :: rs => (r.map (Located.under [i])) <|> firstUnder (i + 1) rs

/-- **Profile support as an algebra of the value tree's fold.** A natural, a negative integer's
magnitude `n + 1`, a constructor's index and a handle's key are the leaves; the magnitude is
compared as `n < natBound`, with no sum. A list, a pair, an option and a constructor's arguments
refuse at their first child that refuses, under its index. Bytes, strings, references, a handle's
kind and a double's bits hold no natural of the profile. -/
def valueAlgebra (profile : ProfileData) : Store.ValAlgebra (fun _ => Option ProfileRefusal) where
  val_unit := none
  val_bool _ := none
  val_nat n := profile.natRefusal n
  val_str _ := none
  val_bytes _ := none
  val_list rs := firstUnder 0 rs
  val_pair a b := firstUnder 0 [a, b]
  val_none := none
  val_some a := firstUnder 0 [a]
  val_ctor i rs := profile.natRefusal i <|> firstUnder 0 rs
  val_ref _ _ := none
  val_handle _ key := profile.natRefusal key
  val_negInt n := if n < profile.natBound then none else some ⟨[], .belowBound n⟩
  val_float _ := none

/-- **Profile support of a value**: `none` when the profile supports it, otherwise the first
number outside the bound, at its path (`valueRefusal_eq_none_iff`). -/
def valueRefusal (profile : ProfileData) (v : Store.Val) : Option ProfileRefusal :=
  Store.cata_val profile.valueAlgebra v

/-- The first of a node's natural literals above the bound, at the node's address. -/
def literalsRefusal (profile : ProfileData) (literals : List Nat) (address : List Nat) :
    Option ProfileRefusal :=
  (literals.find? fun n => !profile.admitsNat n).map fun n => ⟨address, .aboveBound n⟩

/-- **Profile support of a program**: `none` when the profile supports every natural literal the
program states (`natLiterals`), otherwise the first literal above the bound, at the address of
the node that states it (`literalRefusal_eq_none_iff`). It reads each node's literals as
`natLiterals` does, through the generated path fold. -/
def literalRefusal (profile : ProfileData) (program : NativeEff) : Option ProfileRefusal :=
  foldMapAt_eff none (· <|> ·) [] program
    (fun n a => profile.literalsRefusal (readArgs_eff literalReader n).flatten a)
    (fun n a => profile.literalsRefusal (readArgs_stmt literalReader n).flatten a)
    (fun n a => profile.literalsRefusal (readArgs_stmts literalReader n).flatten a)
    (fun n a => profile.literalsRefusal (readArgs_effs literalReader n).flatten a)
    (fun n a => profile.literalsRefusal (readArgs_action literalReader n).flatten a)
    (fun n a => profile.literalsRefusal (readArgs_layer literalReader n).flatten a)
    (fun n a => profile.literalsRefusal (readArgs_layers literalReader n).flatten a)

end ProfileData

/-- **A host's answer as one value tree**: an exit as the machine reifies it (`reifyExitVal`), a
reference read as its cell's handle. Profile support reads a reply through it, and the native
host checks the same tree for the native carrier's domain. -/
def answerTree : Completion Val Err Defect FiberId Ann → Store.Val
  | .ofExit ex => Machine.reifyExitVal ex
  | .ofRefGet cell => Machine.Val.cell cell

end Effect4.Program
