import Effect4.Program.Refs
import Effect4.Program.Native

/-!
# Program.Authoring — the scope reader: names for the program algebra's binders

An author never counts binder levels. The program signature (`Derived.lean` `EffShape`,
`Fold.lean` `EffAlgebra`) with one annotation, which argument of which constructor abstracts
which binders (`tools/Effect4Gen/binders.json`), is a binding signature; its algebra on the
**scope reader** carrier

    Src Op := Env → List Nat → Except Refusal (Eff Op)

is the authoring surface: for each constructor, run every argument under exactly the names it
abstracts, at the child path `Node.child` assigns it, and apply the constructor. Those
operations, one per constructor an author may write, are generated from the table into
`Program/Authoring/Lifts.lean` (DI-83, DI-84). This module is the carrier: the scope, the
refusal, the variable (the one name-resolving operation, nearest binder first, as the
reader's `Var.read` does), the closed-program and module elaborators, and shared layers by
name.

An authored program *is* an element of the algebra; `elaborate` evaluates it at the empty
scope. Reusing a fragment at two depths is applying it to two scopes; renaming a program's
names consistently leaves the tree unchanged, because names are read only through the scope
index. Nothing here is stored: the certificate, the printer and the machine see only the one
first-order `Eff` (DI-78).

Shared layers are the hoisted presentation with names in place of paths. A `Module` declares
each shared layer once by name; `elaborateModule` places every named layer at its first use
in program order and turns each later use into `LayerTerm.ref` of that path, which is what
`Eff.restoreAll` (`Program/Refs.lean`) does with a declaration block. Nobody writes a path.
-/

namespace Effect4.Program.Authoring

open Effect4.Program

/-- The names bound so far, in level order: level `i` is the `i`-th name. -/
abbrev Names := List String

/-- The level of the nearest binding of a name: the last position that carries it. -/
def Names.resolve (names : Names) (x : String) : Option Nat :=
  go names 0 none
where
  go : List String → Nat → Option Nat → Option Nat
    | [], _, acc => acc
    | y :: ys, i, acc => go ys (i + 1) (if y = x then some i else acc)

/-- Why elaboration refused, at the path where it did. -/
inductive Reason
  /-- A name with no binder in scope. -/
  | unbound (name : String)
  /-- A layer reference to no declared layer. -/
  | unboundLayer (name : String)
  /-- Two layer declarations under one name. -/
  | duplicateLayer (name : String)
  /-- Placing a layer failed at this path (a reference site the tree no longer has). -/
  | placement (name : String)
  /-- A call of a host row the module does not declare, by the spelling it was called under. -/
  | unboundRow (spelling : String)
  /-- A name only the surface may write: it begins with the reserved prefix. -/
  | reservedName (name : String)
  /-- Two row declarations under one spelling: a table key is the spelling and the trailing
  names (`Program/Table.lean` `rowKey`), so two rows cannot share one. -/
  | duplicateRow (spelling : String)
  deriving DecidableEq, Repr

structure Refusal where
  path : List Nat
  reason : Reason
  deriving DecidableEq, Repr

/-! ## Names the surface mints for itself

A binder a convenience introduces has a name like any other, and a name an author writes with
the same spelling is read by the same rule — the last binding wins. So a convenience that
mints a fixed spelling can be handed that spelling as its own argument and bind the wrong
variable (B-9). Two rules together close it: a minted name begins with `reservedPrefix`,
which `var` refuses, so an author cannot write one; and it carries the level it is bound at,
so two mints in one scope are two names. `minted` is the reader the surface uses for its own
names, the one `var` would be without the check. -/

/-- The two bytes a minted name begins with: `_` then `%`. A `%` is not part of a TypeScript
identifier, so a minted name never reaches the printer as a binder an author could have
written. -/
def reservedPrefix : String := "_%"

/-- Whether a name is one only the surface may write. Read off the UTF-8 bytes (`95` is `_`,
`37` is `%`): the string API's character traversals reach `Classical.choice` on this
toolchain, as `LayerTerm.readRefName` (`Program/Refs.lean`) records. -/
def Name.reserved (name : String) : Bool :=
  match name.toUTF8.data.toList with
  | 95 :: 37 :: _ => true
  | _ => false

/-- Declared layer names, each to the index of its declaration in the module. -/
abbrev LayerNames := List (String × Nat)

/-- Declared host rows, each spelling to its position in the module's table. -/
abbrev RowNames := List (String × Nat)

/-- What a source program reads: the value names in scope, the declared layer names, and the
declared host rows. -/
structure Env where
  names : Names := []
  layers : LayerNames := []
  rows : RowNames := []

/-- A source term. -/
abbrev TermSrc := Env → List Nat → Except Refusal Term

/-- A source program. -/
abbrev Src (Op : Type) := Env → List Nat → Except Refusal (Eff Op)

/-- A source cause. -/
abbrev CauseSrc := Env → List Nat → Except Refusal CauseTerm

/-- A source fiber action. -/
abbrev ActionSrc (Op : Type) := Env → List Nat → Except Refusal (ActionTerm Op)

/-- A source layer. -/
abbrev LayerSrc (Op : Type) := Env → List Nat → Except Refusal (LayerTerm Op)

/-- Extend the scope by the names a child binds. -/
def Env.push (env : Env) (xs : List String) : Env := { env with names := env.names ++ xs }

/-- The empty value scope, for a layer body (`layerTy` types it in the empty environment).
The declared layers and rows stay: a layer body calls the module's rows like any other. -/
def Env.closed (env : Env) : Env := { env with names := [] }

/-- A binder name the surface mints for itself in this scope: the reserved prefix, the stem
that says which convenience minted it, and the level it will be bound at. Only one binder
sits at a level, so two mints in one scope are two names, and no name an author wrote can be
bound in a mint's place, because `var` refuses the reserved prefix. -/
def Env.mint (env : Env) (stem : String) : String :=
  reservedPrefix ++ stem ++ toString env.names.length

def termsOfList : List Term → Terms
  | [] => .nil
  | t :: ts => .cons t (termsOfList ts)

def effsOfList {Op : Type} : List (Eff Op) → Effs Op
  | [] => .nil
  | e :: es => .cons e (effsOfList es)

/-! ## Spines and options, elaborated in order

A list argument is a spine (`Effs`, `LayerTerms`): entry `i` lives at the spine path
`p ++ [rank] ++ replicate i 1 ++ [0]`, one `cons` per index (`Node.child`). These three
helpers are what the generated lifts call, so a proof about a lift meets a named function
and not a `mapM` over an index. -/

def elabEffs {Op : Type} : List (Src Op) → Env → List Nat → Except Refusal (Effs Op)
  | [], _, _ => .ok .nil
  | e :: es, env, spine => do
    let x ← e env (spine ++ [0])
    let xs ← elabEffs es env (spine ++ [1])
    .ok (.cons x xs)

def elabLayers {Op : Type} : List (LayerSrc Op) → Env → List Nat → Except Refusal (LayerTerms Op)
  | [], _, _ => .ok .nil
  | l :: ls, env, spine => do
    let x ← l env (spine ++ [0])
    let xs ← elabLayers ls env (spine ++ [1])
    .ok (.cons x xs)

def elabOption : Option TermSrc → Env → List Nat → Except Refusal (Option Term)
  | none, _, _ => .ok none
  | some t, env, p => do
    let x ← t env p
    .ok (some x)

/-! ## Terms: the one name-resolving operation, and the two that resolve nothing -/

/-- A variable by name: the level of its nearest binder. A name under the reserved prefix is
refused — it is one the surface minted for itself, and reading it through this operation is
the capture B-9 names. The surface reads its own names with `minted`. -/
def var (x : String) : TermSrc := fun env p =>
  if Name.reserved x then .error ⟨p, .reservedName x⟩
  else
    match env.names.resolve x with
    | some i => .ok (.var i)
    | none => .error ⟨p, .unbound x⟩

/-- A variable the surface minted (`Env.mint`): `var` without the reserved check, because the
reserved prefix is exactly what this reader is for. An author never calls it. -/
def minted (x : String) : TermSrc := fun env p =>
  match env.names.resolve x with
  | some i => .ok (.var i)
  | none => .error ⟨p, .unbound x⟩

def lit (value : Lit) : TermSrc := fun _ _ => .ok (.lit value)

def nat (n : Nat) : TermSrc := lit (.nat n)
def str (s : String) : TermSrc := lit (.str s)
def bool (b : Bool) : TermSrc := lit (.bool b)
def unit : TermSrc := lit .unit

/-- An atom applied to arguments. Arguments share the term's path: a term has no children in
the tree's addressing (`Node.child`), so a refusal inside one names the term's node. -/
def app (atom : String) (args : List TermSrc) : TermSrc := fun env p => do
  let vs ← args.mapM (· env p)
  .ok (.app atom (termsOfList vs))

/-! ## Host rows by name

A host row is a position in the table supplied beside the program (`NativeOp.external i`,
`Program/Native.lean`). An author who writes the position writes an integer whose meaning
lives in a table passed separately, and nothing checks that the two were counted together.
A `RowDef` is that row declared once under its spelling; `Module` assembles the table in
declaration order, and `Row.call` resolves the spelling to the position the module gave it.
The key is `rowKey` (`Program/Table.lean`), the spelling and the trailing names, the same
pair `Table.lawful` requires to be unique; a host row declares no trailing name, so the
spelling alone is its key. -/

/-- A host row an author declares once, with the spelling it is called under. -/
structure RowDef where
  row : Row
  deriving DecidableEq, Repr

/-- A row the host answers: the spelling the printer prints and the reader reads, the request
and answer types, the error column and the rc.112 line it transcribes. `kind := .async` and
`registration := .external` are what `externalRow` (`Program/Compile.lean`) demands of a row
the host answers, and `checkTable` (`Program/Native.lean`) is where a table that breaks them
is refused. -/
def Row.host (spelling : String) (request answer : Ty) (error : Ty := .never)
    (cite : String := "") : RowDef :=
  ⟨{ name := spelling, spelling := spelling, shape := .call, trailing := [], kind := .async,
     request := request, answer := answer, error := error, requires := [], cite := cite,
     typeArgs := [], registration := .external }⟩

/-- The key this row is declared and called under (`rowKey`, `Program/Table.lean`). -/
def RowDef.key (r : RowDef) : String × List String := (r.row.spelling, r.row.trailing)

/-- The rows of a list of declarations, in declaration order: the table to supply beside the
program. A declaration's position in this list is the `NativeOp.external` index that calls it. -/
def RowDef.table (rows : List RowDef) : RowTable := rows.map (·.row)

/-- The spelling each declaration was made under, with its position in `RowDef.table`. -/
def RowDef.names (rows : List RowDef) : RowNames :=
  rows.zipIdx.map fun (r, i) => (r.row.spelling, i)

/-- A declared host row, called on a request. The position is the one the module's table put
the declaration at; an undeclared spelling refuses at the call site. -/
def Row.call (r : RowDef) (request : TermSrc) : Src NativeOp := fun env p =>
  match env.rows.find? (fun entry => entry.1 == r.row.spelling) with
  | some (_, i) => do
    let x ← request env p
    .ok (.perform (.external i) x)
  | none => .error ⟨p, .unboundRow r.row.spelling⟩

/-! ## Services and packages, as declarations

A service is a key and the carrier the signature types it at; nothing in the tree bound the
two at the authoring site before, so an author held `⟨⟨6⟩, ⟨7⟩⟩` and "`7` is a `Ref`" as two
separate facts (B-1). A `ServiceDef` states them once, with the operations that may be
performed on a value of that carrier — rows, whose receiver is the first component of the
request (`RowShape.method`), which is what the printer already prints. A `Package` is a block
of rows and services installed as one unit. The operations over these records live in
`Program/Authoring/Services.lean`; the records are here because `Module` holds them. -/

/-- A service an author declares once: the key, the carrier the signature must type it at,
and the operations that may be performed on a value of that carrier. -/
structure ServiceDef where
  key : Effect4.ServiceKey
  carrier : Ty
  ops : List RowDef := []
  deriving DecidableEq, Repr

/-- A block of rows and services installed as one unit: what one host library offers. -/
structure Package where
  name : String
  rows : List RowDef := []
  services : List ServiceDef := []
  deriving DecidableEq, Repr

/-! ## Shared layers by name -/

/-- A reference target no tree has: the placeholder for the `k`-th declared layer until it is
placed. Real targets are paths into the tree; no node has a billion children. -/
def placeholderBase : Nat := 1000000000

def placeholder (k : Nat) : List Nat := [placeholderBase + k]

/-- The declaration index a placeholder target names, if it is one. -/
def placeholder? : List Nat → Option Nat
  | [n] => if placeholderBase ≤ n then some (n - placeholderBase) else none
  | _ => none

/-- A declared layer by name. Until placement it is a reference to the placeholder target of
its declaration; `elaborateModule` places the term at the first use and points every later
use at that path. The one hand-written layer lift: it resolves a name. -/
def Layer.ref {Op : Type} (name : String) : LayerSrc Op := fun env p =>
  match env.layers.find? (·.1 == name) with
  | some (_, k) => .ok (.ref (placeholder k))
  | none => .error ⟨p, .unboundLayer name⟩

/-! ## Elaboration -/

/-- A closed program: no value in scope, no declared layers, no declared rows. -/
def elaborate {Op : Type} (src : Src Op) : Except Refusal (Eff Op) := src {} []

/-- A closed layer: the same, for a layer written on its own. -/
def elaborateLayer {Op : Type} (l : LayerSrc Op) : Except Refusal (LayerTerm Op) := l {} []

/-- An authored module: the host rows it declares, the services it declares, the shared
layers declared once by name, and the main program. One value holds everything a program
needs, so the table a program is checked against is the table it was written against. -/
structure Module (Op : Type) where
  rows : List RowDef := []
  services : List ServiceDef := []
  layers : List (String × LayerSrc Op) := []
  main : Src Op

/-- Every row a module supplies, in table order: its own declarations, then each service's
operations in service order. -/
def Module.rowDefs {Op : Type} (m : Module Op) : List RowDef :=
  m.rows ++ m.services.flatMap (·.ops)

/-- The table to supply beside the module's program. -/
def Module.table {Op : Type} (m : Module Op) : RowTable := RowDef.table m.rowDefs

/-- The spelling each of the module's rows was declared under, with its position. -/
def Module.rowNames {Op : Type} (m : Module Op) : RowNames := RowDef.names m.rowDefs

/-- The service carriers the module declares, as the signature's service table reads them. -/
def Module.serviceTypes {Op : Type} (m : Module Op) : List (Effect4.ServiceKey × Ty) :=
  m.services.map fun s => (s.key, s.carrier)

private def layerNamesOf {Op : Type} (layers : List (String × LayerSrc Op)) :
    Except Refusal LayerNames :=
  layers.zipIdx.foldlM (init := []) fun acc ((name, _), k) =>
    if acc.any (·.1 == name) then .error ⟨[], .duplicateLayer name⟩ else .ok (acc ++ [(name, k)])

/-- The placeholder sites of a tree, in program order: `(site, k)` for every reference to the
`k`-th declaration. -/
private def placeholderSites {Op : Type} (tree : Eff Op) : List (List Nat × Nat) :=
  let sites := (tree.refSites []).filterMap fun (site, target) =>
    (placeholder? target).map fun k => (site, k)
  let paths := Path.sortBy Path.lt (sites.map (·.1))
  paths.filterMap fun s => (sites.find? (·.1 == s))

/-- Place each declared layer at its first use, one per round: the earliest unplaced
placeholder site in program order receives its declaration's term (whose own references to
declared layers are placeholders again, handled by later rounds). -/
private def placeRounds {Op : Type} (terms : List (LayerTerm Op)) (names : LayerNames) :
    Nat → Eff Op → List (Nat × List Nat) → Except Refusal (Eff Op × List (Nat × List Nat))
  | 0, tree, placed => .ok (tree, placed)
  | fuel + 1, tree, placed =>
    match (placeholderSites tree).find? fun (_, k) => !placed.any (·.1 == k) with
    | none => .ok (tree, placed)
    | some (site, k) =>
      let name := ((names.find? (·.2 == k)).map (·.1)).getD ""
      match terms[k]?, (Node.eff tree).replaceLayerAt site (terms.getD k (.ref site)) with
      | some _, some (Node.eff tree') => placeRounds terms names fuel tree' ((k, site) :: placed)
      | _, _ => .error ⟨site, .placement name⟩

/-- Every remaining placeholder reference points at the placed declaration. -/
private def pointAtPlaced {Op : Type} (placed : List (Nat × List Nat)) (tree : Eff Op) :
    Except Refusal (Eff Op) :=
  (placeholderSites tree).foldlM (init := tree) fun acc (site, k) =>
    match placed.find? (·.1 == k) with
    | some (_, target) =>
      match (Node.eff acc).replaceLayerAt site (.ref target) with
      | some (Node.eff acc') => .ok acc'
      | _ => .error ⟨site, .placement ""⟩
    | none => .error ⟨site, .placement ""⟩

/-- Two rows declared under one spelling refuse: a table key is the spelling and the trailing
names, and `Table.lawful` requires it to be unique. -/
private def rowNamesOf (rows : List RowDef) : Except Refusal RowNames :=
  rows.zipIdx.foldlM (init := []) fun acc (r, i) =>
    if acc.any (·.1 == r.row.spelling) then .error ⟨[], .duplicateRow r.row.spelling⟩
    else .ok (acc ++ [(r.row.spelling, i)])

/-- The one first-order tree of an authored module: main elaborated in the empty scope, every
declared layer placed at its first use in program order, every later use a reference to that
path. A declared layer nobody uses is dropped; a declared row nobody calls keeps its position,
because the table's positions are the declaration order. -/
def elaborateModule {Op : Type} (m : Module Op) : Except Refusal (Eff Op) := do
  let names ← layerNamesOf m.layers
  let rows ← rowNamesOf m.rowDefs
  let env : Env := { layers := names, rows := rows }
  let main ← m.main env []
  let terms ← m.layers.zipIdx.mapM fun ((_, l), k) => l env (placeholder k)
  let (tree, placed) ← placeRounds terms names (m.layers.length + 1) main []
  pointAtPlaced placed tree

end Effect4.Program.Authoring
