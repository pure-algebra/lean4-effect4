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
  deriving DecidableEq, Repr

structure Refusal where
  path : List Nat
  reason : Reason
  deriving DecidableEq, Repr

/-- Declared layer names, each to the index of its declaration in the module. -/
abbrev LayerNames := List (String × Nat)

/-- What a source program reads: the value names in scope and the declared layer names. -/
structure Env where
  names : Names := []
  layers : LayerNames := []

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

/-- The empty value scope, for a layer body (`layerTy` types it in the empty environment). -/
def Env.closed (env : Env) : Env := { env with names := [] }

def termsOfList : List Term → Terms
  | [] => .nil
  | t :: ts => .cons t (termsOfList ts)

def effsOfList {Op : Type} : List (Eff Op) → Effs Op
  | [] => .nil
  | e :: es => .cons e (effsOfList es)

/-! ## Terms: the one name-resolving operation, and the two that resolve nothing -/

/-- A variable by name: the level of its nearest binder. -/
def var (x : String) : TermSrc := fun env p =>
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

/-- A closed program: no value in scope, no declared layers. -/
def elaborate {Op : Type} (src : Src Op) : Except Refusal (Eff Op) := src {} []

/-- An authored module: shared layers declared once by name, and the main program. -/
structure Module (Op : Type) where
  layers : List (String × LayerSrc Op) := []
  main : Src Op

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

/-- The one first-order tree of an authored module: main elaborated in the empty scope, every
declared layer placed at its first use in program order, every later use a reference to that
path. A declared layer nobody uses is dropped. -/
def elaborateModule {Op : Type} (m : Module Op) : Except Refusal (Eff Op) := do
  let names ← layerNamesOf m.layers
  let env : Env := { layers := names }
  let main ← m.main env []
  let terms ← m.layers.zipIdx.mapM fun ((_, l), k) => l env (placeholder k)
  let (tree, placed) ← placeRounds terms names (m.layers.length + 1) main []
  pointAtPlaced placed tree

end Effect4.Program.Authoring
