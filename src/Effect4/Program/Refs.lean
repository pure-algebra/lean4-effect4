import Effect4.Program.NodeLenses
import Effect4.Program.Fold

/-!
# Program.Refs — nodes, paths and layer references (the host rows slice, step 2)

The mutual program family addressed by paths, generic in the operation alphabet, and the
operations the layer reference `LayerTerm.ref` needs on top of it. `Node` is
`Program/Node.lean`; its `child` and `setChild` are generated from the constructor
declarations (`Program/NodeLenses.lean`), the one child scheme typing, printing, reading
and the compile resolve against — one table, no agreement lemma.

A layer's identity is its path (DB-12, `LayerId := List Nat` in `Machine/Stores.lean`). A
reference `LayerTerm.ref target` names the defining occurrence of another layer term by its
path: `const L = Layer.effect(…)` used at a second site (rc.112 keys its memo map on the
layer object, `Layer.ts:411`, `:438`). Well-formedness (`layerRefsWF`): every target names a
layer of the same program that is not itself a reference, and the target precedes the
reference in program order (lexicographically on paths), which makes the references
acyclic without a cycle walk. Typing resolves references by expansion (`expandRefs`): each
reference is replaced by the term at its target, round after round, and a well-formed
program is reference-free after at most as many rounds as it has reference sites; the
compile does not expand — it redirects (`Compile.lean` `resolveLayer`), which is what gives
two references one memo key.

Printing a program with references is a declaration block (`Codegen/Print.lean`
`printModule`): every target is hoisted into `const L_<path> = …` and its site — the
defining occurrence and every reference — prints as that identifier, so rc.112 sees one
object. `hoistAll` and `refTargets` here are that block's arithmetic; `readModule`
(`Codegen/Read.lean`) puts the declarations back at their paths. The identifier carries the
path in its digits (`refName`), and `readRefName` decodes it from the UTF-8 bytes
(`String.toUTF8` is the representation; the string API's character traversals reach
`Classical.choice` on this toolchain, `Eff.lean` `Ty.key`).
-/

namespace Effect4.Program

/-! ## Nodes and paths -/

namespace Node

variable {Op : Type}

/-- The node at a path. -/
def at_ : Node Op → List Nat → Option (Node Op)
  | n, [] => some n
  | n, i :: rest => (n.child i).bind (at_ · rest)

/-- The layer at a path; `none` when the path names no layer. -/
def layerAt (n : Node Op) (p : List Nat) : Option (LayerTerm Op) :=
  match n.at_ p with
  | some (layer l) => some l
  | _ => none

/-- The node with the layer at a path replaced; `none` when the path names no layer. -/
def replaceLayerAt : Node Op → List Nat → LayerTerm Op → Option (Node Op)
  | layer _, [], l' => some (layer l')
  | _, [], _ => none
  | n, i :: rest, l' => do
    let c ← n.child i
    let c' ← replaceLayerAt c rest l'
    n.setChild i c'

/-- The program of an `eff` node. -/
def eff? : Node Op → Option (Eff Op)
  | eff e => some e
  | _ => none

end Node

/-! ## Program order on paths -/

/-- Strict lexicographic order on paths: a proper prefix is earlier. -/
def Path.lt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else Path.lt as bs

/-- `a` is a proper prefix of `b`. -/
def Path.properPrefix : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a = b && Path.properPrefix as bs

/-- `a` is declared before `b` in a declaration block: a target inside another comes first
(its `const` is used by the enclosing one), and otherwise program order. -/
def Path.declBefore (a b : List Nat) : Bool :=
  Path.properPrefix b a || (!Path.properPrefix a b && Path.lt a b)

/-- Insertion sort by a strict comparator (small lists: the targets of a program). -/
def Path.insertBy (before : List Nat → List Nat → Bool) (x : List Nat) :
    List (List Nat) → List (List Nat)
  | [] => [x]
  | y :: rest => if before x y then x :: y :: rest else y :: Path.insertBy before x rest

def Path.sortBy (before : List Nat → List Nat → Bool) (xs : List (List Nat)) : List (List Nat) :=
  xs.foldl (fun acc x => Path.insertBy before x acc) []

/-! ## Reference sites -/

/-- The one yield of the reference walk: a `ref` at its site. -/
def LayerTerm.refSite {Op : Type} : LayerTerm Op → List Nat → List (List Nat × List Nat)
  | .ref target, p => [(p, target)]
  | _, _ => []

/-- Every `LayerTerm.ref` under a program, as `(site, target)` pairs in program order, the
site's path from the root at `p`; the child indices are `Node.child`'s. One yield over the
path fold (`foldMapAt_eff`, `Program/Fold.lean`), at each sort. -/
def Eff.refSites {Op : Type} (p : List Nat) (e : Eff Op) : List (List Nat × List Nat) :=
  foldMapAt_eff [] (· ++ ·) p e (f_layer := LayerTerm.refSite)
def Stmts.refSites {Op : Type} (p : List Nat) (ss : Stmts Op) : List (List Nat × List Nat) :=
  foldMapAt_stmts [] (· ++ ·) p ss (f_layer := LayerTerm.refSite)
def Stmt.refSites {Op : Type} (p : List Nat) (st : Stmt Op) : List (List Nat × List Nat) :=
  foldMapAt_stmt [] (· ++ ·) p st (f_layer := LayerTerm.refSite)
def Effs.refSites {Op : Type} (p : List Nat) (es : Effs Op) : List (List Nat × List Nat) :=
  foldMapAt_effs [] (· ++ ·) p es (f_layer := LayerTerm.refSite)
def ActionTerm.refSites {Op : Type} (p : List Nat) (a : ActionTerm Op) : List (List Nat × List Nat) :=
  foldMapAt_action [] (· ++ ·) p a (f_layer := LayerTerm.refSite)
def LayerTerm.refSites {Op : Type} (p : List Nat) (l : LayerTerm Op) : List (List Nat × List Nat) :=
  foldMapAt_layer [] (· ++ ·) p l (f_layer := LayerTerm.refSite)
def LayerTerms.refSites {Op : Type} (p : List Nat) (ls : LayerTerms Op) : List (List Nat × List Nat) :=
  foldMapAt_layers [] (· ++ ·) p ls (f_layer := LayerTerm.refSite)


/-! ## Expansion, for typing -/

/-- The expansion algebra: the identity fold with every `ref` replaced by the layer at its
target in `orig`, the original program (paths are root-relative, and the compile resolves
against the same root); a target that names no layer is left as it is. -/
def expandAlgebra {Op : Type} (orig : Node Op) : EffAlgebra Op (EffSelfCarrier Op) :=
  EffAlgebra.onRef fun target => (orig.layerAt target).getD (.ref target)

/-- One round of expansion, at each sort: the fold of the expansion algebra. -/
def Eff.expandRound {Op : Type} (orig : Node Op) (e : Eff Op) : Eff Op :=
  cata_eff (expandAlgebra orig) e
def Stmts.expandRound {Op : Type} (orig : Node Op) (ss : Stmts Op) : Stmts Op :=
  cata_stmts (expandAlgebra orig) ss
def Stmt.expandRound {Op : Type} (orig : Node Op) (st : Stmt Op) : Stmt Op :=
  cata_stmt (expandAlgebra orig) st
def Effs.expandRound {Op : Type} (orig : Node Op) (es : Effs Op) : Effs Op :=
  cata_effs (expandAlgebra orig) es
def ActionTerm.expandRound {Op : Type} (orig : Node Op) (a : ActionTerm Op) : ActionTerm Op :=
  cata_action (expandAlgebra orig) a
def LayerTerm.expandRound {Op : Type} (orig : Node Op) (l : LayerTerm Op) : LayerTerm Op :=
  cata_layer (expandAlgebra orig) l
def LayerTerms.expandRound {Op : Type} (orig : Node Op) (ls : LayerTerms Op) : LayerTerms Op :=
  cata_layers (expandAlgebra orig) ls


/-- The layer references of a program are well formed: every target names a layer of this
program that is not itself a reference, precedes the reference in program order, and does
not enclose it (a reference inside its own target would be a `const` that names itself). -/
def Eff.layerRefsWF {Op : Type} (root : Eff Op) : Bool :=
  (root.refSites []).all fun (site, target) =>
    Path.lt target site && !Path.properPrefix target site &&
      (match (Node.eff root).layerAt target with
       | some (.ref _) => false
       | some _ => true
       | none => false)

/-- The path of every layer under a program, in program order (a layer before the layers
inside it), the root at `p`: the path fold yielding every layer's path. -/
def Eff.layerPaths {Op : Type} (p : List Nat) (e : Eff Op) : List (List Nat) :=
  foldMapAt_eff [] (· ++ ·) p e (f_layer := fun _ q => [q])
def Stmts.layerPaths {Op : Type} (p : List Nat) (ss : Stmts Op) : List (List Nat) :=
  foldMapAt_stmts [] (· ++ ·) p ss (f_layer := fun _ q => [q])
def Stmt.layerPaths {Op : Type} (p : List Nat) (st : Stmt Op) : List (List Nat) :=
  foldMapAt_stmt [] (· ++ ·) p st (f_layer := fun _ q => [q])
def Effs.layerPaths {Op : Type} (p : List Nat) (es : Effs Op) : List (List Nat) :=
  foldMapAt_effs [] (· ++ ·) p es (f_layer := fun _ q => [q])
def ActionTerm.layerPaths {Op : Type} (p : List Nat) (a : ActionTerm Op) : List (List Nat) :=
  foldMapAt_action [] (· ++ ·) p a (f_layer := fun _ q => [q])
def LayerTerm.layerPaths {Op : Type} (p : List Nat) (l : LayerTerm Op) : List (List Nat) :=
  foldMapAt_layer [] (· ++ ·) p l (f_layer := fun _ q => [q])
def LayerTerms.layerPaths {Op : Type} (p : List Nat) (ls : LayerTerms Op) : List (List Nat) :=
  foldMapAt_layers [] (· ++ ·) p ls (f_layer := fun _ q => [q])


/-- The program with every reference expanded to its target's term, `refSites + 1` rounds:
each round resolves one hop, and a well-formed program's hops are bounded by its sites. -/
def Eff.expandRefs {Op : Type} (root : Eff Op) : Eff Op :=
  let orig := Node.eff root
  (List.range ((root.refSites []).length + 1)).foldl (fun acc _ => Eff.expandRound orig acc) root

/-! ## The declaration block's arithmetic -/

/-- The distinct targets of a program's references, in declaration order (`Path.declBefore`). -/
def Eff.refTargets {Op : Type} (root : Eff Op) : List (List Nat) :=
  Path.sortBy Path.declBefore ((root.refSites []).map (·.2)).eraseDups

/-- Every target hoisted out of the program: the term at each target captured and its site
replaced by a reference to itself, targets nested in others captured first (descending
program order), so a captured term already carries its nested targets as references. The
main program and the captured terms, each with its path; `none` when a target names no
layer. -/
def Eff.hoistAll {Op : Type} (root : Eff Op) :
    Except (List Nat) (Eff Op × List (List Nat × LayerTerm Op)) :=
  let targets := Path.sortBy (fun a b => Path.lt b a) root.refTargets
  targets.foldlM (init := (root, [])) fun (acc, decls) t =>
    match (Node.eff acc).layerAt t, (Node.eff acc).replaceLayerAt t (.ref t) with
    | some l, some (Node.eff acc') => .ok (acc', (t, l) :: decls)
    | _, _ => .error t

/-- Declarations put back at their paths, ancestors first (ascending program order), so a
nested target's site exists when its turn comes. -/
def Eff.restoreAll {Op : Type} (main : Eff Op) (decls : List (List Nat × LayerTerm Op)) :
    Option (Eff Op) :=
  let ordered := Path.sortBy Path.lt (decls.map (·.1))
  ordered.foldlM (init := main) fun acc t => do
    let l ← (decls.find? (·.1 == t)).map (·.2)
    let n ← (Node.eff acc).replaceLayerAt t l
    n.eff?

/-! ## The identifier that carries a path -/

/-- The declared name of a target: `L_` then its indices joined by `_` (`L_1_0_0`). -/
def LayerTerm.refName (target : List Nat) : String :=
  "L_" ++ "_".intercalate (target.map toString)

/-- A decimal group of the name's bytes: digits until the separator or the end. -/
def LayerTerm.readGroup : List UInt8 → Nat → Bool → Option (Nat × List UInt8)
  | [], acc, seen => if seen then some (acc, []) else none
  | b :: rest, acc, seen =>
    if b = 95 then (if seen then some (acc, rest) else none)
    else if 48 ≤ b ∧ b ≤ 57 then LayerTerm.readGroup rest (acc * 10 + (b.toNat - 48)) true
    else none

/-- The groups of the name's bytes after `L_`, separated by `_`; fuel is the byte count. -/
def LayerTerm.readGroups : Nat → List UInt8 → Option (List Nat)
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bs => do
    let (n, rest) ← LayerTerm.readGroup bs 0 false
    let ns ← LayerTerm.readGroups fuel rest
    some (n :: ns)

/-- The path a declared name carries, read off its UTF-8 bytes; `none` unless the name is
`L_` followed by digit groups. The reader checks `refName` of the answer against the name,
so a non-canonical spelling (a leading zero) is refused there. -/
def LayerTerm.readRefName (s : String) : Option (List Nat) :=
  match s.toUTF8.data.toList with
  | 76 :: 95 :: b :: rest => LayerTerm.readGroups (b :: rest).length (b :: rest)
  | _ => none

/-! ## Receipts -/

#guard LayerTerm.refName [1, 0, 0] = "L_1_0_0"
#guard LayerTerm.readRefName "L_1_0_0" = some [1, 0, 0]
#guard LayerTerm.readRefName "L_0" = some [0]
#guard LayerTerm.readRefName "L_" = none
#guard LayerTerm.readRefName "L_1__0" = none
#guard LayerTerm.readRefName "a0" = none
#guard LayerTerm.readRefName "L_12_3" = some [12, 3]
#guard [[0], [1, 0], [1, 0, 0], [0, 2]].all fun t => LayerTerm.readRefName (LayerTerm.refName t) = some t
#guard Path.lt [0] [0, 1] && Path.lt [0, 1] [1] && !Path.lt [1] [0, 1] && !Path.lt [] []
#guard Path.sortBy Path.declBefore [[1, 0], [0, 0, 1], [0, 0]] = [[0, 0, 1], [0, 0], [1, 0]]

end Effect4.Program
