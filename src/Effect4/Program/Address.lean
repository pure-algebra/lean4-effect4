module

public import Effect4.Program.Refs

/-!
# Program.Address — a path relocated, and the layer references of a moved subtree

An address is a path of child indices from the root of a program (`Node.at_`, `Node.replaceAt`,
`Program/Refs.lean`). A graph operation that moves or pastes a subtree changes the address of every
node in it. Three kinds of position move with the subtree (seat ORG's theory map,
`docs/research/2026-10-08-seat-ORG-theory-map.md` §3.3): variable levels, layer-reference targets
and row positions. This module relocates the second kind.

A layer reference stores its target as a path from the root (DB-12; decisions row 336 (6): absolute
targets, with `rebaseRefs` and its law). A reference inside a moved subtree whose target is inside
the subtree too names, after the move, whatever now stands at the old path. Seat ORG's finite probe
moved such a layer under a `suspend`: its target named the enclosing merge, and `Eff.layerRefsWF`
refused the program. So the targets move with the subtree:

- `Path.below base p` is the rest of `p` below `base`, or `none` when `base` is no prefix of `p`;
- `Path.rebase src dst p` moves a path below `src` to the same rest below `dst`, and leaves any other
  path as it is;
- `Node.mapRefs f` rewrites the target of every layer reference of a node by `f`, and rebuilds the
  rest as it was. It is one fold at each sort: `EffAlgebra.onRef` (`Program/Fold.lean`), the identity
  algebra with the reference slot replaced, at a reference again. The expansion of references is the
  same algebra at the target's term (`expandAlgebra`, `Program/Refs.lean`);
- `Node.rebaseRefs src dst` is `Node.mapRefs (Path.rebase src dst)`, and `Eff.rebaseRefs` is its
  program sort.

The law is `references_move` (`Laws/Program/AddressMove.lean`), the proposed claim `references-move`:
a subtree whose references stay inside it keeps its references well formed when it is pasted with
`Node.rebaseRefs` at an address outside the module's layers that has one scope. The battery
`Test/Program/AddressMove.lean` evaluates seat ORG's probe both ways.

The module relocates no variable level (`Eff.weaken` inserts a slot, and no operation removes one)
and no row position (the open part `sketch-renumbering` of R14). It defines no graph operation: a
move, a paste and an extract are row 336's V4.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

/-! ## A path relocated -/

/-- **The rest of a path below a base**: `some r` when the path is `base ++ r`, and `none` when the
base is no prefix of the path. -/
def Path.below : List Nat → List Nat → Option (List Nat)
  | [], p => some p
  | _ :: _, [] => none
  | b :: base, i :: p => if b = i then Path.below base p else none

/-- **A path relocated from base `src` to base `dst`**: a path below `src` keeps its rest below
`dst`, and any other path is left as it is. -/
def Path.rebase (src dst p : List Nat) : List Nat :=
  match Path.below src p with
  | some r => dst ++ r
  | none => p

/-- Whether the address `c` is inside the subtree at the address `a`. -/
def Table.under (a c : List Nat) : Bool := a.isPrefixOf c

/-! ## The layer references of a node, rewritten -/

variable {Op : Type}

/-- The program with the target of every layer reference rewritten by `f`: the fold of
`EffAlgebra.onRef` at a reference. -/
def Eff.mapRefs (f : List Nat → List Nat) (e : Eff Op) : Eff Op :=
  cata_eff (EffAlgebra.onRef fun target => .ref (f target)) e
/-- `Eff.mapRefs` at a statement. -/
def Stmt.mapRefs (f : List Nat → List Nat) (st : Stmt Op) : Stmt Op :=
  cata_stmt (EffAlgebra.onRef fun target => .ref (f target)) st
/-- `Eff.mapRefs` at a statement list. -/
def Stmts.mapRefs (f : List Nat → List Nat) (ss : Stmts Op) : Stmts Op :=
  cata_stmts (EffAlgebra.onRef fun target => .ref (f target)) ss
/-- `Eff.mapRefs` at a race's entrants. -/
def Effs.mapRefs (f : List Nat → List Nat) (es : Effs Op) : Effs Op :=
  cata_effs (EffAlgebra.onRef fun target => .ref (f target)) es
/-- `Eff.mapRefs` at a fiber action. -/
def ActionTerm.mapRefs (f : List Nat → List Nat) (a : ActionTerm Op) : ActionTerm Op :=
  cata_action (EffAlgebra.onRef fun target => .ref (f target)) a
/-- `Eff.mapRefs` at a layer. -/
def LayerTerm.mapRefs (f : List Nat → List Nat) (l : LayerTerm Op) : LayerTerm Op :=
  cata_layer (EffAlgebra.onRef fun target => .ref (f target)) l
/-- `Eff.mapRefs` at a layer list. -/
def LayerTerms.mapRefs (f : List Nat → List Nat) (ls : LayerTerms Op) : LayerTerms Op :=
  cata_layers (EffAlgebra.onRef fun target => .ref (f target)) ls

/-- **A node with the target of every layer reference rewritten by `f`**: its sort's fold. -/
def Node.mapRefs (f : List Nat → List Nat) : Node Op → Node Op
  | .eff e => .eff (e.mapRefs f)
  | .stmts s => .stmts (s.mapRefs f)
  | .stmt s => .stmt (s.mapRefs f)
  | .action a => .action (a.mapRefs f)
  | .effs es => .effs (es.mapRefs f)
  | .layer l => .layer (l.mapRefs f)
  | .layers ls => .layers (ls.mapRefs f)

/-- **A subtree's layer references, moved from base `src` to base `dst`**: each target below `src`
moves below `dst` (`Path.rebase`). A target outside the subtree stays as it is; the law
`references_move` reads only subtrees whose targets stay inside them. -/
def Node.rebaseRefs (src dst : List Nat) (n : Node Op) : Node Op :=
  n.mapRefs (Path.rebase src dst)

/-- `Node.rebaseRefs` at a program: the form a pasted program takes. -/
def Eff.rebaseRefs (src dst : List Nat) (e : Eff Op) : Eff Op :=
  e.mapRefs (Path.rebase src dst)

end Effect4.Program
