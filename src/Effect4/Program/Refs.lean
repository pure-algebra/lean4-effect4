import Effect4.Program.Eff

/-!
# Program.Refs — nodes, paths and layer references (the host rows slice, step 2)

The mutual program family addressed by paths, generic in the operation alphabet, and the
operations the layer reference `LayerTerm.ref` needs on top of it. `Node` and its `child`
and `at_` were `Program/Compile.lean`'s at `NativeOp` until this slice; they moved here so
that typing, printing and reading can address a layer by its path with the one child scheme
the compile resolves against — one table, no agreement lemma.

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

/-- A node of the mutual program family, addressed by a path of child indices. -/
inductive Node (Op : Type)
  | eff (e : Eff Op)
  | stmts (s : Stmts Op)
  | stmt (s : Stmt Op)
  | action (a : ActionTerm Op)
  | effs (es : Effs Op)
  /-- A layer (the join): its path is its identity, `LayerId` (`Machine/Stores.lean`). -/
  | layer (l : LayerTerm Op)
  /-- The list of a `mergeAll`: a spine, like `effs`. -/
  | layers (ls : LayerTerms Op)
deriving DecidableEq

namespace Node

variable {Op : Type}

/-- The child at an index. Terms are not nodes: only programs, statements, actions, layers
and the two spines are addressed. -/
def child : Node Op → Nat → Option (Node Op)
  | eff (.suspend b), 0 => some (eff b)
  | eff (.bind a _), 0 => some (eff a)
  | eff (.bind _ b), 1 => some (eff b)
  | eff (.gen ss), 0 => some (stmts ss)
  | eff (.catchCause b _), 0 => some (eff b)
  | eff (.catchCause _ h), 1 => some (eff h)
  | eff (.catchIf _ b _), 0 => some (eff b)
  | eff (.catchIf _ _ h), 1 => some (eff h)
  | eff (.matchCause b _ _), 0 => some (eff b)
  | eff (.matchCause _ v _), 1 => some (eff v)
  | eff (.matchCause _ _ c), 2 => some (eff c)
  | eff (.onExit b _), 0 => some (eff b)
  | eff (.onExit _ f), 1 => some (eff f)
  | eff (.exit b), 0 => some (eff b)
  | eff (.uninterruptible b), 0 => some (eff b)
  | eff (.interruptible b), 0 => some (eff b)
  | eff (.branch _ a _), 0 => some (eff a)
  | eff (.branch _ _ b), 1 => some (eff b)
  | eff (.whileLoop _ _ _ b), 0 => some (eff b)
  | eff (.withFiber a), 0 => some (action a)
  | eff (.scoped b), 0 => some (eff b)
  | eff (.acquireRelease a _), 0 => some (eff a)
  | eff (.acquireRelease _ r), 1 => some (eff r)
  | eff (.choose _ l _), 0 => some (eff l)
  | eff (.choose _ _ r), 1 => some (eff r)
  | eff (.provideLayer l _ _), 0 => some (layer l)
  | eff (.provideLayer _ _ b), 1 => some (eff b)
  | eff (.provideService _ _ b), 0 => some (eff b)
  | layer (.effect _ b), 0 => some (eff b)
  | layer (.effectDiscard b), 0 => some (eff b)
  | layer (.provide s _), 0 => some (layer s)
  | layer (.provide _ t), 1 => some (layer t)
  | layer (.provideMerge s _), 0 => some (layer s)
  | layer (.provideMerge _ t), 1 => some (layer t)
  | layer (.merge l _), 0 => some (layer l)
  | layer (.merge _ r), 1 => some (layer r)
  | layer (.fresh i), 0 => some (layer i)
  | layer (.orDie i), 0 => some (layer i)
  | layer (.mergeAll ls), 0 => some (layers ls)
  | layers (.cons h _), 0 => some (layer h)
  | layers (.cons _ t), 1 => some (layers t)
  | stmts (.cons h _), 0 => some (stmt h)
  | stmts (.cons _ t), 1 => some (stmts t)
  | stmt (.bindYield e), 0 => some (eff e)
  | stmt (.yieldDiscard e), 0 => some (eff e)
  | stmt (.ifElse _ a _), 0 => some (stmts a)
  | stmt (.ifElse _ _ b), 1 => some (stmts b)
  | stmt (.whileTrue b), 0 => some (stmts b)
  | action (.fork p _), 0 => some (eff p)
  | action (.forkIn p _ _), 0 => some (eff p)
  | action (.forkScoped p _), 0 => some (eff p)
  | action (.raceAll es), 0 => some (effs es)
  | effs (.cons h _), 0 => some (eff h)
  | effs (.cons _ t), 1 => some (effs t)
  | _, _ => none

/-- The node at a path. -/
def at_ : Node Op → List Nat → Option (Node Op)
  | n, [] => some n
  | n, i :: rest => (n.child i).bind (at_ · rest)

/-- The node with the child at an index replaced, one arm per arm of `child`; `none` where
`child` answers `none` or the replacement is a node of the wrong sort. -/
def setChild : Node Op → Nat → Node Op → Option (Node Op)
  | eff (.suspend _), 0, eff b => some (eff (.suspend b))
  | eff (.bind _ b), 0, eff a => some (eff (.bind a b))
  | eff (.bind a _), 1, eff b => some (eff (.bind a b))
  | eff (.gen _), 0, stmts ss => some (eff (.gen ss))
  | eff (.catchCause _ h), 0, eff b => some (eff (.catchCause b h))
  | eff (.catchCause b _), 1, eff h => some (eff (.catchCause b h))
  | eff (.catchIf t _ h), 0, eff b => some (eff (.catchIf t b h))
  | eff (.catchIf t b _), 1, eff h => some (eff (.catchIf t b h))
  | eff (.matchCause _ v c), 0, eff b => some (eff (.matchCause b v c))
  | eff (.matchCause b _ c), 1, eff v => some (eff (.matchCause b v c))
  | eff (.matchCause b v _), 2, eff c => some (eff (.matchCause b v c))
  | eff (.onExit _ f), 0, eff b => some (eff (.onExit b f))
  | eff (.onExit b _), 1, eff f => some (eff (.onExit b f))
  | eff (.exit _), 0, eff b => some (eff (.exit b))
  | eff (.uninterruptible _), 0, eff b => some (eff (.uninterruptible b))
  | eff (.interruptible _), 0, eff b => some (eff (.interruptible b))
  | eff (.branch t _ b), 0, eff a => some (eff (.branch t a b))
  | eff (.branch t a _), 1, eff b => some (eff (.branch t a b))
  | eff (.whileLoop i t s _), 0, eff b => some (eff (.whileLoop i t s b))
  | eff (.withFiber _), 0, action a => some (eff (.withFiber a))
  | eff (.scoped _), 0, eff b => some (eff (.scoped b))
  | eff (.acquireRelease _ r), 0, eff a => some (eff (.acquireRelease a r))
  | eff (.acquireRelease a _), 1, eff r => some (eff (.acquireRelease a r))
  | eff (.choose s _ r), 0, eff l => some (eff (.choose s l r))
  | eff (.choose s l _), 1, eff r => some (eff (.choose s l r))
  | eff (.provideLayer _ f b), 0, layer l => some (eff (.provideLayer l f b))
  | eff (.provideLayer l f _), 1, eff b => some (eff (.provideLayer l f b))
  | eff (.provideService k v _), 0, eff b => some (eff (.provideService k v b))
  | layer (.effect k _), 0, eff b => some (layer (.effect k b))
  | layer (.effectDiscard _), 0, eff b => some (layer (.effectDiscard b))
  | layer (.provide _ t), 0, layer s => some (layer (.provide s t))
  | layer (.provide s _), 1, layer t => some (layer (.provide s t))
  | layer (.provideMerge _ t), 0, layer s => some (layer (.provideMerge s t))
  | layer (.provideMerge s _), 1, layer t => some (layer (.provideMerge s t))
  | layer (.merge _ r), 0, layer l => some (layer (.merge l r))
  | layer (.merge l _), 1, layer r => some (layer (.merge l r))
  | layer (.fresh _), 0, layer i => some (layer (.fresh i))
  | layer (.orDie _), 0, layer i => some (layer (.orDie i))
  | layer (.mergeAll _), 0, layers ls => some (layer (.mergeAll ls))
  | layers (.cons _ t), 0, layer h => some (layers (.cons h t))
  | layers (.cons h _), 1, layers t => some (layers (.cons h t))
  | stmts (.cons _ t), 0, stmt h => some (stmts (.cons h t))
  | stmts (.cons h _), 1, stmts t => some (stmts (.cons h t))
  | stmt (.bindYield _), 0, eff e => some (stmt (.bindYield e))
  | stmt (.yieldDiscard _), 0, eff e => some (stmt (.yieldDiscard e))
  | stmt (.ifElse t _ b), 0, stmts a => some (stmt (.ifElse t a b))
  | stmt (.ifElse t a _), 1, stmts b => some (stmt (.ifElse t a b))
  | stmt (.whileTrue _), 0, stmts b => some (stmt (.whileTrue b))
  | action (.fork _ o), 0, eff p => some (action (.fork p o))
  | action (.forkIn _ o s), 0, eff p => some (action (.forkIn p o s))
  | action (.forkScoped _ o), 0, eff p => some (action (.forkScoped p o))
  | action (.raceAll _), 0, effs es => some (action (.raceAll es))
  | effs (.cons _ t), 0, eff h => some (effs (.cons h t))
  | effs (.cons h _), 1, effs t => some (effs (.cons h t))
  | _, _, _ => none

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

mutual
  /-- Every `LayerTerm.ref` under a program, as `(site, target)` pairs in program order, the
  site's path from the root at `p`; the child indices are `Node.child`'s. -/
  def Eff.refSites {Op : Type} (p : List Nat) : Eff Op → List (List Nat × List Nat)
    | .suspend b => Eff.refSites (p ++ [0]) b
    | .bind a b => Eff.refSites (p ++ [0]) a ++ Eff.refSites (p ++ [1]) b
    | .gen ss => Stmts.refSites (p ++ [0]) ss
    | .catchCause b h => Eff.refSites (p ++ [0]) b ++ Eff.refSites (p ++ [1]) h
    | .catchIf _ b h => Eff.refSites (p ++ [0]) b ++ Eff.refSites (p ++ [1]) h
    | .matchCause b v c =>
      Eff.refSites (p ++ [0]) b ++ Eff.refSites (p ++ [1]) v ++ Eff.refSites (p ++ [2]) c
    | .onExit b f => Eff.refSites (p ++ [0]) b ++ Eff.refSites (p ++ [1]) f
    | .exit b => Eff.refSites (p ++ [0]) b
    | .uninterruptible b => Eff.refSites (p ++ [0]) b
    | .interruptible b => Eff.refSites (p ++ [0]) b
    | .branch _ a b => Eff.refSites (p ++ [0]) a ++ Eff.refSites (p ++ [1]) b
    | .whileLoop _ _ _ b => Eff.refSites (p ++ [0]) b
    | .withFiber a => ActionTerm.refSites (p ++ [0]) a
    | .scoped b => Eff.refSites (p ++ [0]) b
    | .acquireRelease a r => Eff.refSites (p ++ [0]) a ++ Eff.refSites (p ++ [1]) r
    | .choose _ l r => Eff.refSites (p ++ [0]) l ++ Eff.refSites (p ++ [1]) r
    | .provideLayer l _ b => LayerTerm.refSites (p ++ [0]) l ++ Eff.refSites (p ++ [1]) b
    | .provideService _ _ b => Eff.refSites (p ++ [0]) b
    | .succeed _ | .fail _ | .failCause _ | .yieldError _ | .sync _ | .perform _ _
    | .yieldNow _ | .callback _ _ | .awaitFiber _ _ | .service _ => []
  def Stmts.refSites {Op : Type} (p : List Nat) : Stmts Op → List (List Nat × List Nat)
    | .nil => []
    | .cons h t => Stmt.refSites (p ++ [0]) h ++ Stmts.refSites (p ++ [1]) t
  def Stmt.refSites {Op : Type} (p : List Nat) : Stmt Op → List (List Nat × List Nat)
    | .bindYield e => Eff.refSites (p ++ [0]) e
    | .yieldDiscard e => Eff.refSites (p ++ [0]) e
    | .ifElse _ a b => Stmts.refSites (p ++ [0]) a ++ Stmts.refSites (p ++ [1]) b
    | .whileTrue b => Stmts.refSites (p ++ [0]) b
    | .ret _ | .breakLoop => []
  def Effs.refSites {Op : Type} (p : List Nat) : Effs Op → List (List Nat × List Nat)
    | .nil => []
    | .cons h t => Eff.refSites (p ++ [0]) h ++ Effs.refSites (p ++ [1]) t
  def ActionTerm.refSites {Op : Type} (p : List Nat) : ActionTerm Op → List (List Nat × List Nat)
    | .fork e _ => Eff.refSites (p ++ [0]) e
    | .forkIn e _ _ => Eff.refSites (p ++ [0]) e
    | .forkScoped e _ => Eff.refSites (p ++ [0]) e
    | .raceAll es => Effs.refSites (p ++ [0]) es
    | .runIn _ _ | .interrupt _ | .interruptScoped _ | .interruptAll _ _ | .awaitAll _
    | .awaitAllFailFast _ | .snapshotChildren | .awaitNewChildren _ | .setContext _
    | .getContext | .getId | .closeScope _ _ => []
  def LayerTerm.refSites {Op : Type} (p : List Nat) : LayerTerm Op → List (List Nat × List Nat)
    | .ref target => [(p, target)]
    | .effect _ b => Eff.refSites (p ++ [0]) b
    | .effectDiscard b => Eff.refSites (p ++ [0]) b
    | .provide s t => LayerTerm.refSites (p ++ [0]) s ++ LayerTerm.refSites (p ++ [1]) t
    | .provideMerge s t => LayerTerm.refSites (p ++ [0]) s ++ LayerTerm.refSites (p ++ [1]) t
    | .merge l r => LayerTerm.refSites (p ++ [0]) l ++ LayerTerm.refSites (p ++ [1]) r
    | .fresh i => LayerTerm.refSites (p ++ [0]) i
    | .orDie i => LayerTerm.refSites (p ++ [0]) i
    | .mergeAll ls => LayerTerms.refSites (p ++ [0]) ls
    | .succeed _ _ => []
  def LayerTerms.refSites {Op : Type} (p : List Nat) : LayerTerms Op → List (List Nat × List Nat)
    | .nil => []
    | .cons h t => LayerTerm.refSites (p ++ [0]) h ++ LayerTerms.refSites (p ++ [1]) t
end

/-! ## Expansion, for typing -/

mutual
  /-- One round of expansion: every `ref` replaced by the layer at its target in `orig`, the
  original program (paths are root-relative, and the compile resolves against the same
  root); a target that names no layer is left as it is. -/
  def Eff.expandRound {Op : Type} (orig : Node Op) : Eff Op → Eff Op
    | .suspend b => .suspend (Eff.expandRound orig b)
    | .bind a b => .bind (Eff.expandRound orig a) (Eff.expandRound orig b)
    | .gen ss => .gen (Stmts.expandRound orig ss)
    | .catchCause b h => .catchCause (Eff.expandRound orig b) (Eff.expandRound orig h)
    | .catchIf t b h => .catchIf t (Eff.expandRound orig b) (Eff.expandRound orig h)
    | .matchCause b v c =>
      .matchCause (Eff.expandRound orig b) (Eff.expandRound orig v) (Eff.expandRound orig c)
    | .onExit b f => .onExit (Eff.expandRound orig b) (Eff.expandRound orig f)
    | .exit b => .exit (Eff.expandRound orig b)
    | .uninterruptible b => .uninterruptible (Eff.expandRound orig b)
    | .interruptible b => .interruptible (Eff.expandRound orig b)
    | .branch t a b => .branch t (Eff.expandRound orig a) (Eff.expandRound orig b)
    | .whileLoop i t s b => .whileLoop i t s (Eff.expandRound orig b)
    | .withFiber a => .withFiber (ActionTerm.expandRound orig a)
    | .scoped b => .scoped (Eff.expandRound orig b)
    | .acquireRelease a r => .acquireRelease (Eff.expandRound orig a) (Eff.expandRound orig r)
    | .choose s l r => .choose s (Eff.expandRound orig l) (Eff.expandRound orig r)
    | .provideLayer l f b => .provideLayer (LayerTerm.expandRound orig l) f (Eff.expandRound orig b)
    | .provideService k v b => .provideService k v (Eff.expandRound orig b)
    | .succeed v => .succeed v
    | .fail e => .fail e
    | .failCause c => .failCause c
    | .yieldError e => .yieldError e
    | .sync t => .sync t
    | .perform op r => .perform op r
    | .yieldNow n => .yieldNow n
    | .callback op r => .callback op r
    | .awaitFiber f m => .awaitFiber f m
    | .service k => .service k
  def Stmts.expandRound {Op : Type} (orig : Node Op) : Stmts Op → Stmts Op
    | .nil => .nil
    | .cons h t => .cons (Stmt.expandRound orig h) (Stmts.expandRound orig t)
  def Stmt.expandRound {Op : Type} (orig : Node Op) : Stmt Op → Stmt Op
    | .bindYield e => .bindYield (Eff.expandRound orig e)
    | .yieldDiscard e => .yieldDiscard (Eff.expandRound orig e)
    | .ifElse t a b => .ifElse t (Stmts.expandRound orig a) (Stmts.expandRound orig b)
    | .whileTrue b => .whileTrue (Stmts.expandRound orig b)
    | .ret v => .ret v
    | .breakLoop => .breakLoop
  def Effs.expandRound {Op : Type} (orig : Node Op) : Effs Op → Effs Op
    | .nil => .nil
    | .cons h t => .cons (Eff.expandRound orig h) (Effs.expandRound orig t)
  def ActionTerm.expandRound {Op : Type} (orig : Node Op) : ActionTerm Op → ActionTerm Op
    | .fork e o => .fork (Eff.expandRound orig e) o
    | .forkIn e o s => .forkIn (Eff.expandRound orig e) o s
    | .forkScoped e o => .forkScoped (Eff.expandRound orig e) o
    | .raceAll es => .raceAll (Effs.expandRound orig es)
    | .runIn t s => .runIn t s
    | .interrupt t => .interrupt t
    | .interruptScoped t => .interruptScoped t
    | .interruptAll ts who => .interruptAll ts who
    | .awaitAll ts => .awaitAll ts
    | .awaitAllFailFast ts => .awaitAllFailFast ts
    | .snapshotChildren => .snapshotChildren
    | .awaitNewChildren s => .awaitNewChildren s
    | .setContext c => .setContext c
    | .getContext => .getContext
    | .getId => .getId
    | .closeScope s e => .closeScope s e
  def LayerTerm.expandRound {Op : Type} (orig : Node Op) : LayerTerm Op → LayerTerm Op
    | .ref target =>
      match orig.layerAt target with
      | some l => l
      | none => .ref target
    | .effect k b => .effect k (Eff.expandRound orig b)
    | .effectDiscard b => .effectDiscard (Eff.expandRound orig b)
    | .provide s t => .provide (LayerTerm.expandRound orig s) (LayerTerm.expandRound orig t)
    | .provideMerge s t => .provideMerge (LayerTerm.expandRound orig s) (LayerTerm.expandRound orig t)
    | .merge l r => .merge (LayerTerm.expandRound orig l) (LayerTerm.expandRound orig r)
    | .fresh i => .fresh (LayerTerm.expandRound orig i)
    | .orDie i => .orDie (LayerTerm.expandRound orig i)
    | .mergeAll ls => .mergeAll (LayerTerms.expandRound orig ls)
    | .succeed k v => .succeed k v
  def LayerTerms.expandRound {Op : Type} (orig : Node Op) : LayerTerms Op → LayerTerms Op
    | .nil => .nil
    | .cons h t => .cons (LayerTerm.expandRound orig h) (LayerTerms.expandRound orig t)
end

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

mutual
  /-- The path of every layer under a program, in program order (a layer before the layers
  inside it), the root at `p`. -/
  def Eff.layerPaths {Op : Type} (p : List Nat) : Eff Op → List (List Nat)
    | .suspend b => Eff.layerPaths (p ++ [0]) b
    | .bind a b => Eff.layerPaths (p ++ [0]) a ++ Eff.layerPaths (p ++ [1]) b
    | .gen ss => Stmts.layerPaths (p ++ [0]) ss
    | .catchCause b h => Eff.layerPaths (p ++ [0]) b ++ Eff.layerPaths (p ++ [1]) h
    | .catchIf _ b h => Eff.layerPaths (p ++ [0]) b ++ Eff.layerPaths (p ++ [1]) h
    | .matchCause b v c =>
      Eff.layerPaths (p ++ [0]) b ++ Eff.layerPaths (p ++ [1]) v ++ Eff.layerPaths (p ++ [2]) c
    | .onExit b f => Eff.layerPaths (p ++ [0]) b ++ Eff.layerPaths (p ++ [1]) f
    | .exit b => Eff.layerPaths (p ++ [0]) b
    | .uninterruptible b => Eff.layerPaths (p ++ [0]) b
    | .interruptible b => Eff.layerPaths (p ++ [0]) b
    | .branch _ a b => Eff.layerPaths (p ++ [0]) a ++ Eff.layerPaths (p ++ [1]) b
    | .whileLoop _ _ _ b => Eff.layerPaths (p ++ [0]) b
    | .withFiber a => ActionTerm.layerPaths (p ++ [0]) a
    | .scoped b => Eff.layerPaths (p ++ [0]) b
    | .acquireRelease a r => Eff.layerPaths (p ++ [0]) a ++ Eff.layerPaths (p ++ [1]) r
    | .choose _ l r => Eff.layerPaths (p ++ [0]) l ++ Eff.layerPaths (p ++ [1]) r
    | .provideLayer l _ b => LayerTerm.layerPaths (p ++ [0]) l ++ Eff.layerPaths (p ++ [1]) b
    | .provideService _ _ b => Eff.layerPaths (p ++ [0]) b
    | .succeed _ | .fail _ | .failCause _ | .yieldError _ | .sync _ | .perform _ _
    | .yieldNow _ | .callback _ _ | .awaitFiber _ _ | .service _ => []
  def Stmts.layerPaths {Op : Type} (p : List Nat) : Stmts Op → List (List Nat)
    | .nil => []
    | .cons h t => Stmt.layerPaths (p ++ [0]) h ++ Stmts.layerPaths (p ++ [1]) t
  def Stmt.layerPaths {Op : Type} (p : List Nat) : Stmt Op → List (List Nat)
    | .bindYield e => Eff.layerPaths (p ++ [0]) e
    | .yieldDiscard e => Eff.layerPaths (p ++ [0]) e
    | .ifElse _ a b => Stmts.layerPaths (p ++ [0]) a ++ Stmts.layerPaths (p ++ [1]) b
    | .whileTrue b => Stmts.layerPaths (p ++ [0]) b
    | .ret _ | .breakLoop => []
  def Effs.layerPaths {Op : Type} (p : List Nat) : Effs Op → List (List Nat)
    | .nil => []
    | .cons h t => Eff.layerPaths (p ++ [0]) h ++ Effs.layerPaths (p ++ [1]) t
  def ActionTerm.layerPaths {Op : Type} (p : List Nat) : ActionTerm Op → List (List Nat)
    | .fork e _ => Eff.layerPaths (p ++ [0]) e
    | .forkIn e _ _ => Eff.layerPaths (p ++ [0]) e
    | .forkScoped e _ => Eff.layerPaths (p ++ [0]) e
    | .raceAll es => Effs.layerPaths (p ++ [0]) es
    | .runIn _ _ | .interrupt _ | .interruptScoped _ | .interruptAll _ _ | .awaitAll _
    | .awaitAllFailFast _ | .snapshotChildren | .awaitNewChildren _ | .setContext _
    | .getContext | .getId | .closeScope _ _ => []
  def LayerTerm.layerPaths {Op : Type} (p : List Nat) : LayerTerm Op → List (List Nat)
    | .effect _ b => p :: Eff.layerPaths (p ++ [0]) b
    | .effectDiscard b => p :: Eff.layerPaths (p ++ [0]) b
    | .provide s t => p :: (LayerTerm.layerPaths (p ++ [0]) s ++ LayerTerm.layerPaths (p ++ [1]) t)
    | .provideMerge s t =>
      p :: (LayerTerm.layerPaths (p ++ [0]) s ++ LayerTerm.layerPaths (p ++ [1]) t)
    | .merge l r => p :: (LayerTerm.layerPaths (p ++ [0]) l ++ LayerTerm.layerPaths (p ++ [1]) r)
    | .fresh i => p :: LayerTerm.layerPaths (p ++ [0]) i
    | .orDie i => p :: LayerTerm.layerPaths (p ++ [0]) i
    | .mergeAll ls => p :: LayerTerms.layerPaths (p ++ [0]) ls
    | .succeed _ _ => [p]
    | .ref _ => [p]
  def LayerTerms.layerPaths {Op : Type} (p : List Nat) : LayerTerms Op → List (List Nat)
    | .nil => []
    | .cons h t => LayerTerm.layerPaths (p ++ [0]) h ++ LayerTerms.layerPaths (p ++ [1]) t
end

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
