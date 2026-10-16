import Effect4.Program.Typed
import Effect4.Program.Fold
import Effect4.Codegen.Types
import Effect4.Store.Carrier.Image
import TypeScript.Render

/-! # A finite probe of recursive types (decisions row 400)

Run: `lake env lean docs/research/2026-10-15-recursive-types/probes/Recursive.lean`.

Recursive types enter as rows 124 and 158 say: a table of the application's type declarations,
and `Ty.app name []` as a reference into it. No `Ty` constructor is added. This probe models the
four judgments the landing changes, on the real `Ty` and `Val`, beside the core:

1. **Membership** (`fitsIn`): a declared name unfolds to its body. Recursion is on the value:
   between two value constructors at most `Δ.length` names unfold, so a guarded table needs no
   more, and an unguarded one (`type A = A`) answers `false`.
2. **Guardedness** (`guarded`): no declaration reaches itself through unions and names alone.
3. **Inhabitance** (`inhabitedNames`): the least fixed point over the table, by iteration.
4. **The faces**: the TypeScript declarations through the existing printer; the Lean carrier of a
   recursive inductive, an exact `Image` written by structural recursion, as a deriver would.

The checker here takes fuel, and the probe checks that twice the fuel changes no answer. The
landing's checker is well founded on `(size of the value, unfold budget, size of the type)`. -/

open Effect4 Effect4.Program Effect4.Store Effect4.Codegen

namespace RecProbe

/-- **The application's type declarations**: a name and its body, monomorphic. A body refers to a
declaration, itself included, as `.app name []`. -/
abbrev Decls := List (String × Ty)

/-! ## 1. Membership: a declared name unfolds at a value -/

-- A value's size: one per node. The fuel bound reads it.
mutual
def vsize : Val → Nat
  | .list xs => 1 + vsizeList xs
  | .pair a b => 1 + vsize a + vsize b
  | .some a => 1 + vsize a
  | .ctor _ args => 1 + vsizeList args
  | _ => 1
def vsizeList : List Val → Nat
  | [] => 0
  | x :: xs => vsize x + vsizeList xs
end

/-- A type's size, as a fold. -/
def tsizeAlg : TyAlgebra (fun _ => Nat) where
  ty_never := 1
  ty_unit := 1
  ty_nat := 1
  ty_int := 1
  ty_string := 1
  ty_bool := 1
  ty_handle _ := 1
  ty_option a := a + 1
  ty_list a := a + 1
  ty_prod a b := a + b + 1
  ty_except a b := a + b + 1
  ty_exitOf a b := a + b + 1
  ty_causeOf a := a + 1
  ty_fiberOf a b := a + b + 1
  ty_union a b := a + b + 1
  ty_lit _ := 1
  ty_refOf a := a + 1
  ty_deferredOf a b := a + b + 1
  ty_var _ := 1
  ty_unknown := 1
  ty_record fs := fs.foldr (fun f acc => f.2.2 + acc) 1
  ty_map a b := a + b + 1
  ty_tuple ts := ts.foldr (· + ·) 1
  ty_app _ xs := xs.foldr (· + ·) 1
  ty_null := 1
  ty_undefined := 1
  ty_number := 1
  ty_bytes := 1
  ty_contextOf _ := 1

def tsize (t : Ty) : Nat := cata_ty tsizeAlg t

/-- **Membership under a table.** `budget` counts the names that may still unfold before the next
value constructor; each value constructor restores it to `Δ.length`. The other arms are
`Val.hasTy`'s, with the table carried into every child. -/
def fitsIn (Δ : Decls) : Nat → Nat → Val → Ty → Bool
  | 0, _, _, _ => false
  | k + 1, budget, v, t =>
    match t with
    | .app n [] =>
      match Δ.lookup n with
      | some body => match budget with
        | 0 => false
        | b + 1 => fitsIn Δ k b v body
      | none => Val.hasTy v t
    | .union l r => fitsIn Δ k budget v l || fitsIn Δ k budget v r
    | .option inner => match v with
      | .none => true
      | .some x => fitsIn Δ k Δ.length x inner
      | _ => false
    | .list item => match v with
      | .list xs => xs.all fun x => fitsIn Δ k Δ.length x item
      | _ => false
    | .prod a b => match v with
      | .list [x, y] => fitsIn Δ k Δ.length x a && fitsIn Δ k Δ.length y b
      | _ => false
    | .record fs => match recordParts? v with
      | some (ns, xs) =>
        namedHasTy (Ty.canon (fs.map fun (n, o, ft) => (n, o, fun x => fitsIn Δ k Δ.length x ft)))
          ns xs
      | none => false
    | .map key value => match v with
      | .list es => entriesHasTy (fun a => fitsIn Δ k Δ.length a key)
          (fun x => fitsIn Δ k Δ.length x value) es
      | _ => false
    | _ => Val.hasTy v t

/-- The largest body in the table. -/
def maxBody (Δ : Decls) : Nat := Δ.foldr (fun d acc => max (tsize d.2) acc) 0

/-- Enough fuel: every path consumes a value node at least once per `Δ.length + 1` unfoldings,
and walks at most one type between them. -/
def fuelFor (Δ : Decls) (v : Val) (t : Ty) : Nat :=
  (vsize v + 1) * (Δ.length + 1) * (max (tsize t) (maxBody Δ) + 1) + 1

/-- A value fits a type under the table. -/
def fits (Δ : Decls) (v : Val) (t : Ty) : Bool := fitsIn Δ (fuelFor Δ v t) Δ.length v t

/-- The same question at twice the fuel: the probe's check that the bound suffices. -/
def fits2 (Δ : Decls) (v : Val) (t : Ty) : Bool := fitsIn Δ (2 * fuelFor Δ v t) Δ.length v t

/-! ## 2. Guardedness: no declaration reaches itself without a value constructor -/

/-- The names a type reaches at its head, through unions only. -/
def headAlg : TyAlgebra (fun _ => List String) where
  ty_never := []
  ty_unit := []
  ty_nat := []
  ty_int := []
  ty_string := []
  ty_bool := []
  ty_handle _ := []
  ty_option _ := []
  ty_list _ := []
  ty_prod _ _ := []
  ty_except _ _ := []
  ty_exitOf _ _ := []
  ty_causeOf _ := []
  ty_fiberOf _ _ := []
  ty_union a b := a ++ b
  ty_lit _ := []
  ty_refOf _ := []
  ty_deferredOf _ _ := []
  ty_var _ := []
  ty_unknown := []
  ty_record _ := []
  ty_map _ _ := []
  ty_tuple _ := []
  ty_app n xs := if xs.isEmpty then [n] else []
  ty_null := []
  ty_undefined := []
  ty_number := []
  ty_bytes := []
  ty_contextOf _ := []

def heads (t : Ty) : List String := cata_ty headAlg t

/-- The names reachable at the head from `n` in `k` steps. -/
def headReach (Δ : Decls) : Nat → List String → List String
  | 0, seen => seen
  | k + 1, seen =>
    let next := seen.flatMap fun n => (Δ.lookup n).map heads |>.getD []
    let seen' := seen ++ next.filter (!seen.contains ·)
    if seen'.length == seen.length then seen else headReach Δ k seen'

/-- **Guarded**: no declaration reaches itself at its head. Every cycle passes a value
constructor, so membership consumes the value between two visits of one name. -/
def guarded (Δ : Decls) : Bool :=
  Δ.all fun (n, body) => !(headReach Δ Δ.length (heads body)).contains n

/-! ## 3. Inhabitance: the least fixed point -/

/-- Inhabitance of a type, given the declared names known inhabited. -/
def inhabAlg (Δ : Decls) (known : List String) : TyAlgebra (fun _ => Bool) where
  ty_never := false
  ty_unit := true
  ty_nat := true
  ty_int := true
  ty_string := true
  ty_bool := true
  ty_handle _ := true
  ty_option _ := true
  ty_list _ := true
  ty_prod a b := a && b
  ty_except a b := a || b
  ty_exitOf _ _ := true
  ty_causeOf _ := true
  ty_fiberOf _ _ := true
  ty_union a b := a || b
  ty_lit _ := true
  ty_refOf _ := true
  ty_deferredOf _ _ := true
  ty_var _ := false
  ty_unknown := true
  ty_record fs := fs.all fun f => f.2.1 || f.2.2
  ty_map _ _ := true
  ty_tuple ts := ts.all id
  ty_app n xs := if (Δ.lookup n).isSome && xs.isEmpty then known.contains n else true
  ty_null := true
  ty_undefined := true
  ty_number := true
  ty_bytes := true
  ty_contextOf _ := true

/-- The inhabited declarations: iterate from none known; the table's length bounds the rounds. -/
def inhabitedNames (Δ : Decls) : List String :=
  (List.range (Δ.length + 1)).foldl (fun known _ =>
    Δ.filterMap fun (n, body) => if cata_ty (inhabAlg Δ known) body then some n else none) []

/-! ## The sample tables -/

def rec (fs : List (String × Ty)) : Ty := .record (fs.map fun (n, t) => (n, false, t))

/-- A tree: a leaf, or a node with a label and its children. -/
def treeDecls : Decls :=
  [("Tree", .union (rec [("_tag", .lit "leaf")])
      (rec [("_tag", .lit "node"), ("children", .list (.app "Tree" [])), ("label", .string)]))]

/-- A linked list of integers. -/
def listDecls : Decls :=
  [("IntList", .union (rec [("_tag", .lit "nil")])
      (rec [("_tag", .lit "cons"), ("head", .int), ("tail", .app "IntList" [])]))]

/-- JSON itself: the type of every JSON value. -/
def jsonDecls : Decls :=
  [("Json", .union .null (.union .bool (.union .number (.union .string
      (.union (.list (.app "Json" [])) (.map .string (.app "Json" [])))))))]

/-- Two declarations that refer to each other: an expression holds statements, a statement
holds expressions. -/
def mutualDecls : Decls :=
  [ ("Expr", .union (rec [("_tag", .lit "lit"), ("value", .nat)])
      (rec [("_tag", .lit "block"), ("body", .list (.app "Stmt" []))]))
  , ("Stmt", .union (rec [("_tag", .lit "eval"), ("expr", .app "Expr" [])])
      (rec [("_tag", .lit "let"), ("name", .string), ("value", .app "Expr" [])])) ]

/-- Red: a name that is itself. -/
def selfDecls : Decls := [("A", .app "A" [])]

/-- Red: a name at its own head, beside a string. -/
def headDecls : Decls := [("B", .union (.app "B" []) .string)]

/-- Red: guarded but uninhabited: every value needs a further value. -/
def streamDecls : Decls := [("Stream", rec [("head", .nat), ("next", .app "Stream" [])])]

/-- Two names at each other's heads, through unions. -/
def cycleDecls : Decls := [("C", .union (.app "D" []) .nat), ("D", .union (.app "C" []) .string)]

/-! ## Sample values, in the record frame -/

def recV (fs : List (String × Val)) : Val :=
  .ctor 0 [.list (fs.map fun f => .str f.1), .list (fs.map (·.2))]

def leafV : Val := recV [("_tag", .str "leaf")]
def nodeV (label : String) (children : List Val) : Val :=
  recV [("_tag", .str "node"), ("children", .list children), ("label", .str label)]

def tree3 : Val := nodeV "root" [leafV, nodeV "mid" [leafV], leafV]
/-- Red: a child that is a string, deep inside. -/
def treeBad : Val := nodeV "root" [leafV, nodeV "mid" [.str "oops"]]

def consV (h : Int) (t : Val) : Val :=
  recV [("_tag", .str "cons"), ("head", if h < 0 then .negInt (h.natAbs - 1) else .nat h.toNat),
    ("tail", t)]
def nilV : Val := recV [("_tag", .str "nil")]

def jsonV : Val := .list [.none, .bool true, .nat 3, .str "x",
  .list [.ctor 0 [], .list [.pair (.str "k") (.str "v")]]]

def exprV : Val :=
  recV [("_tag", .str "block"), ("body", .list
    [recV [("_tag", .str "let"), ("name", .str "x"), ("value", recV [("_tag", .str "lit"), ("value", .nat 1)])],
     recV [("_tag", .str "eval"), ("expr", recV [("_tag", .str "lit"), ("value", .nat 2)])]])]

/-- A finite cut of the stream type's values: every one ends, so none fits. -/
def streamV : Val := recV [("head", .nat 1), ("next", recV [("head", .nat 2), ("next", .unit)])]

/-! ## The finite evaluations -/

def tree : Ty := .app "Tree" []

-- 1. membership
#guard fits treeDecls tree3 tree
#guard fits treeDecls leafV tree
#guard !fits treeDecls treeBad tree
#guard fits listDecls (consV 1 (consV (-2) nilV)) (.app "IntList" [])
#guard !fits listDecls (consV 1 (.str "end")) (.app "IntList" [])
#guard fits mutualDecls exprV (.app "Expr" [])
#guard !fits mutualDecls exprV (.app "Stmt" [])
#guard !fits streamDecls streamV (.app "Stream" [])
-- the red tables answer, and no value fits a name that is itself
#guard !fits selfDecls (.str "x") (.app "A" [])
#guard fits headDecls (.str "x") (.app "B" [])
#guard fits cycleDecls (.nat 1) (.app "C" []) && fits cycleDecls (.str "s") (.app "C" [])
-- the fuel bound suffices: twice the fuel changes no answer on any sample
#guard [(treeDecls, tree3, tree), (treeDecls, treeBad, tree),
    (listDecls, consV 1 (consV (-2) nilV), .app "IntList" []),
    (mutualDecls, exprV, .app "Expr" []), (selfDecls, .str "x", .app "A" []),
    (cycleDecls, .str "s", .app "C" [])].all fun (Δ, v, t) => fits Δ v t == fits2 Δ v t

-- 2. guardedness
#guard [treeDecls, listDecls, jsonDecls, mutualDecls, streamDecls].all guarded
#guard ![selfDecls, headDecls, cycleDecls].any guarded

-- 3. inhabitance: the least fixed point
#guard inhabitedNames treeDecls == ["Tree"]
#guard inhabitedNames mutualDecls == ["Expr", "Stmt"]
#guard inhabitedNames streamDecls == []
#guard inhabitedNames selfDecls == []

/-! ## 4a. The TypeScript face: one alias per declaration, through the existing printer

`Types.ofTy` prints no `app` today (`src/Effect4/Codegen/Types.lean`). A declared name prints as
its name, as a handle does, so the probe prints the body with each declared name as a handle. -/

/-- A declared name as a handle of its name; any other application as it is. -/
def nameApp (Δ : Decls) (n : String) (xs : List Ty) : Ty :=
  if (Δ.lookup n).isSome && xs.isEmpty then .handle n else .app n xs

def nameAlg (Δ : Decls) : TyAlgebra TySelfCarrier := { TyAlgebra.id with ty_app := nameApp Δ }

def asHandles (Δ : Decls) (t : Ty) : Ty := cata_ty (nameAlg Δ) t

/-- `type Name = body`, for each declaration. -/
def declText (Δ : Decls) : List String :=
  Δ.map fun (n, body) =>
    match Types.ofTy (asHandles Δ body) with
    | some x => s!"export type {n} = {TypeScript.Render.type TypeScript.house0 x}"
    | none => s!"// {n}: no spelling"

#eval IO.println (String.intercalate "\n" (declText treeDecls ++ declText listDecls ++
  declText jsonDecls ++ declText mutualDecls))

/-! ## 4b. The Lean face: a recursive inductive with its exact image, written by recursion

`Model.alg` gives `app` the empty carrier. A recursive declaration's carrier is a Lean
inductive, and its image cannot come from the fold, since the fold would have to tie the knot.
So the deriver writes the image by structural recursion, and proves the two laws by induction.
This is that output, by hand. -/

inductive Tree where
  | leaf
  | node (label : String) (children : List Tree)

mutual
def Tree.toVal : Tree → Val
  | .leaf => recV [("_tag", .str "leaf")]
  | .node l cs => recV [("_tag", .str "node"), ("children", .list (Tree.toValList cs)), ("label", .str l)]
def Tree.toValList : List Tree → List Val
  | [] => []
  | t :: ts => Tree.toVal t :: Tree.toValList ts
end

mutual
def Tree.ofVal : Val → Option Tree
  | .ctor 0 [.list [.str "_tag"], .list [.str "leaf"]] => some .leaf
  | .ctor 0 [.list [.str "_tag", .str "children", .str "label"],
      .list [.str "node", .list cs, .str l]] => (Tree.ofValList cs).map (Tree.node l)
  | _ => none
def Tree.ofValList : List Val → Option (List Tree)
  | [] => some []
  | v :: vs => match Tree.ofVal v, Tree.ofValList vs with
    | some t, some ts => some (t :: ts)
    | _, _ => none
end

mutual
theorem Tree.ofVal_toVal : ∀ t : Tree, Tree.ofVal (Tree.toVal t) = some t
  | .leaf => rfl
  | .node l cs => by
    show (Tree.ofValList (Tree.toValList cs)).map (Tree.node l) = some (Tree.node l cs)
    rw [Tree.ofValList_toValList cs]
    rfl
theorem Tree.ofValList_toValList : ∀ ts : List Tree, Tree.ofValList (Tree.toValList ts) = some ts
  | [] => rfl
  | t :: ts => by
    show (match Tree.ofVal (Tree.toVal t), Tree.ofValList (Tree.toValList ts) with
      | some t, some ts => some (t :: ts)
      | _, _ => none) = some (t :: ts)
    rw [Tree.ofVal_toVal t, Tree.ofValList_toValList ts]
end

mutual
theorem Tree.ofVal_exact : ∀ (t : Tree) {v : Val}, Tree.ofVal v = some t → v = Tree.toVal t
  | .leaf, v, h => by
    unfold Tree.ofVal at h
    split at h
    · rfl
    · obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp h
      cases he
    · cases h
  | .node l cs, v, h => by
    unfold Tree.ofVal at h
    split at h
    · cases h
    · obtain ⟨ts, hts, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      rw [Tree.ofValList_exact cs hts]
      rfl
    · cases h
theorem Tree.ofValList_exact : ∀ (ts : List Tree) {vs : List Val},
    Tree.ofValList vs = some ts → vs = Tree.toValList ts
  | [], vs, h => by
    cases vs with
    | nil => rfl
    | cons v vs =>
      unfold Tree.ofValList at h
      split at h
      · cases h
      · cases h
  | t :: ts, vs, h => by
    cases vs with
    | nil => cases h
    | cons v vs =>
      unfold Tree.ofValList at h
      split at h
      · rename_i t' ts' ht hts
        cases h
        rw [Tree.ofVal_exact t ht, Tree.ofValList_exact ts hts]
        rfl
      · cases h
end

/-- **The exact image of the recursive inductive.** -/
def Tree.image : Image Tree :=
  ⟨Tree.toVal, Tree.ofVal, Tree.ofVal_toVal, fun h => Tree.ofVal_exact _ h⟩

def sample : Tree := .node "root" [.leaf, .node "mid" [.leaf], .leaf]

-- the Lean image and the declaration agree: the image's values fit the declared type
#guard Tree.toVal sample == tree3
#guard fits treeDecls (Tree.toVal sample) tree
#guard (Tree.ofVal tree3).isSome && (Tree.ofVal treeBad).isNone

end RecProbe
