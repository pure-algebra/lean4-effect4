/-
Contract: the hand `Canonical` instances the generator emits, written the way it writes them.

Frozen: the four acceptance shapes of `docs/research/2026-09-04-cas-trait-plan.md` §4 that a
lane may still have to write by hand — an all-nullary sum, a structure, and a mutual pair —
each with `shapeDoc`, `toVal`, `ofVal` and the three laws, plus the tactic scripts that close
them. The census entry of the facts note §6 lives here as `Templates.entry`, and its payload
digest `8fab16…61fa` is the receipt that the structure template writes the frozen bytes.

Why this is a battery and not a library module: nothing in `src/` consumes these carriers.
They are the worked examples the generator's output is read against, and the templates a lane
copies when `Effect4Gen` refuses a type — today a bare parameterised one (`REPORT-G.md`, the
open item lane X hit on `GSet α`, `Fact L C` and `Vector L C`). `Test/Store/NodeContract.lean`
files `Templates.Entry` as `export` content and addresses it.

Dropped from the spike's `Test/Store/Templates.lean`: the hand `Canonical Float64` and
`Canonical Json`. Both are derived now, in `src/Effect4/Store/Derived/Json.lean`, and a second
instance in the same environment is an ambiguity rather than a template. The nested-recursion
receipts that exercised them are kept below against the derived instance; the printer and
document receipts moved with the instance and are that module's own guards
(`Store/Derived/Json.lean`, the `JsonAcceptance` section).
-/

import Effect4.Store.Canonical
import Effect4.Store.Derived.Json

set_option autoImplicit false

namespace Effect4.Store

namespace Templates

/-! ## An all-nullary sum

`shapeDoc` is a `sum` of empty field lists, `toVal` a `ctor` frame with no arguments at the
constructor's declaration position, `ofVal` one alternative per position; `ofVal_toVal` is
`cases` then `rfl`, `ofVal_exact` a `split` closed by `injection`, and `fits` is `decide`. -/

/-- The declaration kinds the census recognises (`StdLib/Entry.lean`, `ExportKind`). -/
inductive ExportKind where
  | const
  | function
  | class_
  | interface
  | type
  | namespace_
deriving DecidableEq, Repr, Inhabited

namespace ExportKind

def shapeDoc : ShapeDoc :=
  ⟨.sum "ExportKind"
    [("const", []), ("function", []), ("class_", []), ("interface", []), ("type", []),
     ("namespace_", [])], []⟩

def toVal : ExportKind → Val
  | .const => .ctor 0 []
  | .function => .ctor 1 []
  | .class_ => .ctor 2 []
  | .interface => .ctor 3 []
  | .type => .ctor 4 []
  | .namespace_ => .ctor 5 []

def ofVal : Val → Option ExportKind
  | .ctor 0 [] => some .const
  | .ctor 1 [] => some .function
  | .ctor 2 [] => some .class_
  | .ctor 3 [] => some .interface
  | .ctor 4 [] => some .type
  | .ctor 5 [] => some .namespace_
  | _ => none

theorem ofVal_toVal (a : ExportKind) : ofVal (toVal a) = some a := by
  cases a <;> rfl

theorem ofVal_exact {v : Val} {a : ExportKind} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | exact nomatch h

theorem fits (a : ExportKind) : shapeDoc.accepts (toVal a) = true := by
  cases a <;> decide

instance instCanonical : Canonical ExportKind :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end ExportKind

/-! ## A structure

A structure is a one-case sum whose `toVal` is `ctor 0` over the fields in declaration order.
Composition is through the class: a field of type `F` contributes `(shape F).root` to the
fields and `(shape F).defs` to the table, so `fits` lifts each field's own law with
`acceptsIn_mono_of_subset` into the enclosing table. -/

/-- One export of a pinned module: the shape of the census entry before it gained its
`source : Ref Source` field (`StdLib/Entry.lean`, `Entry`). Its `toVal` is the facts
note §6 payload, so its bytes are `Store/Val.lean`'s `sampleEntry`. -/
structure Entry where
  module : String
  name : String
  kind : ExportKind
  line : Nat
deriving DecidableEq, Repr, Inhabited

namespace Entry

def shapeDoc : ShapeDoc :=
  ⟨.struct "Entry"
    [("module", (shape String).root), ("name", (shape String).root),
     ("kind", (shape ExportKind).root), ("line", (shape Nat).root)],
   (shape String).defs ++ (shape String).defs ++ (shape ExportKind).defs ++ (shape Nat).defs⟩

def toVal (e : Entry) : Val :=
  .ctor 0 [Canonical.toVal e.module, Canonical.toVal e.name, Canonical.toVal e.kind,
    Canonical.toVal e.line]

def ofVal : Val → Option Entry
  | .ctor 0 [m, n, k, l] =>
    match Canonical.ofVal (α := String) m, Canonical.ofVal (α := String) n,
        Canonical.ofVal (α := ExportKind) k, Canonical.ofVal (α := Nat) l with
    | some m, some n, some k, some l => some ⟨m, n, k, l⟩
    | _, _, _, _ => none
  | _ => none

theorem ofVal_toVal (e : Entry) : ofVal (toVal e) = some e := by
  obtain ⟨m, n, k, l⟩ := e
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {e : Entry} (h : ofVal v = some e) : v = toVal e := by
  unfold ofVal at h
  split at h
  · next m n k l =>
    split at h
    · next m' n' k' l' hm hn hk hl =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact hm, Canonical.ofVal_exact hn, Canonical.ofVal_exact hk,
        Canonical.ofVal_exact hl]
    · exact nomatch h
  · exact nomatch h

theorem fits (e : Entry) : shapeDoc.accepts (toVal e) = true := by
  obtain ⟨m, n, k, l⟩ := e
  apply accepts_struct
  refine acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_cons _ _ _ _ _ _ ?_
    (acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_nil _))))
  · exact acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits m)
  · exact acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits n)
  · exact acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits k)
  · exact acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits l)

instance instCanonical : Canonical Entry :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end Entry

/-! ## A mutual pair

Two inductives, one shared table, each member named by `named` from the other. The
definitions and the round-trip theorems are mutual and structural; exactness is one induction
on `Val` proving both members at once, because `Val.ind` does not recurse through the pair. -/

mutual
/-- A labelled node with a forest of children. -/
inductive Tree where
  | node (label : Nat) (children : Forest)
/-- A list of trees, as its own inductive. -/
inductive Forest where
  | nil
  | cons (t : Tree) (f : Forest)
end

deriving instance DecidableEq for Tree, Forest

namespace TreeForest

def treeShape : Shape :=
  .sum "Tree" [("node", [("label", (shape Nat).root), ("children", .named "Forest")])]

def forestShape : Shape :=
  .sum "Forest" [("nil", []), ("cons", [("t", .named "Tree"), ("f", .named "Forest")])]

/-- One table for the block, then the field types' tables. -/
def defs : List (String × Shape) :=
  ("Tree", treeShape) :: ("Forest", forestShape) :: (shape Nat).defs

mutual
def toValT : Tree → Val
  | .node n f => .ctor 0 [Canonical.toVal n, toValF f]
def toValF : Forest → Val
  | .nil => .ctor 0 []
  | .cons t f => .ctor 1 [toValT t, toValF f]
end

mutual
def ofValT : Val → Option Tree
  | .ctor 0 [n, f] =>
    match Canonical.ofVal (α := Nat) n, ofValF f with
    | some n, some f => some (.node n f)
    | _, _ => none
  | _ => none
def ofValF : Val → Option Forest
  | .ctor 0 [] => some .nil
  | .ctor 1 [t, f] =>
    match ofValT t, ofValF f with
    | some t, some f => some (.cons t f)
    | _, _ => none
  | _ => none
end

mutual
theorem ofValT_toValT (t : Tree) : ofValT (toValT t) = some t := by
  cases t with
  | node n f => simp [toValT, ofValT, Canonical.ofVal_toVal, ofValF_toValF f]
termination_by structural t
theorem ofValF_toValF (f : Forest) : ofValF (toValF f) = some f := by
  cases f with
  | nil => rfl
  | cons t f => simp [toValF, ofValF, ofValT_toValT t, ofValF_toValF f]
termination_by structural f
end

def ExactT (v : Val) : Prop := ∀ t : Tree, ofValT v = some t → v = toValT t
def ExactF (v : Val) : Prop := ∀ f : Forest, ofValF v = some f → v = toValF f

theorem exact_aux : ∀ v : Val, ExactT v ∧ ExactF v := by
  intro v
  induction v using Val.ind with
  | unit => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | bool b => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | nat n => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | str s => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | bytes bs => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | list xs _ => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | pair a b _ _ => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | none => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | some a _ => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | ref k d => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  | ctor i args ih =>
    constructor
    · intro t h
      unfold ofValT at h
      split at h
      all_goals first
        | (rename_i n f heq
           injection heq with hi hargs
           subst hi hargs
           split at h
           · rename_i n' f' hn hf
             injection h with h
             subst h
             simp only [toValT]
             rw [Canonical.ofVal_exact hn, (ih f (by simp)).2 f' hf]
           · exact nomatch h)
        | exact nomatch h
    · intro fo h
      unfold ofValF at h
      split at h
      all_goals first
        | (rename_i heq
           injection heq with hi hargs
           subst hi hargs
           injection h with h
           subst h
           rfl)
        | (rename_i t f heq
           injection heq with hi hargs
           subst hi hargs
           split at h
           · rename_i t' f' ht hf
             injection h with h
             subst h
             simp only [toValF]
             rw [(ih t (by simp)).1 t' ht, (ih f (by simp)).2 f' hf]
           · exact nomatch h)
        | exact nomatch h

theorem ofValT_exact {v : Val} {t : Tree} (h : ofValT v = some t) : v = toValT t :=
  (exact_aux v).1 t h

theorem ofValF_exact {v : Val} {f : Forest} (h : ofValF v = some f) : v = toValF f :=
  (exact_aux v).2 f h

theorem mem_tree : ("Tree", treeShape) ∈ defs := List.Mem.head _
theorem mem_forest : ("Forest", forestShape) ∈ defs := List.Mem.tail _ (List.Mem.head _)

mutual
theorem fitsT (t : Tree) : acceptsIn defs (.named "Tree") (toValT t) = true := by
  apply accepts_named_of_mem _ _ treeShape _ mem_tree
  cases t with
  | node n f =>
    exact acceptsAt_sum _ _ _ 0 "node" _ _ rfl (acceptsFields_cons _ _ _ _ _ _
      (acceptsIn_mono_of_subset (fun p hp => List.Mem.tail _ (List.Mem.tail _ hp)) _ _
        (Canonical.fits n))
      (acceptsFields_cons _ _ _ _ _ _ (fitsF f) (acceptsFields_nil _)))
termination_by structural t
theorem fitsF (f : Forest) : acceptsIn defs (.named "Forest") (toValF f) = true := by
  apply accepts_named_of_mem _ _ forestShape _ mem_forest
  cases f with
  | nil => exact acceptsAt_sum _ _ _ 0 "nil" [] [] rfl (acceptsFields_nil _)
  | cons t f =>
    exact acceptsAt_sum _ _ _ 1 "cons" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsT t)
      (acceptsFields_cons _ _ _ _ _ _ (fitsF f) (acceptsFields_nil _)))
termination_by structural f
end

end TreeForest

instance Tree.instCanonical : Canonical Tree :=
  ⟨⟨.named "Tree", TreeForest.defs⟩, TreeForest.toValT, TreeForest.ofValT,
    TreeForest.ofValT_toValT, TreeForest.ofValT_exact, TreeForest.fitsT⟩

instance Forest.instCanonical : Canonical Forest :=
  ⟨⟨.named "Forest", TreeForest.defs⟩, TreeForest.toValF, TreeForest.ofValF,
    TreeForest.ofValF_toValF, TreeForest.ofValF_exact, TreeForest.fitsF⟩

/-! ## The receipts of the facts note §6, on the templates -/

/-- The census entry of the facts note: `Effect.gen`, a `const` at line 1947. -/
def entry : Entry := ⟨"Effect", "gen", .const, 1947⟩

-- The structure template writes exactly the value tree the substrate pins.
#guard Canonical.toVal entry = sampleEntry
#guard Canonical.encode entry = Val.encode sampleEntry
#guard (Canonical.encode entry).length = 74
#guard (Canonical.digest entry).hex =
  "8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa"
#guard Canonical.decode (Canonical.encode entry) = some entry
-- The printer follows the same table: fields in declaration order, an all-nullary sum as its
-- constructor's name, a `Nat` as a binary64 number.
#guard Canonical.print entry =
  .obj [("module", .str "Effect"), ("name", .str "gen"), ("kind", .str "const"),
    ("line", Arch.Json.ofNat 1947)]
#guard Canonical.print ExportKind.const = .str "const"
#guard Canonical.encode ExportKind.const = [10, 0, 0, 0, 0, 0, 0, 0, 9, 2, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (Canonical.document Entry).references.length = 0

/-- A forest touching both members of the mutual block. -/
def forest : Forest := .cons (.node 1 (.cons (.node 2 .nil) .nil)) (.cons (.node 3 .nil) .nil)

#guard Canonical.decode (Canonical.encode forest) = some forest
-- The two members are different types with different shapes: a forest is not a tree.
#guard Canonical.decode (α := Tree) (Canonical.encode forest) = none
#guard (Canonical.encode (Tree.node 7 .nil)).length = 9 + 9 + 10 + 18

end Templates

/-! ## The nested recursion, on the derived instance

`Json` recurses through `List Json` and through `List (String × Json)`, two levels below its
constructor. The hand template that proved it retired with the landing; these are the same
round trip and refusal on `Store/Derived/Json.lean`'s generated instance. -/

/-- A JSON value touching every constructor. -/
def templateJson : Effect4.Json :=
  .obj [("a", .arr [.null, .bool true, .number ⟨3⟩, .str "x"]), ("b", .obj [])]

#guard Canonical.decode (Canonical.encode templateJson) = some templateJson
#guard Canonical.decode (α := Effect4.Json) (Canonical.encode (Effect4.Json.arr [.null]) ++ [0])
  = none

/-! ## Axiom receipts -/

#print axioms Templates.ExportKind.ofVal_toVal
#print axioms Templates.ExportKind.ofVal_exact
#print axioms Templates.ExportKind.fits
#print axioms Templates.ExportKind.instCanonical
#print axioms Templates.Entry.ofVal_toVal
#print axioms Templates.Entry.ofVal_exact
#print axioms Templates.Entry.fits
#print axioms Templates.Entry.instCanonical
#print axioms Templates.TreeForest.mem_tree
#print axioms Templates.TreeForest.mem_forest
#print axioms Templates.TreeForest.ofValT_toValT
#print axioms Templates.TreeForest.ofValF_toValF
#print axioms Templates.TreeForest.exact_aux
#print axioms Templates.TreeForest.ofValT_exact
#print axioms Templates.TreeForest.fitsT
#print axioms Templates.TreeForest.fitsF
#print axioms Templates.Tree.instCanonical
#print axioms Templates.Forest.instCanonical
#print axioms Templates.entry
#print axioms Templates.forest
#print axioms templateJson

end Effect4.Store
