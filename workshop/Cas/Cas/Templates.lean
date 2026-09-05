import Cas.Canonical

/-!
# Cas.Templates

Owner: the hand instances the generator will emit, written the way it would write them.

Four acceptance shapes from `docs/research/2026-09-04-cas-trait-plan.md` §4: an all-nullary sum
(`ExportKind`), a structure (`Entry`, whose bytes are the facts note's §6 payload, digest
`8fab16…61fa`), a nested recursion through `List` and `List (String × _)` (`Effect4.Json`,
through `Effect4.Float64`), and a mutual pair (`Tree`/`Forest`). Each carries the five items a
generated file has — `T.shapeDoc`, `T.toVal`, `T.ofVal`, the three laws — and the instance. The
local types restate `Evidence/StdLib/Entry.lean:23-49` rather than import it, because that
module imports the old store.

The fixed scripts (copied into `NOTES.md`): `toVal` is a constructor-indexed `ctor` frame with
the fields' images; `ofVal` is structural on `Val` with one alternative per constructor and
list companions for the nested positions; `ofVal_toVal` is `cases` then `simp` with the
companions and the field instances' `ofVal_toVal`; `ofVal_exact` inducts with `Val.ind`, then
`unfold`/`split` on `ofVal` and closes each alternative with `Option.map_eq_some_iff`, the field
instances' `ofVal_exact` and the companions; `fits` applies `accepts_struct`/`accepts_sum` (or
`accepts_named_of_mem` and `acceptsAt_sum` for a recursive type) and `acceptsFields_cons` down
the field list, each field's law lifted by `acceptsIn_mono_of_subset` into the enclosing table.
Composition is through the class: a field of type `F` contributes `(shape F).root` to the
fields and `(shape F).defs` to the table; a mutual block shares one table and refers to its
members by `named`.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Json Float64)

namespace Templates

/-! ## An all-nullary sum -/

/-- The declaration kinds the census recognises (`Entry.lean:23-30`). -/
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

/-! ## A structure -/

/-- One export of a pinned module (`Entry.lean:44-49`). -/
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

end Templates

/-! ## A structure over a fixed-width scalar: `Float64` -/

namespace Float64Canonical

def shapeDoc : ShapeDoc :=
  ⟨.struct "Float64" [("bits", (shape UInt64).root)], (shape UInt64).defs⟩

def toVal (f : Float64) : Val := .ctor 0 [Canonical.toVal f.bits]

def ofVal : Val → Option Float64
  | .ctor 0 [b] => (Canonical.ofVal (α := UInt64) b).map Float64.mk
  | _ => none

theorem ofVal_toVal (f : Float64) : ofVal (toVal f) = some f := by
  obtain ⟨bits⟩ := f
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {f : Float64} (h : ofVal v = some f) : v = toVal f := by
  unfold ofVal at h
  split at h
  · next b =>
    obtain ⟨bits, hb, hf⟩ := Option.map_eq_some_iff.mp h
    subst hf
    simp only [toVal]
    rw [Canonical.ofVal_exact hb]
  · exact nomatch h

theorem fits (f : Float64) : shapeDoc.accepts (toVal f) = true := by
  apply accepts_struct
  exact acceptsFields_cons _ _ _ _ _ _ (Canonical.fits f.bits) (acceptsFields_nil _)

end Float64Canonical

instance instCanonicalFloat64 : Canonical Float64 :=
  ⟨Float64Canonical.shapeDoc, Float64Canonical.toVal, Float64Canonical.ofVal,
    Float64Canonical.ofVal_toVal, Float64Canonical.ofVal_exact, Float64Canonical.fits⟩

/-! ## A nested recursion: `Json` -/

namespace JsonCanonical

/-- The sum of the six constructors; `Json` refers to itself by name. -/
def jsonShape : Shape :=
  .sum "Json"
    [("null", []),
     ("bool", [("value", (shape Bool).root)]),
     ("number", [("value", (shape Float64).root)]),
     ("str", [("value", (shape String).root)]),
     ("arr", [("elements", .list (.named "Json"))]),
     ("obj", [("entries", .list (.pair (shape String).root (.named "Json")))])]

/-- One table for the block, then the field types' tables. -/
def shapeDoc : ShapeDoc :=
  ⟨.named "Json",
   ("Json", jsonShape) :: ((shape Bool).defs ++ (shape Float64).defs ++ (shape String).defs)⟩

mutual
def toVal : Json → Val
  | .null => .ctor 0 []
  | .bool b => .ctor 1 [Canonical.toVal b]
  | .number f => .ctor 2 [Canonical.toVal f]
  | .str s => .ctor 3 [Canonical.toVal s]
  | .arr xs => .ctor 4 [.list (toValList xs)]
  | .obj es => .ctor 5 [.list (toValEntries es)]
def toValList : List Json → List Val
  | [] => []
  | x :: xs => toVal x :: toValList xs
def toValEntries : List (String × Json) → List Val
  | [] => []
  | (k, v) :: es => .pair (Canonical.toVal k) (toVal v) :: toValEntries es
end

mutual
def ofVal : Val → Option Json
  | .ctor 0 [] => some .null
  | .ctor 1 [b] => (Canonical.ofVal (α := Bool) b).map .bool
  | .ctor 2 [f] => (Canonical.ofVal (α := Float64) f).map .number
  | .ctor 3 [s] => (Canonical.ofVal (α := String) s).map .str
  | .ctor 4 [.list vs] => (ofValList vs).map .arr
  | .ctor 5 [.list vs] => (ofValEntries vs).map .obj
  | _ => none
def ofValList : List Val → Option (List Json)
  | [] => some []
  | v :: vs =>
    match ofVal v, ofValList vs with
    | some x, some xs => some (x :: xs)
    | _, _ => none
def ofValEntries : List Val → Option (List (String × Json))
  | [] => some []
  | .pair k v :: vs =>
    match Canonical.ofVal (α := String) k, ofVal v, ofValEntries vs with
    | some key, some x, some es => some ((key, x) :: es)
    | _, _, _ => none
  | _ => none
end

mutual
theorem ofVal_toVal (j : Json) : ofVal (toVal j) = some j := by
  cases j with
  | null => rfl
  | bool b => simp [toVal, ofVal, Canonical.ofVal_toVal]
  | number f => simp [toVal, ofVal, Canonical.ofVal_toVal]
  | str s => simp [toVal, ofVal, Canonical.ofVal_toVal]
  | arr xs => simp [toVal, ofVal, ofValList_toValList xs]
  | obj es => simp [toVal, ofVal, ofValEntries_toValEntries es]
termination_by structural j
theorem ofValList_toValList (xs : List Json) : ofValList (toValList xs) = some xs := by
  match xs with
  | [] => rfl
  | x :: xs => simp [toValList, ofValList, ofVal_toVal x, ofValList_toValList xs]
termination_by structural xs
theorem ofValEntries_toValEntries (es : List (String × Json)) :
    ofValEntries (toValEntries es) = some es := by
  match es with
  | [] => rfl
  | (k, v) :: es =>
    simp [toValEntries, ofValEntries, Canonical.ofVal_toVal, ofVal_toVal v,
      ofValEntries_toValEntries es]
termination_by structural es
end

/-- Exactness at one value, the form the list companions carry. -/
def Exact (v : Val) : Prop := ∀ j : Json, ofVal v = some j → v = toVal j

theorem ofValList_exact_of : ∀ (vs : List Val), (∀ x ∈ vs, Exact x) →
    ∀ xs : List Json, ofValList vs = some xs → vs = toValList xs
  | [], _, xs, h => by
    simp only [ofValList] at h
    injection h with h
    subst h
    rfl
  | v :: vs, hel, xs, h => by
    simp only [ofValList] at h
    split at h
    · next x xs' hx hxs =>
      injection h with h
      subst h
      rw [toValList, hel v (by simp) x hx,
        ofValList_exact_of vs (fun y hy => hel y (by simp [hy])) xs' hxs]
    · exact nomatch h

theorem ofValEntries_exact_of : ∀ (vs : List Val), (∀ x ∈ vs, ∀ k w, x = .pair k w → Exact w) →
    ∀ es : List (String × Json), ofValEntries vs = some es → vs = toValEntries es
  | [], _, es, h => by
    simp only [ofValEntries] at h
    injection h with h
    subst h
    rfl
  | .pair k v :: vs, hel, es, h => by
    simp only [ofValEntries] at h
    split at h
    · next key x es' hk hx hes =>
      injection h with h
      subst h
      rw [toValEntries, Canonical.ofVal_exact hk, hel (.pair k v) (by simp) k v rfl x hx,
        ofValEntries_exact_of vs (fun y hy => hel y (by simp [hy])) es' hes]
    · exact nomatch h
  | .unit :: _, _, _, h => nomatch h
  | .bool _ :: _, _, _, h => nomatch h
  | .nat _ :: _, _, _, h => nomatch h
  | .str _ :: _, _, _, h => nomatch h
  | .bytes _ :: _, _, _, h => nomatch h
  | .list _ :: _, _, _, h => nomatch h
  | .none :: _, _, _, h => nomatch h
  | .some _ :: _, _, _, h => nomatch h
  | .ctor _ _ :: _, _, _, h => nomatch h
  | .ref _ _ :: _, _, _, h => nomatch h

/-- The induction carries exactness at the value, at every element of a `list`, and at the
second component of a `pair`, because a `ctor` argument that is a list of pairs is three levels
below the constructor. -/
theorem exact_aux : ∀ v : Val,
    Exact v ∧ (∀ vs, v = .list vs → ∀ x ∈ vs, Exact x ∧ ∀ k w, x = .pair k w → Exact w) ∧
      (∀ k w, v = .pair k w → Exact w) := by
  intro v
  induction v using Val.ind with
  | unit => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | bool b => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | nat n => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | str s => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | bytes bs => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | none => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | some a _ => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | ref k d => exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | list xs ih =>
    refine ⟨(fun _ h => nomatch h), fun vs h => ?_, (fun _ _ h => nomatch h)⟩
    injection h with h
    subst h
    exact fun x hx => ⟨(ih x hx).1, (ih x hx).2.2⟩
  | pair a b _ ihb =>
    refine ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), fun k w h => ?_⟩
    injection h with _ hw
    subst hw
    exact ihb.1
  | ctor i args ih =>
    refine ⟨fun j h => ?_, (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
    unfold ofVal at h
    split at h
    all_goals first
      | (rename_i heq
         injection heq with hi hargs
         subst hi hargs
         injection h with h
         subst h
         rfl)
      | (rename_i w heq
         injection heq with hi hargs
         subst hi hargs
         obtain ⟨x, hx, hj⟩ := Option.map_eq_some_iff.mp h
         subst hj
         simp only [toVal]
         rw [Canonical.ofVal_exact hx])
      | (rename_i vs heq
         injection heq with hi hargs
         subst hi hargs
         obtain ⟨xs, hxs, hj⟩ := Option.map_eq_some_iff.mp h
         subst hj
         simp only [toVal]
         rw [ofValList_exact_of vs (fun x hx => ((ih (.list vs) (by simp)).2.1 vs rfl x hx).1)
           xs hxs])
      | (rename_i vs heq
         injection heq with hi hargs
         subst hi hargs
         obtain ⟨es, hes, hj⟩ := Option.map_eq_some_iff.mp h
         subst hj
         simp only [toVal]
         rw [ofValEntries_exact_of vs
           (fun x hx => ((ih (.list vs) (by simp)).2.1 vs rfl x hx).2) es hes])
      | exact nomatch h

theorem ofVal_exact {v : Val} {j : Json} (h : ofVal v = some j) : v = toVal j :=
  (exact_aux v).1 j h

theorem mem_defs : ("Json", jsonShape) ∈ shapeDoc.defs := List.Mem.head _

mutual
theorem fits (j : Json) : shapeDoc.accepts (toVal j) = true := by
  show acceptsIn shapeDoc.defs (.named "Json") (toVal j) = true
  apply accepts_named_of_mem _ _ jsonShape _ mem_defs
  cases j with
  | null => exact acceptsAt_sum _ _ _ 0 "null" [] [] rfl (acceptsFields_nil _)
  | bool b =>
    exact acceptsAt_sum _ _ _ 1 "bool" _ _ rfl (acceptsFields_cons _ _ _ _ _ _
      (acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits b))
      (acceptsFields_nil _))
  | number f =>
    exact acceptsAt_sum _ _ _ 2 "number" _ _ rfl (acceptsFields_cons _ _ _ _ _ _
      (acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits f))
      (acceptsFields_nil _))
  | str s =>
    exact acceptsAt_sum _ _ _ 3 "str" _ _ rfl (acceptsFields_cons _ _ _ _ _ _
      (acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits s))
      (acceptsFields_nil _))
  | arr xs =>
    exact acceptsAt_sum _ _ _ 4 "arr" _ _ rfl (acceptsFields_cons _ _ _ _ _ _
      (accepts_list _ _ _ (fitsList xs)) (acceptsFields_nil _))
  | obj es =>
    exact acceptsAt_sum _ _ _ 5 "obj" _ _ rfl (acceptsFields_cons _ _ _ _ _ _
      (accepts_list _ _ _ (fitsEntries es)) (acceptsFields_nil _))
termination_by structural j
theorem fitsList (xs : List Json) :
    ∀ v ∈ toValList xs, acceptsIn shapeDoc.defs (.named "Json") v = true := by
  match xs with
  | [] =>
    intro v hv
    exact nomatch hv
  | x :: xs =>
    intro v hv
    simp only [toValList, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact fits x
    · exact fitsList xs v hv
termination_by structural xs
theorem fitsEntries (es : List (String × Json)) :
    ∀ v ∈ toValEntries es,
      acceptsIn shapeDoc.defs (.pair (shape String).root (.named "Json")) v = true := by
  match es with
  | [] =>
    intro v hv
    exact nomatch hv
  | (k, x) :: es =>
    intro v hv
    simp only [toValEntries, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact accepts_pair _ _ _ _ _
        (acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits k))
        (fits x)
    · exact fitsEntries es v hv
termination_by structural es
end

end JsonCanonical

instance instCanonicalJson : Canonical Json :=
  ⟨JsonCanonical.shapeDoc, JsonCanonical.toVal, JsonCanonical.ofVal, JsonCanonical.ofVal_toVal,
    JsonCanonical.ofVal_exact, JsonCanonical.fits⟩

/-! ## A mutual pair -/

namespace Templates

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

#guard Canonical.toVal entry = sampleEntry
#guard Canonical.encode entry = Val.encode sampleEntry
#guard (Canonical.encode entry).length = 74
#guard (Canonical.digest entry).hex =
  "8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa"
#guard Canonical.decode (Canonical.encode entry) = some entry
#guard Canonical.print entry =
  .obj [("module", .str "Effect"), ("name", .str "gen"), ("kind", .str "const"),
    ("line", Json.ofNat 1947)]
#guard Canonical.print ExportKind.const = .str "const"
#guard Canonical.encode ExportKind.const = [10, 0, 0, 0, 0, 0, 0, 0, 9, 2, 0, 0, 0, 0, 0, 0, 0, 0]
#guard (Canonical.document Entry).references.length = 0

/-- A JSON value touching every constructor. -/
def json : Json :=
  .obj [("a", .arr [.null, .bool true, .number ⟨3⟩, .str "x"]), ("b", .obj [])]

#guard Canonical.decode (Canonical.encode json) = some json
#guard Canonical.decode (α := Json) (Canonical.encode (Json.arr [.null]) ++ [0]) = none
#guard Canonical.print (Json.arr [.null, .bool false]) =
  .obj [("_tag", .str "arr"), ("elements", .arr [.obj [("_tag", .str "null")],
    .obj [("_tag", .str "bool"), ("value", .bool false)]])]
#guard (Canonical.document Json).references.length = 2

def forest : Forest := .cons (.node 1 (.cons (.node 2 .nil) .nil)) (.cons (.node 3 .nil) .nil)

#guard Canonical.decode (Canonical.encode forest) = some forest
#guard Canonical.decode (α := Tree) (Canonical.encode forest) = none
#guard (Canonical.encode (Tree.node 7 .nil)).length = 9 + 9 + 10 + 18

end Templates

/-! ## Receipts -/

#print axioms Templates.ExportKind.ofVal_exact
#print axioms Templates.ExportKind.fits
#print axioms Templates.ExportKind.instCanonical
#print axioms Templates.Entry.ofVal_toVal
#print axioms Templates.Entry.ofVal_exact
#print axioms Templates.Entry.fits
#print axioms Templates.Entry.instCanonical
#print axioms Float64Canonical.ofVal_exact
#print axioms Float64Canonical.fits
#print axioms instCanonicalFloat64
#print axioms JsonCanonical.toVal
#print axioms JsonCanonical.ofVal
#print axioms JsonCanonical.ofVal_toVal
#print axioms JsonCanonical.exact_aux
#print axioms JsonCanonical.ofVal_exact
#print axioms JsonCanonical.mem_defs
#print axioms JsonCanonical.fits
#print axioms instCanonicalJson
#print axioms Templates.TreeForest.mem_tree
#print axioms Templates.TreeForest.mem_forest
#print axioms Templates.TreeForest.ofValT_toValT
#print axioms Templates.TreeForest.exact_aux
#print axioms Templates.TreeForest.fitsT
#print axioms Templates.Tree.instCanonical
#print axioms Templates.Forest.instCanonical

end Effect4.Store
