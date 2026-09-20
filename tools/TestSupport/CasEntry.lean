import Effect4.Store.Domain.Node
import Effect4.Store.Domain.Derived.Json

/-! Shared CAS entry fixture. No runtime module imports test support.
Declarations and proofs retain their existing names; tests retain all guards. -/

set_option autoImplicit false

namespace Effect4.Store.Templates

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
    [("const", 0, []), ("function", 1, []), ("class_", 2, []), ("interface", 3, []),
     ("type", 4, []), ("namespace_", 5, [])], []⟩

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

/-- The census entry of the facts note: `Effect.gen`, a `const` at line 1947. -/
def entry : Entry := ⟨"Effect", "gen", .const, 1947⟩

end Effect4.Store.Templates

namespace Test.Store.NodeContract
open Effect4.Store

/-- `Templates.Entry` files as `export`, the kind the plan's §3 gives the census entry. -/
instance instContentEntry : Content Effect4.Store.Templates.Entry := ⟨.«export»⟩

end Test.Store.NodeContract
