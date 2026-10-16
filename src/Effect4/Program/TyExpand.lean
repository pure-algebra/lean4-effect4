module

public import Effect4.Program.Ty

/-!
# Program.TyExpand — the declaration table, and a type's expansion under a table of expansions

The **declaration table** (`TyDecls`) is a list of named type bodies (decisions rows 124, 158, 400
and 401). A body refers to a declared name by a nominal reference, `handle n` or `app n args`.
The table's checker, its fixed point and its laws are `Program/TyDecls.lean` and
`Laws/Program/TyDecls.lean`. This module holds what a Lean module may import: the table, its
lookup, and expansion.

**Expansion** (`Ty.expand`) replaces each reference to a name that a table of expansions
declares by that name's entry. It replaces a reference only at a position that the checker reads
by shape: a child of `option`, `list`, `prod`, `except`, `exitOf`, `causeOf`, `union`, `record`,
`map` or `tuple`, the children that `Val.obligations` asks its questions at. Every other type is a
leaf to the checker, read as it is, and expansion leaves it as it is. A table of expansions solves
a declaration table when each declared name's expansion is its body's (`TyDecls.Expands`). On a
guarded table, membership at a type is then membership at its expansion (`memberIn_iff_expand`,
`Laws/Program/TyExpand.lean`): a declared name with no recursion abbreviates its expansion.

`Modeled` reads this module: a named Lean type's reference expands to its code
(`Modeled.ref_expands`, `src/Effect4/Schema/Modeled.lean`).
-/

@[expose] public section

namespace Effect4.Program

/-- **The declaration table** (decisions rows 124, 158 and 400): each entry a name and its body.
A body refers to a declaration by `app n args` or `handle n`. A name's first entry is its
declaration; formation refuses a repeated name. -/
abbrev TyDecls := List (String × Ty)

namespace TyDecls

/-- The body a name declares: its first entry. -/
def body? (decls : TyDecls) (name : String) : Option Ty := decls.lookup name

/-- A declared name has an entry. -/
theorem mem_of_body? {decls : TyDecls} {name : String} {body : Ty}
    (h : decls.body? name = some body) : (name, body) ∈ decls := by
  induction decls with
  | nil => cases h
  | cons d decls ih =>
    obtain ⟨m, b⟩ := d
    unfold body? at h
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      cases h
      rw [beq_iff_eq.mp heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

end TyDecls

/-- The name of a nominal reference: `handle n`, or `app n args` at any arguments. A declared
name is read at both spellings, since `app n []` normalizes to `handle n`. -/
def Ty.refName? : Ty → Option String
  | .handle name => some name
  | .app name _ => some name
  | _ => none

/-! ## Expansion -/

mutual
/-- **Expansion**: each reference to a name that `exps` declares, at a position the checker reads
by shape, replaced by the name's entry in `exps`. A leaf stays as it is: the checker reads it as
it is and unfolds no name inside it. -/
def Ty.expand (exps : TyDecls) : Ty → Ty
  | .handle n => (exps.body? n).getD (.handle n)
  | .app n args => (exps.body? n).getD (.app n args)
  | .option t => .option (Ty.expand exps t)
  | .list t => .list (Ty.expand exps t)
  | .prod a b => .prod (Ty.expand exps a) (Ty.expand exps b)
  | .except a b => .except (Ty.expand exps a) (Ty.expand exps b)
  | .exitOf a b => .exitOf (Ty.expand exps a) (Ty.expand exps b)
  | .causeOf t => .causeOf (Ty.expand exps t)
  | .union a b => .union (Ty.expand exps a) (Ty.expand exps b)
  | .map a b => .map (Ty.expand exps a) (Ty.expand exps b)
  | .record fs => .record (Ty.expandFields exps fs)
  | .tuple ts => .tuple (Ty.expandItems exps ts)
  | .fiberOf a b => .fiberOf a b
  | .refOf t => .refOf t
  | .deferredOf a b => .deferredOf a b
  | .never => .never
  | .unknown => .unknown
  | .unit => .unit
  | .nat => .nat
  | .int => .int
  | .string => .string
  | .bool => .bool
  | .lit s => .lit s
  | .var i => .var i
  | .null => .null
  | .undefined => .undefined
  | .number => .number
  | .bytes => .bytes
  | .contextOf keys => .contextOf keys
/-- The field-list companion of `Ty.expand`. -/
def Ty.expandFields (exps : TyDecls) : List (String × Bool × Ty) → List (String × Bool × Ty)
  | [] => []
  | (n, o, t) :: rest => (n, o, Ty.expand exps t) :: Ty.expandFields exps rest
/-- The item-list companion of `Ty.expand`. -/
def Ty.expandItems (exps : TyDecls) : List Ty → List Ty
  | [] => []
  | t :: rest => Ty.expand exps t :: Ty.expandItems exps rest
end

/-- The field companion of `Ty.expand` is a map. -/
theorem Ty.expandFields_eq_map (exps : TyDecls) (fs : List (String × Bool × Ty)) :
    Ty.expandFields exps fs = fs.map (fun q => (q.1, q.2.1, Ty.expand exps q.2.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [Ty.expandFields, ih]
    rfl

/-- The item companion of `Ty.expand` is a map. -/
theorem Ty.expandItems_eq_map (exps : TyDecls) (ts : List Ty) :
    Ty.expandItems exps ts = ts.map (Ty.expand exps) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [Ty.expandItems, ih, List.map_cons]

/-! ## A table of expansions that solves a declaration table -/

/-- **`exps` solves `decls`**: each entry's name has, in `exps`, its body's expansion. The
expansions are then a solution of the table's equations, written with no declared name at a
position the checker reads by shape. A recursive table has no such solution. -/
def TyDecls.Expands (exps decls : TyDecls) : Prop :=
  ∀ e ∈ decls, exps.body? e.1 = some (Ty.expand exps e.2)

/-- A solution of a table solves each part of it: the declarations a field's type brings. -/
theorem TyDecls.Expands.left {exps a b : TyDecls} (h : TyDecls.Expands exps (a ++ b)) :
    TyDecls.Expands exps a :=
  fun e he => h e (List.mem_append_left b he)

/-- A solution of a table solves each part of it: the declarations after the first part. -/
theorem TyDecls.Expands.right {exps a b : TyDecls} (h : TyDecls.Expands exps (a ++ b)) :
    TyDecls.Expands exps b :=
  fun e he => h e (List.mem_append_right a he)

/-- **A declared name expands to its body's expansion** under a solution that holds its entry. -/
theorem TyDecls.Expands.named {exps : TyDecls} {name : String} {body : Ty}
    (h : TyDecls.Expands exps [(name, body)]) :
    Ty.expand exps (.handle name) = Ty.expand exps body := by
  show (exps.body? name).getD (.handle name) = _
  rw [h (name, body) List.mem_cons_self]
  rfl

/-- **The expansions of a table**, read left to right: each body with the names declared before
it replaced by their expansions. Whether they solve the table is checked, not assumed
(`TyDecls.expandable`). -/
def TyDecls.expansions (decls : TyDecls) : TyDecls :=
  decls.foldl (fun acc d => acc ++ [(d.1, Ty.expand acc d.2)]) []

/-- `exps` solves `decls`, decided: each entry's name has its body's expansion in `exps`. -/
def TyDecls.expandsAll (exps decls : TyDecls) : Bool :=
  decls.all fun d => exps.body? d.1 == some (Ty.expand exps d.2)

/-- **Expandable**: the expansions of the table solve it. A table with no recursion whose bodies
name only earlier names is expandable; a recursive table is not. -/
def TyDecls.expandable (decls : TyDecls) : Bool := decls.expansions.expandsAll decls

/-! ### Expansion by its arms

The equations a written expansion proof composes, one per arm that `deriving Modeled` writes
(`Schema/Modeled/Derive.lean`): a record's fields, a union's sides, and a literal. -/

/-- A record expands field by field. -/
theorem Ty.expand_record_eq {exps : TyDecls} {fs gs : List (String × Bool × Ty)}
    (h : Ty.expandFields exps fs = gs) : Ty.expand exps (.record fs) = .record gs := by
  show Ty.record (Ty.expandFields exps fs) = _
  rw [h]

/-- No field expands to no field. -/
theorem Ty.expandFields_nil (exps : TyDecls) : Ty.expandFields exps [] = [] := rfl

/-- A field expands at its type. -/
theorem Ty.expandFields_cons_eq {exps : TyDecls} {n : String} {o : Bool} {t x : Ty}
    {rest rest' : List (String × Bool × Ty)} (ht : Ty.expand exps t = x)
    (hr : Ty.expandFields exps rest = rest') :
    Ty.expandFields exps ((n, o, t) :: rest) = (n, o, x) :: rest' := by
  show (n, o, Ty.expand exps t) :: Ty.expandFields exps rest = _
  rw [ht, hr]

/-- A union expands side by side. -/
theorem Ty.expand_union_eq {exps : TyDecls} {a b a' b' : Ty} (ha : Ty.expand exps a = a')
    (hb : Ty.expand exps b = b') : Ty.expand exps (.union a b) = .union a' b' := by
  show Ty.union (Ty.expand exps a) (Ty.expand exps b) = _
  rw [ha, hb]

/-- A literal is a leaf. -/
theorem Ty.expand_lit (exps : TyDecls) (s : String) : Ty.expand exps (.lit s) = .lit s := rfl

/-- A list expands at its item. -/
theorem Ty.expand_list_eq {exps : TyDecls} {t x : Ty} (h : Ty.expand exps t = x) :
    Ty.expand exps (.list t) = .list x := by
  show Ty.list (Ty.expand exps t) = _
  rw [h]

/-- An option expands at its inner type. -/
theorem Ty.expand_option_eq {exps : TyDecls} {t x : Ty} (h : Ty.expand exps t = x) :
    Ty.expand exps (.option t) = .option x := by
  show Ty.option (Ty.expand exps t) = _
  rw [h]

/-- A pair expands side by side. -/
theorem Ty.expand_prod_eq {exps : TyDecls} {a b a' b' : Ty} (ha : Ty.expand exps a = a')
    (hb : Ty.expand exps b = b') : Ty.expand exps (.prod a b) = .prod a' b' := by
  show Ty.prod (Ty.expand exps a) (Ty.expand exps b) = _
  rw [ha, hb]

end Effect4.Program
