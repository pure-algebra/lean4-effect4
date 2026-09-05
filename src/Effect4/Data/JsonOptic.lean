import Effect4.Data.Json
import Effect4.Data.Optic

/-!
# Data.JsonOptic — the optic at a key of a JSON object, with its laws

The generated optics module (`src/Effect4/Data/JsonOptic.lean`, rule `surface.entity.optics`)
emits `Optic.id<S>().key("p")` per property of an entity. Its Lean model is `Json.key "p"`: on
the encoded side of a schema, a property is a key of a JSON object, and the optic that reads
and writes it is a stable `Optional` over `Json` whose four equations
(`Effect4.Optional.Lawful`) are proved here once. The depth-two lens through a referenced
entity is `Optional.compose`, lawful by `Optional.Lawful.compose`.

The focus is the **first** binding of the key, and `replace` writes that binding in place
and touches nothing else; on a value that is not an object, or an object without the key,
`replace` is the identity, which is what `replace_absent` asks. rc.112's `key` is typed so
the key is always present and the optic is a `Lens`; the model is the weaker `Optional`
because `Json` does not carry the type.

Prisms (`Optic.id<S>().tag("Circle")`) have no model here: a prism over `Json` whose focus is
again `Json` cannot satisfy `preview_replace` for a replacement that lacks the tag. The row
is owed and the emitter says so in its header.
-/

namespace Effect4.Json

/-- The first binding of a name. -/
def get (name : String) : List (String × Json) → Option Json
  | [] => none
  | (k, v) :: rest => if k == name then some v else get name rest

/-- Replace the first binding of a name in place; leave the entries alone when absent. -/
def set (name : String) (value : Json) : List (String × Json) → List (String × Json)
  | [] => []
  | (k, v) :: rest => if k == name then (name, value) :: rest else (k, v) :: set name value rest

/-- The optic at a key of a JSON object: rc.112's `key`. -/
def key (name : String) : Optional Json Json where
  preview
    | .obj entries => get name entries
    | _ => none
  replace value
    | .obj entries => .obj (set name value entries)
    | other => other

/-! ## The laws -/

/-- `name == name` on a `String`, through `LawfulBEq`'s `beq_iff_eq` rather than `BEq.rfl`:
the `ReflBEq String` route `simp` takes reaches `Classical.choice` on this toolchain, and
these laws must stay at the library's axiom ceiling. -/
private theorem beq_self (name : String) : (name == name) = true := beq_iff_eq.mpr rfl

theorem get_set_present (name : String) (value : Json) :
    ∀ entries : List (String × Json),
      (get name entries).isSome → get name (set name value entries) = some value
  | [], h => by simp [get] at h
  | (k, v) :: rest, h => by
    by_cases eq : (k == name) = true
    · rw [beq_iff_eq.mp eq]
      simp only [set, get, beq_self, ite_true]
    · simp [set, get, eq] at h ⊢
      exact get_set_present name value rest h

theorem set_absent (name : String) (value : Json) :
    ∀ entries : List (String × Json), get name entries = none → set name value entries = entries
  | [], _ => rfl
  | (k, v) :: rest, h => by
    by_cases eq : (k == name) = true
    · simp [get, eq] at h
    · simp [set, get, eq] at h ⊢
      exact set_absent name value rest h

theorem set_get (name : String) :
    ∀ (entries : List (String × Json)) (current : Json),
      get name entries = some current → set name current entries = entries
  | [], _, h => by simp [get] at h
  | (k, v) :: rest, current, h => by
    by_cases eq : (k == name) = true
    · simp [get, eq] at h
      simp [set, eq]
      exact ⟨(beq_iff_eq.mp eq).symm, h.symm⟩
    · simp [set, get, eq] at h ⊢
      exact set_get name rest current h

theorem set_set (name : String) (first second : Json) :
    ∀ entries : List (String × Json),
      set name second (set name first entries) = set name second entries
  | [] => rfl
  | (k, v) :: rest => by
    by_cases eq : (k == name) = true
    · rw [beq_iff_eq.mp eq]
      simp only [set, beq_self, ite_true]
    · simp [set, eq]
      exact set_set name first second rest

/-- The optic at a key is a stable optional. -/
theorem key_lawful (name : String) : Optional.Lawful (key name) := by
  constructor
  · intro source value absent
    cases source with
    | obj entries =>
      simp only [key] at absent ⊢
      rw [set_absent name value entries absent]
    | _ => rfl
  · intro source current value present
    cases source with
    | obj entries =>
      simp only [key] at present ⊢
      exact get_set_present name value entries (by rw [present]; rfl)
    | _ => simp [key] at present
  · intro source current present
    cases source with
    | obj entries =>
      simp only [key] at present ⊢
      rw [set_get name entries current present]
    | _ => simp [key] at present
  · intro source first second
    cases source with
    | obj entries =>
      simp only [key]
      rw [set_set]
    | _ => rfl

/-- The lens through a referenced entity: `key outer` then `key inner`, lawful by
composition. -/
def path (outer inner : String) : Optional Json Json := (key outer).compose (key inner)

theorem path_lawful (outer inner : String) : Optional.Lawful (path outer inner) :=
  Optional.Lawful.compose (key_lawful outer) (key_lawful inner)

/-! ## Anti-vacuity -/

private def user : Json :=
  .obj [("id", .str "u1"), ("address", .obj [("street", .str "Main"), ("city", .str "Oslo")])]

#guard (key "id").preview user == some (.str "u1")
#guard (key "missing").preview user == none
#guard (key "id").replace (.str "u2") user ==
  .obj [("id", .str "u2"), ("address", .obj [("street", .str "Main"), ("city", .str "Oslo")])]
#guard (key "missing").replace (.str "x") user == user
#guard (path "address" "city").preview user == some (.str "Oslo")
#guard (path "address" "city").replace (.str "Bergen") user ==
  .obj [("id", .str "u1"), ("address", .obj [("street", .str "Main"), ("city", .str "Bergen")])]
#guard (key "id").preview (.str "not an object") == none

end Effect4.Json
