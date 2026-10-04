import Effect4.Codegen.Metadata
import Effect4.Codegen.Types
import TypeScript.Identifier

/-!
# Canonical record wrappers and field access

This target-syntax boundary retains raw declared fields, supplied names, and child expressions.
The normal image uses `objectWith` in row 196's whole-literal key form. The raw image retains
inputs whose target annotation is unavailable or whose name/value lengths differ.

The structural reader recognizes one image for every input. The Laws module proves both
directions without adding a formation or length premise to the later term round trip.
The runtime presence helper and target-text parsing remain separate obligations.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Record
open Effect4.Program TypeScript

/-- Runtime helper bindings owned by the record target profile, separate from program heads. -/
def helperNames : List String := ["recordValue", "recordRaw", "recordRequired", "recordOptional", "recordSet"]

/-- Existing raw record declaration data, not a new type representation. -/
abbrev Fields := List (String × Bool × Ty)

/-- A transparent view of the record constructor's three components. -/
abbrev Parts := Fields × List String × List Expr

/-- Row 196 selects one key form for the whole literal. -/
def keyForm (names : List String) : KeyForm :=
  if names.contains "__proto__" then .computed
  else if names.all targetIdentifier then .plain
  else .quoted

/-- The normal branch requires both a target annotation and aligned arguments. -/
def targetType (fields : Fields) (names : List String) (values : List Expr) : Option TypeRef :=
  if names.length = values.length then Types.ofTy (.record fields) else none

/-- Properties retain the supplied order. The normal branch checks that zip loses nothing. -/
def properties (names : List String) (values : List Expr) : List ObjectEntry :=
  (names.zip values).map fun p => .property p.1 p.2

/-- The sole structural record image, including a total raw fallback. -/
def writeRecord (fields : Fields) (names : List String) (values : List Expr) : Expr :=
  let metadata := Metadata.writeTy (.record fields)
  match targetType fields names values with
  | some type =>
    .call (.generic (.ident "recordValue") [type])
      [metadata, .objectWith (keyForm names) (properties names values)]
  | none =>
    .call (.generic (.ident "recordRaw") [.name ["unknown"] []])
      [metadata, .arr (names.map Expr.str), .arr values]

/-- Decode a record declaration from the exact existing type metadata. -/
def readFields (e : Expr) : Option Fields := do
  match ← Metadata.readTy e with
  | .record fields => some fields
  | _ => none

/-- Property entries retain their child expressions. A spread is outside construction's image. -/
def readProperties : List ObjectEntry → Option (List (String × Expr))
  | [] => some []
  | .property name value :: entries => do
    let rest ← readProperties entries
    some ((name, value) :: rest)
  | .spread _ :: _ => none

/-- Raw argument names are string data, never expressions to execute. -/
def readNames : List Expr → Option (List String)
  | [] => some []
  | .str name :: names => do
    let rest ← readNames names
    some (name :: rest)
  | _ => none

/-- Recognize the canonical normal or raw branch, without comparing child expressions. -/
def readRecord : Expr → Option Parts
  | .call (.generic (.ident "recordValue") [annotation]) [metadata, .objectWith form entries] => do
    let fields ← readFields metadata
    let pairs ← readProperties entries
    let names := pairs.map Prod.fst
    let values := pairs.map Prod.snd
    let expected ← targetType fields names values
    if TypeRef.beq annotation expected && decide (form = keyForm names) then
      some (fields, names, values)
    else none
  | .call (.generic (.ident "recordRaw") [.name ["unknown"] []])
      [metadata, .arr nameExprs, .arr values] => do
    let fields ← readFields metadata
    let names ← readNames nameExprs
    match targetType fields names values with
    | none => some (fields, names, values)
    | some _ => none
  | _ => none

/-- Exact-codecs helper for the `printed-modules` consumer `readTermList`: recovering the
child values adds no syntax. The sole premise is successful property reading (R2/R3). -/
theorem readProperties_size (entries : List ObjectEntry) (pairs : List (String × Expr))
    (h : readProperties entries = some pairs) :
    sizeOf (pairs.map Prod.snd) ≤ sizeOf entries := by
  induction entries generalizing pairs with
  | nil => cases h; exact Nat.le_refl _
  | cons entry entries ih =>
    cases entry with
    | property name value =>
      simp only [readProperties] at h
      obtain ⟨rest, hrest, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      have hi := ih rest hrest
      simp only [List.map_cons, List.cons.sizeOf_spec, ObjectEntry.property.sizeOf_spec]
      omega
    | spread _ => exact nomatch h

/-- Exact-codecs termination helper for `readTermList`, on every successful wrapper read.
It bounds the recovered child list, without a formation or target-execution claim (R2/R3). -/
theorem readRecord_size (e : Expr) (fields : Fields) (names : List String) (values : List Expr)
    (h : readRecord e = some (fields, names, values)) : sizeOf values < sizeOf e := by
  unfold readRecord at h
  split at h
  · next annotation metadata form entries =>
    obtain ⟨fields', hfields, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨pairs, hpairs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨expected, ht, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
      have hs := readProperties_size entries pairs hpairs
      simp only [Expr.call.sizeOf_spec, List.cons.sizeOf_spec, Expr.objectWith.sizeOf_spec]
      omega
    · exact nomatch h
  · next metadata nameExprs values' =>
    obtain ⟨fields', hfields, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨names', hnames, h⟩ := Option.bind_eq_some_iff.mp h
    cases ht : targetType fields' names' values' with
    | none =>
      rw [ht] at h
      cases h
      simp only [Expr.call.sizeOf_spec, List.cons.sizeOf_spec, Expr.arr.sizeOf_spec]
      omega
    | some type => rw [ht] at h; exact nomatch h
  · exact nomatch h

/-- Both modes retain a literal key marker and use a never-preserving target helper (row 198). -/
def writeField (optional : Bool) (name : String) (target : Expr) : Expr :=
  .call (.call (.generic (.ident (if optional then "recordOptional" else "recordRequired"))
    [.literal name]) [.str name]) [target]

/-- The helper head retains the mode; both literal key occurrences must agree. -/
def readField : Expr → Option (Bool × String × Expr)
  | .call (.call (.generic (.ident "recordRequired") [.literal name]) [.str key]) [target] =>
    if key = name then some (false, name, target) else none
  | .call (.call (.generic (.ident "recordOptional") [.literal name]) [.str key]) [target] =>
    if key = name then some (true, name, target) else none
  | _ => none

/-- Exact-codecs termination helper for `readTerm`, on every successful field read.
It bounds the recovered target, without a typing or target-execution claim (R2/R3). -/
theorem readField_size (e : Expr) (optional : Bool) (name : String) (target : Expr)
    (h : readField e = some (optional, name, target)) : sizeOf target < sizeOf e := by
  unfold readField at h
  split at h
  · split at h
    · cases h
      simp only [Expr.call.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · exact nomatch h
  · split at h
    · cases h
      simp only [Expr.call.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · exact nomatch h
  · exact nomatch h

/-- Curried update: copy the target before evaluating the replacement (row 198).
The literal generic marker distinguishes this image from an ordinary atom call. -/
def writeSet (name : String) (target value : Expr) : Expr :=
  .call (.call (.call (.generic (.ident "recordSet") [.literal name]) [.str name]) [target]) [value]

/-- Read the exact literal key, target, and replacement from the curried helper image. -/
def readSet : Expr → Option (String × Expr × Expr)
  | .call (.call (.call (.generic (.ident "recordSet") [.literal name]) [.str key]) [target]) [value] =>
    if key = name then some (name, target, value) else none
  | _ => none

/-- Exact-codecs termination helper for the two update children of `readTerm`.
Successful structural reading is the only premise; it makes no execution claim (R2/R3). -/
theorem readSet_size (e : Expr) (name : String) (target value : Expr)
    (h : readSet e = some (name, target, value)) :
    sizeOf target < sizeOf e ∧ sizeOf value < sizeOf e := by
  unfold readSet at h
  split at h
  · split at h
    · cases h
      simp only [Expr.call.sizeOf_spec, List.cons.sizeOf_spec]
      constructor <;> omega
    · exact nomatch h
  · exact nomatch h

end Effect4.Codegen.Record
