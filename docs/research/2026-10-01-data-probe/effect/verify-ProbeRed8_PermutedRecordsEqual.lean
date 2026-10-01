/-! RED CONTROL (must fail): the witnesses file with one guard flipped — the two permuted records
are claimed EQUAL. Expected: the flipped `#guard` fails, exit 1. -/

/-!
# Verifier of seat EFFECT (2026-10-01): witnesses in the seat's own record model

The definitions between the two markers are copied verbatim from the seat's
`lean/ProbeRecordModel.lean` lines 25-218 (by `sed -n 25,218p`), only the namespace differs. What
this file adds, each a finite witness or a kernel theorem about the MODEL, not the tree:

1. the model's `sub` relates two records whose fields are a permutation of each other in both
   directions while the two types differ, so the tree's proved canonical antisymmetry
   (`Ty.sub_antisymm_canonical`, DI-15 (3)) survives records only if the canonical form fixes the
   field order (the type-algebra note §1.3's "ascending by name"); then `schema ∘ ofSchema`
   reorders a foreign struct, and S-a1's exactness needs field order in its normaliser, not only
   `stripAnn` (`model_sub_not_antisymm`, proved);
2. a positional carrier with prefix semantics passes the seat's width witness (`posFitsFields`)
   and fails at a permutation, which is the witness that actually forces name-keyed values;
3. the model's decoder and `norm` keep the FIRST of two duplicate keys; rc.112 from JSON text keeps
   the LAST (`ts/rc112-schema-behaviour.log` T7); the tree refuses both (schema-codec contract). The
   model's exactness theorem is therefore proved under a duplicate policy neither side has.
-/

set_option autoImplicit false

namespace VerifyEffect.Model

-- ===== BEGIN verbatim copy: lean/ProbeRecordModel.lean lines 25-218 =====
mutual
  /-- Data types: strings, naturals and records. -/
  inductive DTy where
    | str
    | nat
    | record (fields : DFields)
  /-- A record's fields as a spine: name, whether the key may be absent, type. -/
  inductive DFields where
    | nil
    | cons (name : String) (optional : Bool) (type : DTy) (rest : DFields)
end

mutual
  /-- JSON as the wire sees it: strings, signed integers (as JSON numbers may be), objects
  with ordered entries, duplicates kept. -/
  inductive J where
    | str (s : String)
    | num (n : Int)
    | obj (entries : JEntries)
  inductive JEntries where
    | nil
    | cons (key : String) (value : J) (rest : JEntries)
end

mutual
  /-- Machine values: strings, naturals, and name-keyed records. -/
  inductive V where
    | str (s : String)
    | nat (n : Nat)
    | obj (entries : VEntries)
  inductive VEntries where
    | nil
    | cons (key : String) (value : V) (rest : VEntries)
end

deriving instance DecidableEq for DTy, DFields
deriving instance DecidableEq for J, JEntries
deriving instance DecidableEq for V, VEntries

/-! ## Lookups and names -/

/-- The first entry with key `k`. -/
def JEntries.find? (k : String) : JEntries → Option J
  | .nil => none
  | .cons key value rest => if k = key then some value else JEntries.find? k rest

/-- The first entry with key `k`. -/
def VEntries.find? (k : String) : VEntries → Option V
  | .nil => none
  | .cons key value rest => if k = key then some value else VEntries.find? k rest

/-- The first field named `k`: whether it is optional, and its type. -/
def DFields.find? (k : String) : DFields → Option (Bool × DTy)
  | .nil => none
  | .cons name optional type rest =>
      if k = name then some (optional, type) else DFields.find? k rest

def DFields.names : DFields → List String
  | .nil => []
  | .cons name _ _ rest => name :: DFields.names rest

/-! ## Well-formedness: distinct field names at every record -/

mutual
  def DTy.WF : DTy → Prop
    | .str => True
    | .nat => True
    | .record fields => DFields.WF fields ∧ (DFields.names fields).Nodup
  def DFields.WF : DFields → Prop
    | .nil => True
    | .cons _ _ type rest => DTy.WF type ∧ DFields.WF rest
end

/-! ## Membership, subtyping, the codec, the normaliser, the projection -/

mutual
  /-- `Fits`, name-keyed: every declared key is present and fits, or absent and optional;
  undeclared keys are ignored (width). -/
  def fits : DTy → V → Bool
    | .str, .str _ => true
    | .nat, .nat _ => true
    | .record fields, .obj entries => fitsFields fields entries
    | _, _ => false
  def fitsFields : DFields → VEntries → Bool
    | .nil, _ => true
    | .cons name optional type rest, entries =>
      (match VEntries.find? name entries with
        | some value => fits type value
        | none => optional) && fitsFields rest entries
end

mutual
  /-- `sub a b`, recursing on `b`: width (a may have more fields), depth (field types by `sub`),
  optionality (a required field may become optional, never the reverse), and every key of `b`
  declared by `a`. The last clause is stricter than TypeScript; see `subTS`. -/
  def sub : DTy → DTy → Bool
    | .str, .str => true
    | .nat, .nat => true
    | .record source, .record target => subFields source target
    | _, _ => false
  def subFields : DFields → DFields → Bool
    | _, .nil => true
    | source, .cons name optional type rest =>
      (match DFields.find? name source with
        | some (sourceOptional, sourceType) => sub sourceType type && (optional || !sourceOptional)
        | none => false) && subFields source rest
end

mutual
  /-- TypeScript's rule at an optional target key the source does not declare: accepted
  (`{}` is assignable to `{ x?: string }`). Kept only for the counterexample below. -/
  def subTS : DTy → DTy → Bool
    | .str, .str => true
    | .nat, .nat => true
    | .record source, .record target => subTSFields source target
    | _, _ => false
  def subTSFields : DFields → DFields → Bool
    | _, .nil => true
    | source, .cons name optional type rest =>
      (match DFields.find? name source with
        | some (sourceOptional, sourceType) => subTS sourceType type && (optional || !sourceOptional)
        | none => optional) && subTSFields source rest
end

mutual
  def decode : DTy → J → Option V
    | .str, .str s => some (.str s)
    | .nat, .num n => if 0 ≤ n then some (.nat n.toNat) else none
    | .record fields, .obj entries =>
      match decodeFields fields entries with
      | some values => some (.obj values)
      | none => none
    | _, _ => none
  def decodeFields : DFields → JEntries → Option VEntries
    | .nil, _ => some .nil
    | .cons name optional type rest, entries =>
      match JEntries.find? name entries with
      | some j =>
        match decode type j, decodeFields rest entries with
        | some v, some vs => some (.cons name v vs)
        | _, _ => none
      | none => if optional then decodeFields rest entries else none
end

mutual
  def encode : DTy → V → Option J
    | .str, .str s => some (.str s)
    | .nat, .nat n => some (.num n)
    | .record fields, .obj entries =>
      match encodeFields fields entries with
      | some js => some (.obj js)
      | none => none
    | _, _ => none
  def encodeFields : DFields → VEntries → Option JEntries
    | .nil, _ => some .nil
    | .cons name optional type rest, entries =>
      match VEntries.find? name entries with
      | some v =>
        match encode type v, encodeFields rest entries with
        | some j, some js => some (.cons name j js)
        | _, _ => none
      | none => if optional then encodeFields rest entries else none
end

mutual
  /-- The normaliser exactness is stated modulo: declared keys only, in declared order, the
  first occurrence of each. -/
  def norm : DTy → J → J
    | .str, j => j
    | .nat, j => j
    | .record fields, .obj entries => .obj (normFields fields entries)
    | .record _, j => j
  def normFields : DFields → JEntries → JEntries
    | .nil, _ => .nil
    | .cons name _ type rest, entries =>
      match JEntries.find? name entries with
      | some j => .cons name (norm type j) (normFields rest entries)
      | none => normFields rest entries
end

mutual
  /-- The projection retraction is stated modulo: what rc.112's struct parser keeps. -/
  def proj : DTy → V → V
    | .str, v => v
    | .nat, v => v
    | .record fields, .obj entries => .obj (projFields fields entries)
    | .record _, v => v
  def projFields : DFields → VEntries → VEntries
    | .nil, _ => .nil
    | .cons name _ type rest, entries =>
      match VEntries.find? name entries with
      | some v => .cons name (proj type v) (projFields rest entries)
      | none => projFields rest entries
end
-- ===== END verbatim copy =====

/-! ## 1. Permuted records: mutual subtypes, distinct types -/

def abRec : DTy := .record (.cons "a" false .str (.cons "b" false .nat .nil))
def baRec : DTy := .record (.cons "b" false .nat (.cons "a" false .str .nil))

#guard sub abRec baRec = true
#guard sub baRec abRec = true
#guard abRec = baRec

/-- The model's `sub` is not antisymmetric on raw types: a canonical form must fix field order. -/
theorem model_sub_not_antisymm :
    ¬ ∀ a b : DTy, sub a b = true → sub b a = true → a = b := by
  intro h
  have hab : abRec = baRec := h abRec baRec (by decide) (by decide)
  exact absurd hab (by decide)

/-! ## 2. A prefix-positional carrier: passes the seat's witness, fails at a permutation -/

/-- Values by position, names only in the type, extra trailing values allowed (prefix width). -/
def posPrefixFits : DFields → List V → Bool
  | .nil, _ => true
  | .cons _ _ t rest, v :: vs => fits t v && posPrefixFits rest vs
  | .cons _ optional _ rest, [] => optional && posPrefixFits rest []

def abFields' : DFields := .cons "a" false .str (.cons "b" false .nat .nil)
def aFields' : DFields := .cons "a" false .str .nil
def baFields' : DFields := .cons "b" false .nat (.cons "a" false .str .nil)

-- the seat's witness (drop a trailing field) does not separate this carrier from a name-keyed one
#guard sub (.record abFields') (.record aFields') = true
#guard posPrefixFits abFields' [.str "x", .nat 1] = true
#guard posPrefixFits aFields' [.str "x", .nat 1] = true
-- the permutation does
#guard sub (.record abFields') (.record baFields') = true
#guard posPrefixFits baFields' [.str "x", .nat 1] = false
#guard fits (.record baFields') (.obj (.cons "a" (.str "x") (.cons "b" (.nat 1) .nil))) = true

/-! ## 3. Duplicate keys: the model keeps the first; rc.112 from text keeps the last (T7) -/

def user' : DTy := .record (.cons "id" false .nat (.cons "name" false .str .nil))
def dupWire' : J := .obj (.cons "id" (.num 1) (.cons "id" (.num 2) (.cons "name" (.str "a") .nil)))

#guard decode user' dupWire' = some (.obj (.cons "id" (.nat 1) (.cons "name" (.str "a") .nil)))
#guard norm user' dupWire' = .obj (.cons "id" (.num 1) (.cons "name" (.str "a") .nil))


end VerifyEffect.Model
