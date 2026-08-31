import Cas.IR.Word
import Cas.Codec.Hex
import Cas.Schema.Ast

/-!
# Conformance-vector carriers

The vector layer has three distinct representations:

- `ConformanceVector` is a candidate with a checked name and a
  non-empty store word;
- `CheckedConformanceVector` is the runtime-admitted state, obtainable
  only through `ConformanceVector.check`;
- `Wire.*` are named boundary records. Their `Described` instances and
  canonical JSON projection live in `Cas.Vectors.Schema`, keeping the
  compiler-side deriving handler out of the core `Cas` facade.

Concrete SHA-256 vectors are checked by executing `Word.wf`. They do
not carry a kernel proof that SHA-256 is injective. Formal callers that
do possess a proof use `Word.Admitted` instead.
-/

namespace Cas.Vectors

/-- The vector format version. -/
inductive VectorFormat where
  | v1
  deriving DecidableEq

namespace VectorFormat

def number : VectorFormat → Nat
  | .v1 => 1

end VectorFormat

/-- The digest algorithm and framing scheme named by the vector. -/
inductive DigestAlgorithm where
  | sha256Scheme0
  deriving DecidableEq

namespace DigestAlgorithm

def name : DigestAlgorithm → String
  | .sha256Scheme0 => "sha256-scheme0"

end DigestAlgorithm

/-- Backwards-compatible scalar views of the current closed tags. -/
def formatVersion : Nat := VectorFormat.v1.number
def digestScheme : String := DigestAlgorithm.sha256Scheme0.name

/-- The tail grammar for a kebab-case fixture stem. -/
def validVectorNameTail : List Char → Bool
  | [] => true
  | '-' :: next :: rest =>
    (next.isLower || next.isDigit) && validVectorNameTail rest
  | '-' :: [] => false
  | char :: rest =>
    (char.isLower || char.isDigit) && validVectorNameTail rest

/-- Kebab-case fixture stems: lowercase ASCII letters, digits, and
single interior hyphens. -/
def validVectorName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
    (first.isLower || first.isDigit) && validVectorNameTail rest

/-- A fixture stem proven suitable for a platform-neutral file name. -/
structure VectorName where
  value : String
  valid : validVectorName value = true
  deriving DecidableEq

instance : ToString VectorName where
  toString name := name.value

/-- A natural count that can be represented by the schema plane's
language-neutral safe integer. -/
structure Count where
  value : Nat
  isSafe : value ≤ Schema.maxSafeNat

namespace Count

def ofNat? (value : Nat) : Option Count :=
  if h : value ≤ Schema.maxSafeNat then some ⟨value, h⟩ else none

def toSafeInt (count : Count) : Schema.SafeInt :=
  ⟨Int.ofNat count.value, by simpa using count.isSafe⟩

end Count

/-- Byte-width scalar converted losslessly to a safe integer. -/
def safeOfUInt8 (byte : UInt8) : Schema.SafeInt :=
  ⟨Int.ofNat byte.toNat, by
    show byte.toNat ≤ Schema.maxSafeNat
    exact Nat.le_trans (Nat.le_of_lt byte.toNat_lt) (by decide)⟩

/-- Failures at the candidate/check/registry boundary. -/
inductive VectorError where
  | wordNotAdmitted (name : VectorName)
  | duplicateName (name : VectorName)
  | bindingCountOutOfRange (name : VectorName) (count : Nat)

def VectorError.message : VectorError → String
  | .wordNotAdmitted name =>
    s!"vector {name}: word does not admit (Word.wf = false)"
  | .duplicateName name =>
    s!"vector registry repeats the name {name}"
  | .bindingCountOutOfRange name count =>
    s!"vector {name}: binding count {count} exceeds the safe-integer boundary"

/-- A named replay candidate. Non-emptiness makes its root total. -/
structure ConformanceVector where
  name : VectorName
  description : String
  word : NonemptyWord

namespace ConformanceVector

def fileName (vector : ConformanceVector) : String :=
  vector.name.value ++ ".json"

def root (vector : ConformanceVector) : Binding := vector.word.root

def bindingCount (vector : ConformanceVector) : Nat := vector.word.length

end ConformanceVector

/-- A candidate that passed the executable admission scan. The
constructor is private: external code must call `ConformanceVector.check`. -/
structure CheckedConformanceVector where
  private mk ::
  vector : ConformanceVector
  wordWf : Word.wf vector.word.word = true

namespace ConformanceVector

def check (vector : ConformanceVector) :
    Except VectorError CheckedConformanceVector :=
  if h : Word.wf vector.word.word = true then
    .ok ⟨vector, h⟩
  else
    .error (.wordNotAdmitted vector.name)

end ConformanceVector

namespace CheckedConformanceVector

def name (vector : CheckedConformanceVector) : VectorName :=
  vector.vector.name

def description (vector : CheckedConformanceVector) : String :=
  vector.vector.description

def word (vector : CheckedConformanceVector) : NonemptyWord :=
  vector.vector.word

def fileName (vector : CheckedConformanceVector) : String :=
  vector.vector.fileName

def root (vector : CheckedConformanceVector) : Binding :=
  vector.vector.root

def bindingCount (vector : CheckedConformanceVector) : Nat :=
  vector.vector.bindingCount

/-- The checked vector as the proof-bearing word used by formal
consumers; this witnesses the executable admission judgment only. -/
def admittedWord (vector : CheckedConformanceVector) : Word.Admitted where
  word := vector.word
  wf := vector.wordWf

end CheckedConformanceVector

private def firstDuplicate? : List VectorName → Option VectorName
  | [] => none
  | name :: rest =>
    if name ∈ rest then some name else firstDuplicate? rest

private theorem firstDuplicate_eq_none_iff : ∀ names : List VectorName,
    firstDuplicate? names = none ↔ names.Nodup
  | [] => by simp [firstDuplicate?]
  | name :: rest => by
    by_cases h : name ∈ rest
    · simp [firstDuplicate?, h]
    · simp [firstDuplicate?, h, firstDuplicate_eq_none_iff rest]

private def checkVectors : List ConformanceVector →
    Except VectorError (List CheckedConformanceVector)
  | [] => .ok []
  | vector :: rest => do
    let checked ← vector.check
    let checkedRest ← checkVectors rest
    pure (checked :: checkedRest)

/-- One checked registry with unique fixture names. -/
structure VectorRegistry where
  private mk ::
  vectors : List CheckedConformanceVector
  uniqueNames : (vectors.map CheckedConformanceVector.name).Nodup

namespace VectorRegistry

def check (candidates : List ConformanceVector) :
    Except VectorError VectorRegistry := do
  let checked ← checkVectors candidates
  let names := checked.map CheckedConformanceVector.name
  match hdup : firstDuplicate? names with
  | some name => .error (.duplicateName name)
  | none => .ok ⟨checked, (firstDuplicate_eq_none_iff names).mp hdup⟩

def length (registry : VectorRegistry) : Nat := registry.vectors.length

end VectorRegistry

/-! ## Named wire records

These records deliberately use encoded JSON carriers (`String` and
`SafeInt`). Refining arbitrary strings into canonical hex belongs to a
future schema-refinement constructor; the domain side already retains
`Bytes` and `Addr32`, so no unvalidated string enters store semantics.
-/

namespace Wire

structure VectorRef where
  expectedTag : Schema.SafeInt
  id : String

structure VectorNode where
  version : Schema.SafeInt
  tag : Schema.SafeInt
  payload : String
  refs : List VectorRef

structure VectorBinding where
  address : String
  node : VectorNode

structure VectorDocument where
  schemaVersion : VectorFormat
  digest : DigestAlgorithm
  name : String
  description : String
  word : List VectorBinding

structure IndexEntry where
  name : String
  file : String
  description : String
  bindings : Schema.SafeInt
  root : String

structure VectorIndex where
  schemaVersion : VectorFormat
  digest : DigestAlgorithm
  vectors : List IndexEntry

def ofRef (ref : Ref) : VectorRef where
  expectedTag := safeOfUInt8 ref.expectedTag
  id := hexS ref.addr.val

def ofNode (node : Node) : VectorNode where
  version := safeOfUInt8 node.version
  tag := safeOfUInt8 node.tag
  payload := hexS node.payload
  refs := node.refs.map ofRef

def ofBinding (binding : Binding) : VectorBinding where
  address := hexS binding.address.val
  node := ofNode binding.node

def ofVector (vector : CheckedConformanceVector) : VectorDocument where
  schemaVersion := .v1
  digest := .sha256Scheme0
  name := vector.name.value
  description := vector.description
  word := vector.word.word.map ofBinding

def indexEntry (vector : CheckedConformanceVector) :
    Except VectorError IndexEntry := do
  let count ← match Count.ofNat? vector.bindingCount with
    | some count => pure count
    | none => throw (.bindingCountOutOfRange vector.name vector.bindingCount)
  pure {
    name := vector.name.value
    file := vector.fileName
    description := vector.description
    bindings := count.toSafeInt
    root := hexS vector.root.address.val
  }

def index (registry : VectorRegistry) : Except VectorError VectorIndex := do
  let entries ← registry.vectors.mapM indexEntry
  pure {
    schemaVersion := .v1
    digest := .sha256Scheme0
    vectors := entries
  }

end Wire

end Cas.Vectors
