import Effect4.Program.Ty
import Effect4.Store.Carrier.Val

open Effect4 Effect4.Store

namespace ConstructiveProjection

/-! ## 1. Mini Types & Constructive Lexicographic Canonicalizer -/

inductive MiniTy where
  | record (fields : List (String × MiniTy))
  | nat
  | string

mutual
  def beqTy : MiniTy → MiniTy → Bool
    | .nat, .nat => true
    | .string, .string => true
    | .record fs1, .record fs2 => beqFields fs1 fs2
    | _, _ => false

  def beqFields : List (String × MiniTy) → List (String × MiniTy) → Bool
    | [], [] => true
    | (k1, t1) :: r1, (k2, t2) :: r2 => k1 == k2 && beqTy t1 t2 && beqFields r1 r2
    | _, _ => false
end

instance : BEq MiniTy := ⟨beqTy⟩

/-- Constructive lexicographic UTF-8 comparator reusing Ty.ltKey (axiom-free). -/
def stringLt (s1 s2 : String) : Bool :=
  Effect4.Program.Ty.ltKey (s1.toUTF8.data.toList.map UInt8.toNat)
    (s2.toUTF8.data.toList.map UInt8.toNat)

/-- Insert an entry into an association list sorted by key. -/
def insertSorted {α : Type} (k : String) (v : α) : List (String × α) → List (String × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if stringLt k k' then (k, v) :: (k', v') :: rest
      else (k', v') :: insertSorted k v rest

/-- Sort fields canonically by key. -/
def sortFields {α : Type} (fields : List (String × α)) : List (String × α) :=
  fields.foldl (fun acc (k, v) => insertSorted k v acc) []

/-- Check if all field names in an association list are unique. -/
def keysNodup {α : Type} (fields : List (String × α)) : Bool :=
  let rec go (seen : List String) : List (String × α) → Bool
    | [] => true
    | (k, _) :: rest => if seen.contains k then false else go (k :: seen) rest
  go [] fields

/-- Lookup field index and type in a canonically sorted record layout. -/
def fieldLookup (fields : List (String × MiniTy)) (name : String) : Option (Nat × MiniTy) :=
  let rec go (idx : Nat) : List (String × MiniTy) → Option (Nat × MiniTy)
    | [] => none
    | (k, t) :: rest => if k == name then some (idx, t) else go (idx + 1) rest
  go 0 fields

/-! ## 2. Checked Term Representation with Canonical Alignment -/

inductive Term where
  | var (name : String)
  | litNat (n : Nat)
  | litStr (s : String)
  | recordMake (fields : List (String × Term))
  | recordProj (target : Term) (label : String) (index : Nat)

mutual
  def typeCheck (env : String → Option MiniTy) : Term → Option MiniTy
    | .var x => env x
    | .litNat _ => some .nat
    | .litStr _ => some .string
    | .recordMake fields => do
        if !keysNodup fields then none  -- Refuse duplicate keys on entry!
        let typedFields ← typeCheckFields env fields
        let canonicalFields := sortFields typedFields  -- Canonical sort!
        some (.record canonicalFields)
    | .recordProj target label index => do
        let targetTy ← typeCheck env target
        match targetTy with
        | .record canonicalFields => do
            let (actualIdx, fieldTy) ← fieldLookup canonicalFields label
            if actualIdx == index then some fieldTy else none
        | _ => none

  def typeCheckFields (env : String → Option MiniTy) : List (String × Term) → Option (List (String × MiniTy))
    | [] => some []
    | (k, t) :: rest => do
        let ty ← typeCheck env t
        let restTys ← typeCheckFields env rest
        some ((k, ty) :: restTys)
end

mutual
  def eval (env : String → Option Val) : Term → Option Val
    | .var x => env x
    | .litNat n => some (.nat n)
    | .litStr s => some (.str s)
    | .recordMake fields => do
        let evaluatedFields ← evalFields env fields
        let canonicalFields := sortFields evaluatedFields
        let vs := canonicalFields.map Prod.snd
        some (.ctor 0 vs)
    | .recordProj target _ index => do
        match eval env target with
        | some (.ctor 0 vs) => vs[index]?
        | _ => none

  def evalFields (env : String → Option Val) : List (String × Term) → Option (List (String × Val))
    | [] => some []
    | (k, t) :: rest => do
        let v ← eval env t
        let vs ← evalFields env rest
        some ((k, v) :: vs)
end

/-! ## 3. Reusable Sorting Law Supporting Static Type/Value Alignment -/

/-- Sorting is key-only: mapping payloads commutes with inserting a field. -/
theorem insertSorted_mapPayload {α β : Type} (f : α → β) (k : String) (v : α)
    (xs : List (String × α)) :
    insertSorted k (f v) (xs.map (fun (name, x) => (name, f x))) =
      (insertSorted k v xs).map (fun (name, x) => (name, f x)) := by
  induction xs with
  | nil => rfl
  | cons kv xs ih =>
    rcases kv with ⟨name, x⟩
    change
      (if stringLt k name then
        (k, f v) :: (name, f x) :: xs.map (fun (n, a) => (n, f a))
       else (name, f x) :: insertSorted k (f v) (xs.map (fun (n, a) => (n, f a)))) =
      (if stringLt k name then (k, v) :: (name, x) :: xs
       else (name, x) :: insertSorted k v xs).map (fun (n, a) => (n, f a))
    cases stringLt k name with
    | false => exact congrArg (fun rest => (name, f x) :: rest) ih
    | true => rfl

/-- The fold accumulator transports through a payload map. -/
theorem sortFold_mapPayload {α β : Type} (f : α → β) (xs acc : List (String × α)) :
    (xs.map (fun (name, x) => (name, f x))).foldl
      (fun out (name, x) => insertSorted name x out)
      (acc.map (fun (name, x) => (name, f x))) =
    (xs.foldl (fun out (name, x) => insertSorted name x out) acc).map
      (fun (name, x) => (name, f x)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons kv xs ih =>
    rcases kv with ⟨name, x⟩
    simp only [List.map_cons, List.foldl_cons, insertSorted_mapPayload, ih]

/-- General model law: sorting preserves payload correspondence at each key.
Enables compiling static layouts once during preparation rather than dynamic sorting. -/
theorem sortFields_mapPayload {α β : Type} (f : α → β) (xs : List (String × α)) :
    sortFields (xs.map (fun (name, x) => (name, f x))) =
      (sortFields xs).map (fun (name, x) => (name, f x)) :=
  sortFold_mapPayload f xs []

/-! ## Asserting Controls -/

-- 1. Unsorted input [("b", 42), ("a", "hello")] is canonically sorted to [("a", string), ("b", nat)]
def unsortedRec : Term := .recordMake [("b", .litNat 42), ("a", .litStr "hello")]

#guard typeCheck (fun _ => none) unsortedRec ==
  some (.record [("a", .string), ("b", .nat)])

-- Valid access to 'a': index 0
def projA : Term := .recordProj unsortedRec "a" 0
#guard typeCheck (fun _ => none) projA == some .string
#guard eval (fun _ => none) projA == some (.str "hello")

-- Valid access to 'b': index 1
def projB : Term := .recordProj unsortedRec "b" 1
#guard typeCheck (fun _ => none) projB == some .nat
#guard eval (fun _ => none) projB == some (.nat 42)

-- 2. Rejecting Control: Accessing 'b' with written index 0 (which was its input position before canonicalization) FAILS!
def projBWrongWrittenIdx : Term := .recordProj unsortedRec "b" 0
#guard typeCheck (fun _ => none) projBWrongWrittenIdx == none

-- 3. Rejecting Control: Duplicate fields at formation are strictly REFUSED!
def dupRec : Term := .recordMake [("a", .litNat 1), ("a", .litNat 2)]
#guard typeCheck (fun _ => none) dupRec == none

-- 4. Environment test with canonical vs raw layouts
def rawEnv : String → Option MiniTy
  | "r" => some (.record [("b", .nat), ("a", .string)])
  | _ => none

#guard typeCheck rawEnv (.recordProj (.var "r") "b" 0) == some .nat
#guard typeCheck rawEnv (.recordProj (.var "r") "b" 1) == none

-- 5. Lexicographical UTF-8 byte ordering demonstration
#guard ((sortFields [("é", 0), ("aa", 1), ("a", 2), ("", 3), ("😀", 4)]).map Prod.fst) ==
  ["", "a", "aa", "é", "😀"]

/-! ## Axiom Audits -/
#print axioms stringLt
#print axioms typeCheck
#print axioms eval
#print axioms insertSorted_mapPayload
#print axioms sortFields_mapPayload

end ConstructiveProjection
