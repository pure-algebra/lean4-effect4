import Effect4.Codegen.Types

/-!
# Effect4.Laws.Codegen.TargetOrder

Owner: a model of tsgo's assignability on the target types the printer writes
(`docs/research/2026-10-11-type-interface/README.md`, R-T3). `TypeRef` in lean4-typescript is
syntax only, so the type interface's first law, that the printer is monotone into the target's
order, had no statement. `assignable` is that order, transcribed rule by rule from tsgo's
source at the pinned build's date (microsoft/typescript-go `e7efb4b210`, 2026-06-29, the commit
on or before `@typescript/native-preview` 7.0.0-dev.20260629.1). Each rule names the function it
transcribes. The excerpts that decide the discriminated decomposition are filed in
`docs/research/2026-10-11-type-interface/sources/`.

The fragment is the printer's image: the keyword types, string literals, readonly tuples,
unions, object types of readonly fields, and the named Effect types at their declared variances
(`vendor/effect-4.0.0-rc.112/src`: `Option.ts` `None<out A>` and `Some<out A>`; `Result.ts` and
`Exit.ts` `Success<out A, out E>` and `Failure<out A, out E>`; `Cause.ts` `Cause<out E>`;
`Fiber.ts` `Fiber<out A, out E>`; `Ref.ts` `Ref<in out A>`; `Deferred.ts`
`Deferred<in out A, in out E>`). The compiler flags are the lanes': `strict` and
`exactOptionalPropertyTypes`.

Placement:

- Concept: `subtyping-algebra`, the target half of law 1.
- Question: the proposed claim `sub-print-sound`. Its statement waits for repair A (row 346): a
  planned goal that a registered counterexample refutes would let a proof derive anything. Until
  then the battery states `E4-PRINT-CE-001` in this model's terms.
- Reach: the printer's fragment. A function type, an intersection, a generic type parameter, an
  index signature other than `Readonly<Record<string, V>>`, and an enum are outside it.
- Consumers: the finite check against tsgo's verdicts in `generated/assignability.tsv`
  (`Test/Codegen/TargetOrder.lean`), and repair A's slice.

What this module does not claim: that tsgo computes this relation. The model is a
transcription, and its evidence is the finite check against tsgo's recorded verdicts.
-/

set_option autoImplicit false

namespace Effect4.Codegen.TargetOrder

open TypeScript

/-! ## A size, for the recursion bound -/

mutual
/-- A structural size of a target type. -/
def size : TypeRef → Nat
  | .name _ args => 1 + sizeList args
  | .literal _ => 1
  | .tuple items _ => 1 + sizeList items
  | .union members => 1 + sizeList members
  | .object fields => 1 + sizeFields fields
  | .function params result => 1 + sizeParams params + size result

/-- The size of a list of target types. -/
def sizeList : List TypeRef → Nat
  | [] => 0
  | x :: xs => size x + sizeList xs

/-- The size of a list of fields. -/
def sizeFields : List TypeRef.Field → Nat
  | [] => 0
  | f :: fs => size f.type + sizeFields fs

/-- The size of a list of parameters. -/
def sizeParams : List (String × TypeRef) → Nat
  | [] => 0
  | p :: ps => size p.2 + sizeParams ps
end

/-! ## The named types and their variances -/

/-- How a named type relates its arguments. -/
inductive Variance where
  /-- Covariant: `out` in the declaration. -/
  | out
  /-- Invariant: `in out` in the declaration, or an exact key. -/
  | inout
  deriving DecidableEq

/-- The variances of the named types the printer writes; `none` for any other name, which then
relates only to itself. -/
def variances : List String → Option (List Variance)
  | ["Option", "Option"] => some [.out]
  | ["ReadonlyArray"] => some [.out]
  | ["Result", "Result"] => some [.out, .out]
  | ["Exit", "Exit"] => some [.out, .out]
  | ["Cause", "Cause"] => some [.out]
  | ["Fiber", "Fiber"] => some [.out, .out]
  | ["Ref", "Ref"] => some [.inout]
  | ["Deferred", "Deferred"] => some [.inout, .inout]
  | ["Readonly"] => some [.out]
  | ["Record"] => some [.inout, .out]
  | _ => none

/-- A keyword type: `.name [k] []`. -/
def keyword (k : String) : TypeRef := .name [k] []

/-- The members of a type as a union source: a union's members, or the type itself. -/
def members : TypeRef → List TypeRef
  | .union xs => xs
  | t => [t]

/-- `countTypes` (`internal/checker/checker.go`): a union counts its members, `never` zero, any
other type one. -/
def countTypes : TypeRef → Nat
  | .union xs => xs.length
  | .name ["never"] [] => 0
  | _ => 1

/-- A position is a discriminant of a union of tuples when its types differ across the
constituents and one of them is a string literal (`isDiscriminantProperty`, flags
`CheckFlagsNonUniformAndLiteral`). -/
def tupleDiscriminant (targets : List (List TypeRef)) (i : Nat) : Bool :=
  let at_ : List (Option TypeRef) := targets.map fun items => items[i]?
  (at_.any fun t => match t with | some (TypeRef.literal _) => true | _ => false) &&
    (at_.any fun t => t != at_.head?.join)

/-- Every choice of one member per discriminant position: the combinations of
`typeRelatedToDiscriminatedType`, as lists of `(position, member)`. -/
def combinations : List (Nat × List TypeRef) → List (List (Nat × TypeRef))
  | [] => [[]]
  | (i, ms) :: rest => ms.flatMap fun m => (combinations rest).map fun c => (i, m) :: c

/-! ## The order -/

/-- **The model of tsgo's assignability** on the printer's fragment, at a recursion bound. Each
arm names the tsgo function it transcribes (`internal/checker/relater.go`). Every recursive call
is on a piece strictly inside the compared types, so the bound `size s + size t + 1` of
`assignable` is never exhausted on a call it starts. -/
def rel : Nat → TypeRef → TypeRef → Bool
  | 0, _, _ => false
  | n + 1, s, t =>
    if s == t then true
    else match s, t with
    -- `isSimpleTypeRelatedTo`: `never` is below every type, every type is below `unknown`,
    -- and nothing other than `never` is below `never`.
    | .name ["never"] [], _ => true
    | _, .name ["unknown"] [] => true
    | _, .name ["never"] [] => false
    -- `unionOrIntersectionRelatedTo`, `eachTypeRelatedToType`: a union source relates when
    -- each member does.
    | .union ss, _ => ss.all fun x => rel n x t
    -- `typeRelatedToSomeType`: a union target relates when one member does; otherwise the
    -- discriminated decomposition of a tuple source (`typeRelatedToDiscriminatedType`).
    | .tuple ss _, .union ts =>
      ts.any (rel n s ·) ||
        let targets := ts.filterMap fun
          | .tuple items _ => if items.length == ss.length then some items else none
          | _ => none
        let positions := (List.range ss.length).filter (tupleDiscriminant targets)
        let product := positions.foldl (fun k i => k * ((ss[i]?.map countTypes).getD 1)) 1
        if positions.isEmpty || product == 0 || 25 < product then false
        else
          -- for each combination, the constituents whose discriminants relate
          let found := (combinations (positions.map fun i => (i, (ss[i]?.map members).getD []))).map
            fun combination => targets.filter fun items =>
              combination.all fun (i, m) => match items[i]? with
                | some item => rel n m item
                | none => false
          -- every combination matches one, and every match takes the other elements
          (found.all fun ms => !ms.isEmpty) &&
            (found.flatten.all fun items =>
              (List.range ss.length).all fun i =>
                positions.contains i ||
                  match ss[i]?, items[i]? with
                  | some a, some b => rel n a b
                  | _, _ => false)
    | _, .union ts => ts.any (rel n s ·)
    -- `isSimpleTypeRelatedTo`: a string literal is below `string`; `undefined` is below `void`.
    | .literal _, .name ["string"] [] => true
    | .name ["undefined"] [], .name ["void"] [] => true
    -- `propertiesRelatedTo` on tuples: one arity, a readonly source only into a readonly target,
    -- and each element related.
    | .tuple ss sr, .tuple ts tr =>
      ss.length == ts.length && (tr || !sr) && (ss.zip ts).all fun (a, b) => rel n a b
    -- A tuple is an array of its elements' union: below `ReadonlyArray<A>` when each element is.
    | .tuple ss _, .name ["ReadonlyArray"] [a] => ss.all fun x => rel n x a
    -- `propertiesRelatedTo` on objects: each target field is present in the source, required
    -- only if the source's is, and related; a source keeps any other field (width). `readonly`
    -- is not compared.
    | .object fs, .object gs =>
      gs.all fun g => match fs.find? (·.name == g.name) with
        | none => g.optional
        | some f => (g.optional || !f.optional) && rel n f.type g.type
    -- `structuredTypeRelatedTo` on references: one name, one arity, each argument at its
    -- declared variance; a name without a declared variance relates only to itself.
    | .name nm as, .name nm' bs =>
      nm == nm' && as.length == bs.length &&
        match variances nm with
        | none => false
        | some vs => ((as.zip bs).zip vs).all fun ((a, b), v) =>
          match v with
          | .out => rel n a b
          | .inout => rel n a b && rel n b a
    | _, _ => false

/-- The order, at the bound its arguments' sizes give. -/
def assignable (s t : TypeRef) : Bool := rel (size s + size t + 1) s t

end Effect4.Codegen.TargetOrder
