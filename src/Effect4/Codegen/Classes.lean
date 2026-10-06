import Effect4.Codegen.Record
import Effect4.Program.Formation

/-!
# Codegen.Classes — the error payload face: one `Data.TaggedError` class per tagged payload type

Decisions row 120, ruling (b): the face prints one `Data.TaggedError` class per tagged payload
type, named by its tag, and constructs a payload with `new`. A record type is a payload class
when `Types.payloadClass?` names it: its fields are a tagged payload record type
(`payloadRecordTy`) and its tag is a target identifier. The type prints as the class name
(`Types.ofTy`), wherever a type prints.

Three images live here.

* **The construction.** A record construction in the class form (`classTag?`: its declared
  fields are a payload class, `_tag` is its first field, its first name and its first value, the
  tag's literal) prints as `new Tag({ f: v, … })` with `_tag` omitted (`writeClass`), because
  rc.112's constructor takes the fields without it (`vendor/effect-4.0.0-rc.112/src/Data.ts`,
  `TaggedError`: `P extends "_tag" ? never : P`). The object keeps the record's one key form
  (decisions row 196). The image carries no field declaration, so the reader takes the module's
  classes (`Classes`, tag ↦ fields) as a parameter: `readClass` recovers the tag, the names and
  the value expressions, and the term reader restores the fields and `_tag` from the classes.
* **The class declaration.** `export class Tag extends Data.TaggedError("Tag")<{ readonly f: T; … }> {}`
  (`classDecl`): the fields after `_tag`, in their written order, each type as `ofTy` spells it.
  `readClassDecl` reads it back through the field-type reader `readTy` and accepts exactly what
  `classDecl` prints (it re-prints and compares). TypeScript's spelling erases distinctions
  (`number` is `nat` and `number`; a union is printed flat), so the classes a module can declare
  are those whose declaration reads back: the domain is decided where the module prints
  (`ClassTable.checkedDecl`), never assumed.
* **Coverage.** `Term.covers classes t`: every class construction of `t` names a class with its
  declared fields. It is the premise the term round trip reads under (`readTerm_printTerm`).

What this module does not establish: that tsgo accepts the printed module (finite controls,
`ts/eff/test/payload-classes.typecheck.ts`), that rc.112 behaves as the model (the truth lane),
or that every payload type has a readable class (the module refuses the others by name).
-/

set_option autoImplicit false

namespace Effect4.Codegen.Classes

open Effect4.Program TypeScript

/-- A record type's declared fields, `_tag` included: the raw declaration a construction carries. -/
abbrev Fields := List (String × Bool × Ty)

/-- The payload classes a module declares, by tag: the reading environment of `new Tag({ … })`.
The first entry of a tag is the one a reader uses. -/
abbrev Classes := List (String × Fields)

/-- The first value of an argument list. -/
def firstTerm : Terms → Option Term
  | .nil => none
  | .cons head _ => some head

/-- The values after the first. -/
def restTerms : Terms → Terms
  | .nil => .nil
  | .cons _ tail => tail

/-- The class a record construction prints as (decisions row 120, ruling (b)): its tag, when the
declared fields are a payload class (`Types.payloadClass?`), `_tag` is the first declared field,
the first supplied name and supplied by the tag's literal, no later name repeats `_tag`, and the
other names pair one for one with the other values. Every other construction prints as the
structural record (`Record.writeRecord`). -/
def classTag? (fields : Fields) (names : List String) (values : Terms) : Option String := do
  let tag ← Types.payloadClass? fields
  if fields.head? = some ("_tag", false, .lit tag) ∧ names.head? = some "_tag" ∧
      firstTerm values = some (.lit (.str tag)) ∧ "_tag" ∉ names.tail ∧
      names.tail.length = (restTerms values).toList.length then some tag else none

/-- `new Tag({ f: v, … })`: a class construction, `_tag` omitted, the other names in their written
order with the literal's one key form (decisions row 196). -/
def writeClass (tag : String) (names : List String) (values : List Expr) : Expr :=
  .new (.ident tag) [.objectWith (Record.keyForm names) (Record.properties names values)]

/-- The tag, the names and the value expressions of exactly `writeClass`'s image: a `new` of an
identifier at one object literal of properties, in the key form its names choose. -/
def readClass : Expr → Option (String × List String × List Expr)
  | .new (.ident tag) [.objectWith form entries] =>
    (Record.readProperties entries).bind fun pairs =>
      if form = Record.keyForm (pairs.map Prod.fst) then
        some (tag, pairs.map Prod.fst, pairs.map Prod.snd)
      else none
  | _ => none

/-- Exact-codecs termination helper for the term reader's class branch: the value expressions a
construction reads to are smaller than it. Serves `readTerm` (R8 through `read_exact`). -/
theorem readClass_size (e : Expr) (tag : String) (names : List String) (values : List Expr)
    (h : readClass e = some (tag, names, values)) : sizeOf values < sizeOf e := by
  unfold readClass at h
  split at h
  · next tag' form entries =>
    obtain ⟨pairs, hpairs, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
      have hs := Record.readProperties_size entries pairs hpairs
      simp only [Expr.new.sizeOf_spec, List.cons.sizeOf_spec, Expr.objectWith.sizeOf_spec]
      omega
    · exact nomatch h
  · exact nomatch h

/-! ## The field-type reader -/

/-- A named type at its arguments' readings, at one choice per spelling: `number` reads as `nat`,
and `Readonly<Record<string, V>>` as a map. A class name reads as nothing: a class's field naming
another class has no reading here. `never` reads as the empty type (the state plan's T5, part B):
the error column of `Deferred.make<A, never>()` is spelled so. A handle's name (`Ref.Ref<A>`,
`Deferred.Deferred<A, E>`) and `unknown` read as nothing. -/
def readNamed : List String → List Ty → Option Ty
  | ["number"], [] => some .nat
  | ["string"], [] => some .string
  | ["boolean"], [] => some .bool
  | ["void"], [] => some .unit
  | ["never"], [] => some .never
  | ["null"], [] => some .null
  | ["undefined"], [] => some .undefined
  | ["Uint8Array"], [] => some .bytes
  | ["Option", "Option"], [x] => some (.option x)
  | ["ReadonlyArray"], [x] => some (.list x)
  | ["Result", "Result"], [v, e] => some (.except e v)
  | ["Record"], [.string, v] => some (.map .string v)
  | ["Readonly"], [.map k v] => some (.map k v)
  | _, _ => none

mutual
  /-- A payload field's type from its printed spelling (`Types.ofTy`'s image): a name through
  `readNamed`, a literal, `readonly [A, B]` as a product and any other readonly tuple as a tuple, an
  object as a record, a union as the right-nested union of its members. The reader is permissive;
  the class reader accepts a reading only when printing it gives the spelling back. -/
  def readTy : TypeRef → Option Ty
    | .name qualified args => do
      let xs ← readTys args
      readNamed qualified xs
    | .literal value => some (.lit value)
    | .tuple items readonly => do
      let xs ← readTys items
      if readonly then
        match xs with
        | [x, y] => some (.prod x y)
        | _ => some (.tuple xs)
      else none
    | .union members => (readTys members).map Ty.ofMembers
    | .object fields => (readFieldTys fields).map .record
    | .function _ _ => none
  termination_by structural t => t

  /-- The items of a tuple or a union, in order. -/
  def readTys : List TypeRef → Option (List Ty)
    | [] => some []
    | t :: ts => do
      let x ← readTy t
      let xs ← readTys ts
      some (x :: xs)
  termination_by structural ts => ts

  /-- An object type's fields, in order. -/
  def readFieldTys : List TypeRef.Field → Option (List (String × Bool × Ty))
    | [] => some []
    | f :: fs => do
      let x ← readFieldTy f
      let xs ← readFieldTys fs
      some (x :: xs)
  termination_by structural fs => fs

  /-- One readonly field: its name, its optional flag and its type. -/
  def readFieldTy : TypeRef.Field → Option (String × Bool × Ty)
    | ⟨name, readonly, optional, type⟩ => do
      let x ← readTy type
      if readonly then some (name, optional, x) else none
  termination_by structural f => f
end

/-! ## The checked type reader

One reader for the places where the faces print a program type (the state plan's T5, part B).
Two of the three read their type back, and only through this reader: the type arguments an
operation carries on its call's head (`Deferred.make<A, E>()`, `installTypeArgs`,
`Codegen/Read.lean`), and a loop's stated cursor type (`readLeaf`). The third, a list fold's
stated accumulator type, is printed and not read yet. The class reader below checks a whole
declaration by the same re-print. -/

/-- **The checked type reader**: a program type from its printed spelling (`readTy`), kept only
when the type printer prints that type as this spelling (`Types.ofTy`). What it accepts is exact
by its definition (`readTyChecked_exact`, `Laws/Codegen/Classes.lean`). The check does not make
the printer injective: two types can share one spelling, and the reader answers one of them
(`ReadableTy`). -/
def readTyChecked (x : TypeRef) : Option Ty :=
  (readTy x).bind fun ty => if Types.ofTy ty = some x then some ty else none

/-- **The readable types**: a type that the checked reader answers from its own printed spelling.
It is the premise of every retraction through `readTyChecked`
(`readTyChecked_of_readable`, `Laws/Codegen/Classes.lean`), decided by running the round trip.
A type is outside it for one of four reasons, and each stays visible here.

* **No printed form** (`Types.ofTy` answers `none`): a row template's parameter, a nominal
  application at arguments, a map whose key is no string, and a handle whose legacy name does
  not parse.
* **A collision**: `int` and `number` print as `number`, which reads as `nat`; a union whose
  members collapse in the target prints as one member.
* **A spelling with no reading**: `unknown`; `Ref.Ref<A>`, `Deferred.Deferred<A, E>`,
  `Exit.Exit<A, E>`, `Cause.Cause<E>` and `Fiber.Fiber<A, E>`; the scope handle and every other
  handle; a tagged payload record, which prints as the name of its class.
* **Not the reader's choice for its spelling**: `readonly [A, B]` reads as a product, never as
  a tuple of two items, and a type outside normal form prints as its normal form (a union in
  another order of members, for one).

A type that holds one of these is outside too. -/
def ReadableTy (ty : Ty) : Bool :=
  decide ((Types.ofTy ty).bind readTyChecked = some ty)

/-- The printed forms of a list of types, in order; `none` when one has no printed form. -/
def writeTys : List Ty → Option (List TypeRef)
  | [] => some []
  | ty :: tys => do
    let x ← Types.ofTy ty
    let xs ← writeTys tys
    some (x :: xs)

/-- A list of types from their printed spellings, each through the checked reader. -/
def readTysChecked : List TypeRef → Option (List Ty)
  | [] => some []
  | x :: xs => do
    let ty ← readTyChecked x
    let tys ← readTysChecked xs
    some (ty :: tys)

/-! ## The class declaration -/

/-- The class's type argument: the fields after `_tag`, in their written order, `readonly`, each
with its optional flag and its type as `ofTy` spells it. `none` when a type has no spelling. -/
def classFields? (fields : Fields) : Option (List TypeRef.Field) :=
  fields.tail.mapM fun (name, optional, type) =>
    (Types.ofTy type).map fun target => { name, readonly := true, optional, type := target }

/-- `export class Tag extends Data.TaggedError("Tag")<{ readonly f: T; … }> {}` (decisions row
120, ruling (b)): the heritage is the call `Data.TaggedError("Tag")` at the field record. -/
def classDecl (tag : String) (fields : Fields) : Option ClassDecl :=
  (classFields? fields).map fun fs =>
    { doc := [], name := tag
      heritage := some (.generic (.call (.ident "Data.TaggedError") [.str tag]) [.object fs])
      members := [], exported := true }

/-- A class declaration back to its tag and fields: the tag from the heritage call, `_tag` first,
then the field record through `readTy`. Exactly `classDecl`'s image: the reading is accepted only
when the declaration is what `classDecl` prints of it. -/
def readClassDecl (c : ClassDecl) : Option (String × Fields) :=
  match c.heritage with
  | some (.generic (.call (.ident head) [.str tag]) [.object fs]) => do
    let rest ← readFieldTys fs
    let fields := ("_tag", false, .lit tag) :: rest
    if head = "Data.TaggedError" ∧ c.doc = [] ∧ c.name = tag ∧ c.members = [] ∧
        c.exported = true ∧ (classFields? fields).map TypeRef.object = some (.object fs) then
      some (tag, fields)
    else none
  | _ => none

/-- A module's leading class declarations back to its classes, in order. The classes a module
can declare are those whose declaration reads back, decided where the module prints
(`ClassTable.checkedDecl`). -/
def readClassDecls (decls : List ClassDecl) : Option Classes := decls.mapM readClassDecl

end Effect4.Codegen.Classes

namespace Effect4.Program

open Effect4.Codegen.Classes (Classes classTag?)

/-- One node's coverage (decisions row 120): a class construction names a class whose fields are
its declared fields; every other node is covered. -/
def coverNode (classes : Classes) : Term → Bool
  | .record fields names values => match classTag? fields names values with
    | some tag => decide (classes.lookup tag = some fields)
    | none => true
  | _ => true

/-- The classes cover a term: every class construction in it is covered (`coverNode`). The
generated term fold, so a node's coverage is its own check and its children's. -/
def Term.covers (classes : Classes) (t : Term) : Bool :=
  foldMap_term true (· && ·) t (f_term := coverNode classes)

/-- The classes cover every term of an argument list. -/
def Terms.covers (classes : Classes) (ts : Terms) : Bool :=
  foldMap_terms true (· && ·) ts (f_term := coverNode classes)

/-- The classes cover every term of a cause. -/
def CauseTerm.covers (classes : Classes) (c : CauseTerm) : Bool :=
  foldMap_cause true (· && ·) c (f_cause := fun node => match node with
    | .fail t | .die t => t.covers classes
    | .interrupt who => who.all (·.covers classes)
    | .both _ _ => true)

/-! ## The record constructions of a program -/

/-- One record construction: its declared fields, its names and its values. -/
abbrev RecordSite := List (String × Bool × Ty) × List String × Terms

/-- Every record construction of a term, by the generated term fold, in preorder. -/
def termRecords (t : Term) : List RecordSite :=
  foldMap_term [] (· ++ ·) t (f_term := fun node => match node with
    | .record fields names values => [(fields, names, values)]
    | _ => [])

/-- Every record construction of a cause's terms. -/
def causeRecords (c : CauseTerm) : List RecordSite :=
  foldMap_cause [] (· ++ ·) c (f_cause := fun node => match node with
    | .fail t | .die t => termRecords t
    | .interrupt who => who.toList.flatMap termRecords
    | .both _ _ => [])

/-- The record constructions of one node's leaves, through the generated view (no second
program-constructor match), as `Formation.argumentAnnotations` reads them. An operation
argument is read through the alphabet's own view of its binder term (`ScopedOp.term?`): the
faces print that term (the state plan's T5), so a class construction inside it is a
construction of the module, whose class the module declares with the construction's own
fields. -/
def argumentRecords {Op : Type} [ScopedOp Op] : ArgF Op (EffSelfCarrier Op) → List RecordSite
  | .term t => termRecords t
  | .cause c => causeRecords c
  | .optTerm t => t.toList.flatMap termRecords
  | .op op => (ScopedOp.term? op).toList.flatMap termRecords
  | _ => []

/-- One node's record constructions. -/
def nodeRecords {Op : Type} [ScopedOp Op] (fam : EffFam) (node : EffSelfCarrier Op fam) :
    List RecordSite :=
  (view fam node).2.flatMap argumentRecords

/-- Every record construction of a program, layers included, by the generated program fold. -/
def programRecords {Op : Type} [ScopedOp Op] (program : Eff Op) : List RecordSite :=
  foldMap_eff [] (· ++ ·) program
    (f_eff := nodeRecords .eff) (f_stmt := nodeRecords .stmt) (f_stmts := nodeRecords .stmts)
    (f_effs := nodeRecords .effs) (f_action := nodeRecords .action)
    (f_layer := nodeRecords .layer) (f_layers := nodeRecords .layers)

/-- The classes a program's constructions name, each with its declared fields, in preorder: the
reading environment its module declares (`Codegen/ClassTable.lean` checks that the
constructions agree). -/
def classesOf {Op : Type} [ScopedOp Op] (program : Eff Op) : Classes :=
  (programRecords program).filterMap fun (fields, names, values) =>
    (classTag? fields names values).map fun tag => (tag, fields)

end Effect4.Program
