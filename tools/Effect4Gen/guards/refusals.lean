/-! Refusal acceptance (decisions row 17): every refusal an agent can be shown, written as content,
read back exactly, refused with a byte added or removed, and fitting its generated shape; two
refusals are distinct as bytes exactly when they are distinct values. -/
namespace RefusalsAcceptance
open Effect4 Effect4.Program Effect4.Api

def tables : List TableRefusal := [.notExternal 0, .notAsync 3]

def admissions : List AdmitRefusal :=
  [.illTyped, .duplicateKey ("Db", ["get"]), .builtinCollision ("Ref", ["get"]),
   .valueRowTrailing ("Clock", ["now"]), .table (.notAsync 2), .uninhabited ["program", "answer"],
   .internalHandle ["table", "1", "answer"], .emptyColumn ["table", "0", "request"]]

def scopes : List Authoring.Refusal :=
  [⟨[], .unbound "x"⟩, ⟨[0, 1], .unboundLayer "L"⟩, ⟨[2], .duplicateLayer "L"⟩,
   ⟨[], .placement "L"⟩, ⟨[3], .unboundRow "Db.get"⟩, ⟨[1], .reservedName "_%x"⟩,
   ⟨[], .duplicateRow "Db.get"⟩]

def typings : List TypeRefusal :=
  [⟨[1], .term (.var 3)⟩, ⟨[], .cause (.both (.fail (.lit (.nat 1))) (.interrupt none))⟩,
   ⟨[], .errorNotAdmitted .nat⟩, ⟨[0], .outsideDomain "Db.get"⟩,
   ⟨[], .requestNotSubtype "Db.get" .string .nat⟩, ⟨[], .predicateNotBool .nat⟩,
   ⟨[2], .notSelectable (.tag "Some") (.option .nat)⟩, ⟨[], .stepNotCursor .string .nat⟩,
   ⟨[], .initialNotCursor .bool .nat⟩, ⟨[], .releaseFails .string⟩, ⟨[], .notFiber .unit⟩,
   ⟨[], .serviceUnknown ⟨⟨3⟩, ⟨7⟩⟩⟩, ⟨[], .valueNotSubtype ⟨⟨3⟩, ⟨7⟩⟩ .string .nat⟩,
   ⟨[], .layerReference [0, 1]⟩, ⟨[], .referencesIllFormed⟩, ⟨[], .mergeAllEmpty⟩,
   ⟨[], .returnNotLast⟩, ⟨[], .breakOutsideLoop⟩, ⟨[], .literalOutsideAlphabet (.str "x")⟩]

def authors : List AuthorRefusal := scopes.map .scope ++ typings.map .typing

def prints : List PrintRefusal :=
  [.internalAction "fork", .layerRef [0, 2], .unsafeName "a0", .typeSpelling "Date"]

def reads : List ReadRefusal :=
  [.unknownHead "Cause.fail", .unknownIdent "x", .arity "Db.get", .binder "a1", .shape "call",
   .negative (-3), .unsupportedStmt, .annotation "lambda parameter"]

#guard tables.all fun x => Canonical.decode (α := TableRefusal) (Canonical.encode x) = some x
#guard admissions.all fun x => Canonical.decode (α := AdmitRefusal) (Canonical.encode x) = some x
#guard scopes.all fun x => Canonical.decode (α := Authoring.Refusal) (Canonical.encode x) = some x
#guard typings.all fun x => Canonical.decode (α := TypeRefusal) (Canonical.encode x) = some x
#guard authors.all fun x => Canonical.decode (α := AuthorRefusal) (Canonical.encode x) = some x
#guard prints.all fun x => Canonical.decode (α := PrintRefusal) (Canonical.encode x) = some x
#guard reads.all fun x => Canonical.decode (α := ReadRefusal) (Canonical.encode x) = some x
-- A byte added or removed is refused, never repaired.
#guard authors.all fun x => Canonical.decode (α := AuthorRefusal) (Canonical.encode x ++ [0]) = none
#guard authors.all fun x => Canonical.decode (α := AuthorRefusal) (Canonical.encode x).dropLast = none
#guard reads.all fun x => Canonical.decode (α := ReadRefusal) (Canonical.encode x ++ [0]) = none
#guard admissions.all fun x => Canonical.decode (α := AdmitRefusal) (Canonical.encode x).dropLast = none
-- Every refusal fits its generated shape.
#guard typings.all fun x => (Canonical.shape TypeRefusal).accepts (Canonical.toVal x)
#guard authors.all fun x => (Canonical.shape AuthorRefusal).accepts (Canonical.toVal x)
#guard prints.all fun x => (Canonical.shape PrintRefusal).accepts (Canonical.toVal x)
#guard reads.all fun x => (Canonical.shape ReadRefusal).accepts (Canonical.toVal x)
#guard admissions.all fun x => (Canonical.shape AdmitRefusal).accepts (Canonical.toVal x)
-- Refusals are distinct as bytes exactly when they are distinct values.
#guard (authors.map Canonical.encode).eraseDups.length = authors.length
#guard (reads.map Canonical.encode).eraseDups.length = reads.length
-- An authoring refusal and a read refusal are different content: neither reads as the other.
#guard authors.all fun x => Canonical.decode (α := ReadRefusal) (Canonical.encode x) = none

end RefusalsAcceptance
