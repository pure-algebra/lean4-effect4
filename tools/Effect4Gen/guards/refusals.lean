/-! Refusal acceptance (decisions row 17): every refusal an agent can be shown, written as content,
read back exactly, refused with a byte added or removed, and fitting its generated shape; two
refusals are distinct as bytes exactly when they are distinct values. -/
namespace RefusalsAcceptance
open Effect4 Effect4.Program Effect4.Api

def tables : List TableRefusal := [.notExternal 0, .notAsync 3]

def formationReasons : List FormationReason := [.repeatedField "x", .mapKey, .typeVariable]

def formations : List FormationRefusal :=
  [⟨["table", "0", "answer", "type", "0"], .map .nat .string, .mapKey⟩,
   ⟨["program", "cursorTy", "type", "0"],
     .record [("x", false, .nat), ("x", true, .string)], .repeatedField "x"⟩]

def recordReasons : List RecordTypingReason :=
  [.duplicateDeclaration "x", .duplicateSupplied "x", .missingRequired "x",
   .unknownSupplied "x", .fieldNotSubtype "x" .string .nat, .columnLengths 1 2,
   .missingReadField "x" (.record []), .optionalReadField "x" (.record [("x", true, .nat)]),
   .declarationFormation ⟨["type"], .map .nat .string, .mapKey⟩]

def recordTerms : List RecordTermRefusal := recordReasons.map fun why => ⟨[0, 2], why⟩

def recordCauses : List RecordCauseRefusal := recordTerms.map fun why => ⟨[1, 0], why⟩

/-- Every constructor of a row's reason (decisions row 21: the signature's refusal reaches an
agent through admission's). -/
def rowReasons : List RowReason :=
  [.notExternal, .notAsync, .builtinCollision, .valueRowTrailing,
   .internalHandle "answer", .emptyColumn "error", .templateNotAdmissible "request",
   .notWellScoped]

def serviceReasons : List ServiceReason := [.reservedName, .nonFlatCarrier, .conflictsBuiltin]

def signatures : List SigRefusal :=
  rowReasons.map (SigRefusal.row 0) ++ [.duplicateRow ("Db", [.name "get"])] ++
    serviceReasons.map (SigRefusal.service 1) ++ [.duplicateCode ⟨7⟩, .unservedKey 2 ⟨⟨30⟩, ⟨30⟩⟩]

def admissions : List AdmitRefusal :=
  [.illTyped] ++ signatures.map .signature ++
    [.emptyColumn ["program", "answer"], .emptyColumn ["program", "error"]] ++
    formations.map .formation

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
   ⟨[], .returnNotLast⟩, ⟨[], .breakOutsideLoop⟩, ⟨[], .literalOutsideAlphabet (.str "x")⟩,
   ⟨[], .errorPayloadField (.record [("_tag", false, .lit "E"), ("id", false, .int)]) ["id"] .int⟩,
   ⟨[], .errorSpelling (.record [("_tag", false, .lit "E"), ("message", false, .string)])
     (.prod (.lit "E") .string)⟩] ++
    formations.map (fun why => ⟨[0], .instantiatedFormation "Db.get" why⟩) ++
    recordTerms.map (fun why => ⟨[1], .recordTerm why⟩) ++
    recordCauses.map (fun why => ⟨[2], .recordCause why⟩)

def authors : List AuthorRefusal := scopes.map .scope ++ typings.map .typing

def prints : List PrintRefusal :=
  [.internalAction "fork", .layerRef [0, 2], .unsafeName "a0", .typeSpelling "Date",
   .payloadClass "not-a-tag" .notIdentifier, .payloadClass "Effect" .collides,
   .payloadClass "NotFound" .fieldsDiffer, .payloadClass "NotFound" .construction,
   .payloadClass "Rate" .unreadable, .binderTerm "Ref.modify"]

def reads : List ReadRefusal :=
  [.unknownHead "Cause.fail", .unknownIdent "x", .arity "Db.get", .binder "a1", .shape "call",
   .negative (-3), .unsupportedStmt, .annotation "lambda parameter"]

/-- The two ways a module's build is refused that no authored source meets: admission's, and a
service declared at another carrier than its signature's. -/
def buildsOnly : List BuildRefusal :=
  admissions.map .admission ++
    [.serviceCarrier ⟨⟨3⟩, ⟨7⟩⟩ .nat (some .string), .serviceCarrier ⟨⟨4⟩, ⟨1⟩⟩ .unit none]

/-- Every way a module's build is refused (`Api.build`), the eighth of the row's refusals: the
scope reader's, the checker's, and the two of `buildsOnly`. -/
def builds : List BuildRefusal := scopes.map .scope ++ typings.map .typing ++ buildsOnly

/-- Every constructor of the checker's reason, in declaration order. -/
def reasons : List TypeReason :=
  [.term (.var 3), .cause (.fail (.lit (.nat 1))), .errorNotAdmitted .nat, .outsideDomain "Db.get",
   .requestNotSubtype "Db.get" .string .nat, .predicateNotBool .nat,
   .notSelectable (.tag "Some") (.option .nat), .stepNotCursor .string .nat,
   .initialNotCursor .bool .nat, .releaseFails .string, .notFiber .unit, .scopeExpected .nat,
   .natExpected .string, .listOfFibersExpected .nat, .contextExpected .unit,
   .snapshotExpected .bool, .exitExpected .string, .serviceUnknown ⟨⟨3⟩, ⟨7⟩⟩,
   .valueNotSubtype ⟨⟨3⟩, ⟨7⟩⟩ .string .nat, .layerReference [0, 1], .referencesIllFormed,
   .mergeAllEmpty, .returnNotLast, .breakOutsideLoop, .literalOutsideAlphabet (.str "x"),
   .instantiatedFormation "Db.get" ⟨["row", "answer", "type", "0"], .map .nat .string, .mapKey⟩,
   .recordTerm ⟨[0], .missingRequired "x"⟩,
   .recordCause ⟨[1], ⟨[0], .missingRequired "x"⟩⟩,
   .tupleTerm ⟨[0], 2, .outOfBounds 2⟩,
   .tupleCause ⟨[1], ⟨[0], 0, .nonTuple .nat⟩⟩,
   .errorPayloadField (.record [("_tag", false, .lit "E"), ("cause", false, .unknown)])
     ["cause"] .unknown,
   .errorSpelling (.record [("_tag", false, .lit "E")]) (.lit "E"),
   .binderTerm "Ref.update" .string, .resultNotSubtype "Ref.modify" (.list .string) (.list .never),
   .foldTerm ⟨[0], .notList .nat⟩,
   .foldCause ⟨[1], ⟨[0], .bodyNotAccumulator (.list .nat) (.list .never)⟩⟩,
   .maskRestoreExpected .bool, .definitionBlock, .definitionsMismatch 1 0,
   .definitionColumns "count", .bodyNotDeclared "count" (EffTy.pure .string)]

/-- The name `ShapeDoc.print` writes for a sum's value: its `_tag` field, or the string an
all-nullary sum prints as; the empty string for anything else. -/
def printedHead : Effect4.Json → String
  | .str s => s
  | .obj entries => match entries.lookup "_tag" with
    | some (.str s) => s
    | _ => ""
  | _ => ""

#guard recordReasons.all fun x => Canonical.decode (α := RecordTypingReason) (Canonical.encode x) = some x
#guard recordReasons.all fun x => Canonical.decode (α := RecordTypingReason) (Canonical.encode x ++ [0]) = none
#guard recordReasons.all fun x => Canonical.decode (α := RecordTypingReason) (Canonical.encode x).dropLast = none
#guard recordReasons.all fun x => (Canonical.shape RecordTypingReason).accepts (Canonical.toVal x)
#guard recordTerms.all fun x => Canonical.decode (α := RecordTermRefusal) (Canonical.encode x) = some x
#guard recordTerms.all fun x => Canonical.decode (α := RecordTermRefusal) (Canonical.encode x ++ [0]) = none
#guard recordTerms.all fun x => Canonical.decode (α := RecordTermRefusal) (Canonical.encode x).dropLast = none
#guard recordTerms.all fun x => (Canonical.shape RecordTermRefusal).accepts (Canonical.toVal x)
#guard recordCauses.all fun x => Canonical.decode (α := RecordCauseRefusal) (Canonical.encode x) = some x
#guard recordCauses.all fun x => Canonical.decode (α := RecordCauseRefusal) (Canonical.encode x ++ [0]) = none
#guard recordCauses.all fun x => Canonical.decode (α := RecordCauseRefusal) (Canonical.encode x).dropLast = none
#guard recordCauses.all fun x => (Canonical.shape RecordCauseRefusal).accepts (Canonical.toVal x)

#guard formationReasons.all fun x => Canonical.decode (α := FormationReason) (Canonical.encode x) = some x
#guard formations.all fun x => Canonical.decode (α := FormationRefusal) (Canonical.encode x) = some x
#guard formations.all fun x => Canonical.decode (α := FormationRefusal) (Canonical.encode x ++ [0]) = none
#guard formations.all fun x => Canonical.decode (α := FormationRefusal) (Canonical.encode x).dropLast = none
#guard formations.all fun x => (Canonical.shape FormationRefusal).accepts (Canonical.toVal x)
#guard formationReasons.all fun x => (Canonical.shape FormationReason).accepts (Canonical.toVal x)
#guard tables.all fun x => Canonical.decode (α := TableRefusal) (Canonical.encode x) = some x
#guard rowReasons.all fun x => Canonical.decode (α := RowReason) (Canonical.encode x) = some x
#guard serviceReasons.all fun x => Canonical.decode (α := ServiceReason) (Canonical.encode x) = some x
#guard signatures.all fun x => Canonical.decode (α := SigRefusal) (Canonical.encode x) = some x
#guard signatures.all fun x => Canonical.decode (α := SigRefusal) (Canonical.encode x ++ [0]) = none
#guard signatures.all fun x => Canonical.decode (α := SigRefusal) (Canonical.encode x).dropLast = none
#guard signatures.all fun x => (Canonical.shape SigRefusal).accepts (Canonical.toVal x)
#guard (signatures.map Canonical.encode).eraseDups.length = signatures.length
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
-- The build refusal (seat J2): read back exactly, refused with a byte added or removed, fitting
-- its shape, and distinct as bytes exactly when distinct.
#guard builds.all fun x => Canonical.decode (α := BuildRefusal) (Canonical.encode x) = some x
#guard builds.all fun x => Canonical.decode (α := BuildRefusal) (Canonical.encode x ++ [0]) = none
#guard builds.all fun x => Canonical.decode (α := BuildRefusal) (Canonical.encode x).dropLast = none
#guard builds.all fun x => (Canonical.shape BuildRefusal).accepts (Canonical.toVal x)
#guard (builds.map Canonical.encode).eraseDups.length = builds.length
-- A build refused at a name or a type is the author refusal of the same case, byte for byte: the
-- bytes hold a case's position and its content, never the type's name (the shape document names
-- the type; a node's address adds the version, kind and spec). The cases only a build meets are
-- no author refusal.
#guard scopes.all fun r => Canonical.encode (BuildRefusal.scope r) = Canonical.encode (AuthorRefusal.scope r)
#guard typings.all fun r => Canonical.encode (BuildRefusal.typing r) = Canonical.encode (AuthorRefusal.typing r)
#guard buildsOnly.all fun x => Canonical.decode (α := AuthorRefusal) (Canonical.encode x) = none
-- `Canonical.head` (decisions row 17): the constructor's name read off the shape agrees with the
-- hand-written `TypeReason.head` on every constructor (the list is every case, in order) ...
#guard reasons.map TypeReason.head == Canonical.heads TypeReason
#guard reasons.all fun x => Canonical.head x == x.head
-- ... and with the name `ShapeDoc.print` writes, for every value of the group's sums.
#guard tables.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard rowReasons.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard serviceReasons.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard signatures.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard admissions.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard (scopes.map (·.reason)).all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard reasons.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard authors.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard prints.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard reads.all fun x => Canonical.head x == printedHead (Canonical.print x)
#guard builds.all fun x => Canonical.head x == printedHead (Canonical.print x)
-- A structure's head is its name, which its printed object does not carry.
#guard typings.all fun x => Canonical.head x == "TypeRefusal" && printedHead (Canonical.print x) == ""

end RefusalsAcceptance

namespace TupleRefusalAcceptance
open Effect4 Effect4.Program Effect4.Store

def controls : List TypeReason :=
  [.tupleTerm ⟨[1, 0], 2, .outOfBounds 2⟩,
   .tupleTerm ⟨[], 0, .nonTuple (.list .nat)⟩,
   .tupleCause ⟨[1], ⟨[0], 900719925474099312345678901, .outOfBounds 1⟩⟩]

#guard controls.all fun reason =>
  Canonical.decode (α := TypeReason) (Canonical.encode reason) = some reason
#guard controls.all fun reason =>
  Canonical.decode (α := TypeReason) (Canonical.encode reason ++ [0]) = none

end TupleRefusalAcceptance

namespace FoldRefusalAcceptance
open Effect4 Effect4.Program Effect4.Store

/-- The three reasons a list fold has no type (decisions row 228), in a term and in a cause. -/
def controls : List TypeReason :=
  [.foldTerm ⟨[1, 0], .notList .nat⟩,
   .foldTerm ⟨[], .initialNotAccumulator (.list .nat) (.list .never)⟩,
   .foldTerm ⟨[2], .bodyNotAccumulator .string .nat⟩,
   .foldCause ⟨[1], ⟨[0], .notList (.option .nat)⟩⟩]

#guard controls.all fun reason =>
  Canonical.decode (α := TypeReason) (Canonical.encode reason) = some reason
#guard controls.all fun reason =>
  Canonical.decode (α := TypeReason) (Canonical.encode reason ++ [0]) = none
#guard controls.all fun reason => Canonical.head reason == RefusalsAcceptance.printedHead (Canonical.print reason)

end FoldRefusalAcceptance
