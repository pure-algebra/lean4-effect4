import Effect4.Laws.Codegen.Record

/-!
Structural wrapper controls. The universal laws are about target expressions, not rendered
source or JavaScript execution. Each refusal control has an available normal-image control.
-/

namespace Effect4.Test.Record
open Effect4.Program Effect4.Codegen Effect4.Codegen.Record TypeScript

def fields : Fields := [("nickname", true, .string), ("id", false, .nat)]
def names : List String := ["id"]
def values : List Expr := [.int 7]

-- The coordinator's type projection must make the normal controls non-vacuous.
#guard (Types.ofTy (.record fields)).isSome
#guard readRecord (writeRecord fields names values) == some (fields, names, values)

-- Every raw list remains recoverable, even when no checked program could use it.
#guard readRecord (writeRecord fields ["id", "extra"] [.int 7]) ==
  some (fields, ["id", "extra"], [.int 7])
#guard readRecord (writeRecord fields ["id"] [.int 7, .str "extra"]) ==
  some (fields, ["id"], [.int 7, .str "extra"])
#guard readRecord (writeRecord [("x", false, .var 99)] ["x"] [.ident "value"]) ==
  some ([("x", false, .var 99)], ["x"], [.ident "value"])
#guard readRecord (writeRecord [("z", true, .nat), ("z", false, .string)]
    ["z", "z"] [.int 1, .str "last"]) ==
  some ([("z", true, .nat), ("z", false, .string)], ["z", "z"], [.int 1, .str "last"])

-- All properties of a literal use its one canonical key form.
#guard keyForm ["id", "nickname"] = .plain
#guard keyForm ["id", "a-b"] = .quoted
#guard keyForm ["id", "a-b", "__proto__"] = .computed
#guard keyForm [""] = .quoted

def normalWith (annotation : TypeRef) (form : KeyForm) (entries : List ObjectEntry) : Expr :=
  .call (.generic (.ident "recordValue") [annotation])
    [Metadata.writeTy (.record fields), .objectWith form entries]

-- The annotation, object constructor, key mode and property-only shape are checked.
#guard (match Types.ofTy (.record fields) with
  | none => false
  | some annotation =>
    (readRecord (normalWith annotation .plain (properties names values))).isSome &&
    (readRecord (normalWith annotation .quoted (properties names values))).isNone &&
    (readRecord (normalWith annotation .computed (properties names values))).isNone &&
    (readRecord (normalWith annotation .plain [.spread (.ident "p")])).isNone &&
    (readRecord (normalWith annotation .plain [.property "id" (.int 7),
      .spread (.ident "p")])).isNone &&
    (readRecord (.call (.generic (.ident "recordValue") [annotation])
      [Metadata.writeTy (.record fields), .object [("id", .int 7)]])).isNone)
#guard (readRecord (normalWith (.name ["unknown"] []) .plain (properties names values))).isNone
#guard (match Types.ofTy (.record fields) with
  | some (.object fs) =>
    (readRecord (normalWith (.object (fs.map fun f => { f with optional := !f.optional }))
      .plain (properties names values))).isNone
  | _ => false)

-- The raw spelling is refused when this input has a normal spelling.
#guard (readRecord (.call (.generic (.ident "recordRaw") [.name ["unknown"] []])
  [Metadata.writeTy (.record fields), .arr [.str "id"], .arr [.int 7]])).isNone
#guard (readRecord (.call (.generic (.ident "recordRaw") [.name ["unknown"] []])
  [Metadata.writeTy (.record fields), .arr [.int 1], .arr []])).isNone
#guard (readRecord (.call (.generic (.ident "recordRaw") [.name ["unknown"] []])
  [Metadata.writeTy .nat, .arr [], .arr []])).isNone

-- Required and optional access remain distinct on exactly the same child expression.
#guard readField (writeField false "nickname" (.ident "p")) ==
  some (false, "nickname", .ident "p")
#guard readField (writeField true "nickname" (.ident "p")) ==
  some (true, "nickname", .ident "p")
#guard readField (writeField false "a-b" (.ident "p")) == some (false, "a-b", .ident "p")
#guard readField (writeField true "__proto__" (.ident "p")) == some (true, "__proto__", .ident "p")
#guard (readField (.index (.ident "p") (.str "nickname"))).isNone
#guard (readField (.member (.ident "p") "a-b")).isNone
#guard (readField (.call (.call (.generic (.ident "recordOptional") [.literal "nickname"])
  [.str "other"]) [.ident "p"])).isNone

-- Updates have exactly one spread followed by one property, with an independent generic marker.
#guard readSet (writeSet "nickname" (.ident "p") (.str "Ada")) ==
  some ("nickname", .ident "p", .str "Ada")
#guard readSet (writeSet "a-b" (.ident "p") (.int 4)) ==
  some ("a-b", .ident "p", .int 4)
#guard readSet (writeSet "__proto__" (.ident "p") (.ident "undefined")) ==
  some ("__proto__", .ident "p", .ident "undefined")

def updateWith (key : String) (form : KeyForm) (entries : List ObjectEntry) : Expr :=
  .call (.call (.generic (.ident "recordSet") [.literal key]) []) [.objectWith form entries]

#guard (readSet (updateWith "x" .plain [.spread (.ident "p"), .property "x" (.int 1)])).isSome
#guard (readSet (updateWith "other" .plain [.spread (.ident "p"), .property "x" (.int 1)])).isNone
#guard (readSet (updateWith "x" .quoted [.spread (.ident "p"), .property "x" (.int 1)])).isNone
#guard (readSet (updateWith "__proto__" .plain
  [.spread (.ident "p"), .property "__proto__" (.int 1)])).isNone
#guard (readSet (updateWith "x" .plain [.property "x" (.int 1), .spread (.ident "p")])).isNone
#guard (readSet (updateWith "x" .plain
  [.spread (.ident "p"), .property "x" (.int 1), .spread (.ident "q")])).isNone
#guard (readSet (updateWith "x" .plain
  [.spread (.ident "p"), .property "x" (.int 1), .property "y" (.int 2)])).isNone
#guard (readSet (.call (.ident "recordSet") [.ident "p"])).isNone

example (fs : Fields) (ns : List String) (vs : List Expr) :
    readRecord (writeRecord fs ns vs) = some (fs, ns, vs) := readRecord_writeRecord fs ns vs
example (e : Expr) (fs : Fields) (ns : List String) (vs : List Expr)
    (h : readRecord e = some (fs, ns, vs)) : writeRecord fs ns vs = e :=
  readRecord_exact e fs ns vs h

end Effect4.Test.Record

#print axioms TypeScript.TypeRef.beq
#print axioms TypeScript.TypeRef.beq_iff
#print axioms TypeScript.TypeRef.beq_self
#print axioms Effect4.Codegen.Record.writeRecord
#print axioms Effect4.Codegen.Record.readRecord
#print axioms Effect4.Codegen.Record.readRecord_size
#print axioms Effect4.Codegen.Record.readField_size
#print axioms Effect4.Codegen.Record.readRecord_writeRecord
#print axioms Effect4.Codegen.Record.readRecord_exact
#print axioms Effect4.Codegen.Record.readField_writeField
#print axioms Effect4.Codegen.Record.readField_exact
#print axioms Effect4.Codegen.Record.readSet_size
#print axioms Effect4.Codegen.Record.readSet_writeSet
#print axioms Effect4.Codegen.Record.readSet_exact
