import Tools.Session
import Effect4.Program.Authoring.Lifts

/-!
# Probe: two wire abstractions for fluent authoring, on the tree's own code

Probe for `docs/research/2026-10-13-fluent-authoring/README.md`. A finite probe: every check is a
`#guard` on named programs, no theorem.

* **A. The named source.** A program with names is data: the free object of the binding
  signature that the authoring lifts already form an algebra of (`Program/Authoring.lean`,
  `binders.json`). Reading it is one fold into the lifts, so its refusals are theirs.
* **B. One JSON encoding.** A located twin of `readIn` (`Store/Domain/ShapeRead.lean`), and the
  carrier rule of `ts/eff/eff.gen.ts`: a sum whose cases are exactly `nil` and `cons head tail`
  is a JSON array. The shape, so the canonical bytes, does not change.
-/

set_option autoImplicit false

open Effect4 Effect4.Program Effect4.Store

namespace FluentProbe

/-! ## A. The named source -/

/-- A term with names (a fragment: variables, two literals, atoms). -/
inductive NTerm where
  | var (name : String)
  | nat (n : Nat)
  | str (s : String)
  | app (atom : String) (args : List NTerm)

/-- A program with names (a fragment: succeed, perform, a host row by spelling, bind). -/
inductive NEff where
  | succeed (value : NTerm)
  | perform (op : NativeOp) (request : NTerm)
  | call (row : String) (request : NTerm)
  | bind (answer : String) (first rest : NEff)

mutual
/-- The fold into the term lifts. -/
def NTerm.read : NTerm → Authoring.TermSrc
  | .var x => Authoring.var x
  | .nat n => Authoring.nat n
  | .str s => Authoring.str s
  | .app a args => Authoring.app a (NTerm.readAll args)
def NTerm.readAll : List NTerm → List Authoring.TermSrc
  | [] => []
  | t :: ts => NTerm.read t :: NTerm.readAll ts
end

/-- A host row by its spelling: `Authoring.Row.call`'s body, which reads only the spelling. -/
def callBySpelling (spelling : String) (request : Authoring.TermSrc) :
    Authoring.Src NativeOp := fun env p =>
  match env.rows.find? (fun entry => entry.1 == spelling) with
  | some (_, i) => do
    let x ← request env p
    .ok (.perform (.external i) x)
  | none => .error ⟨p, .unboundRow spelling⟩

/-- **The fold into the program lifts**: one line per constructor. -/
def NEff.read : NEff → Authoring.Src NativeOp
  | .succeed t => Authoring.succeed t.read
  | .perform op t => Authoring.perform op t.read
  | .call r t => callBySpelling r t.read
  | .bind x p q => Authoring.bind x p.read q.read

def okIs (r : Except Authoring.Refusal NativeEff) (e : NativeEff) : Bool :=
  match r with
  | .ok e' => decide (e' = e)
  | .error _ => false

def refusedAt (r : Except Authoring.Refusal NativeEff) (p : List Nat)
    (why : Authoring.Reason) : Bool :=
  match r with
  | .error ⟨p', why'⟩ => decide (p' = p) && decide (why' = why)
  | .ok _ => false

open NTerm in
/-- The probe's to-do program, with names. -/
def todoNamed (a b c : String) : NEff :=
  .bind a (.succeed (app "cons" [str "buy milk", app "nil" []]))
    (.bind b (.perform .refMake (var a))
      (.bind c (.perform .refGet (var b))
        (.succeed (app "length" [var c]))))

/-- The same program as stored: variables are levels. -/
def todoEff : NativeEff :=
  .bind (.succeed (.app "cons" (.cons (.lit (.str "buy milk")) (.cons (.app "nil" .nil) .nil))))
    (.bind (.perform .refMake (.var 0))
      (.bind (.perform .refGet (.var 1))
        (.succeed (.app "length" (.cons (.var 2) .nil)))))

-- Names read to levels, by the lifts.
#guard okIs ((todoNamed "todos" "ref" "now").read {} []) todoEff
-- Renaming every name consistently gives the same stored program.
#guard okIs ((todoNamed "a" "b" "c").read {} []) todoEff
-- The nearest binder wins.
#guard okIs ((NEff.bind "x" (.succeed (.nat 1)) (.bind "x" (.succeed (.nat 2))
    (.succeed (.var "x")))).read {} [])
  (.bind (.succeed (.lit (.nat 1))) (.bind (.succeed (.lit (.nat 2))) (.succeed (.var 1))))
-- An unbound name is refused by name, at its path.
#guard refusedAt ((NEff.bind "todos" (.succeed (.nat 1)) (.succeed (.app "length" [.var "nwo"]))).read {} [])
  [1] (.unbound "nwo")
-- A host row by spelling reads to its position in the application's table ...
#guard okIs ((NEff.bind "id" (.call "insert" (.str "buy milk")) (.succeed (.var "id"))).read
    { rows := [("list", 0), ("insert", 1)] } [])
  (.bind (.perform (.external 1) (.lit (.str "buy milk"))) (.succeed (.var 0)))
-- ... and is refused by spelling outside it.
#guard refusedAt ((NEff.bind "id" (.call "insert" (.str "x")) (.succeed (.var "id"))).read {} [])
  [0] (.unboundRow "insert")

/-! ### Back to names: generated names, one per level -/

def nameAt (level : Nat) : String := s!"v{level}"

mutual
def unTerm : Term → Option NTerm
  | .var i => some (.var (nameAt i))
  | .lit (.nat n) => some (.nat n)
  | .lit (.str s) => some (.str s)
  | .app a args => (unTerms args).map (.app a)
  | _ => none
def unTerms : Terms → Option (List NTerm)
  | .nil => some []
  | .cons t ts => (unTerm t).bind fun x => (unTerms ts).map (x :: ·)
end

/-- A stored program with generated names; a host row by the spelling the table gives it. -/
def unEff (rows : List String) : Nat → NativeEff → Option NEff
  | _, .succeed t => (unTerm t).map .succeed
  | _, .perform (.external i) t => (rows[i]?).bind fun r => (unTerm t).map (.call r)
  | _, .perform op t => (unTerm t).map (.perform op)
  | d, .bind p q => (unEff rows d p).bind fun a => (unEff rows (d + 1) q).map (.bind (nameAt d) a)
  | _, _ => none

def roundTrips (rows : List String) (e : NativeEff) : Bool :=
  match unEff rows 0 e with
  | some n => okIs (n.read { rows := rows.zipIdx } []) e
  | none => false

-- Reading the generated names gives the stored program back.
#guard roundTrips [] todoEff
#guard roundTrips ["list", "insert"]
  (.bind (.perform (.external 1) (.lit (.str "a"))) (.bind (.perform (.external 0) (.var 0))
    (.succeed (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))))))

/-! ## B. One JSON encoding, read with its location -/

/-- Where a read stopped: the JSON path, and what the shape wanted there. -/
structure Miss where
  path : List String
  wanted : String

def caseNames (cases : List (String × Nat × List (String × Shape))) : String :=
  ", ".intercalate (cases.map (·.1))

/-- What a shape wants, in words. -/
def wantedOf (defs : List (String × Shape)) (s : Shape) : String :=
  match headShape defs s with
  | .unit => "null"
  | .bool => "a boolean"
  | .nat => "a natural number"
  | .string => "a string"
  | .bytes | .digest => "lowercase hex"
  | .list _ => "an array"
  | .option _ => "a value or null"
  | .pair _ _ => "an array of two"
  | .struct n _ => s!"an object {n}"
  | .sum n cases =>
    if allNullary cases then s!"{n}: one of {caseNames cases}"
    else s!"{n}: an object whose _tag is one of {caseNames cases}"
  | .ref _ => "a reference"
  | .anyRef => "a reference and its kind"
  | .named n => n

/-- The carrier rule of `ts/eff/eff.gen.ts`: a sum whose cases are exactly `nil` and
`cons head tail`, with its two tags and its item's shape. -/
def listFamily? : List (String × Nat × List (String × Shape)) → Option (Nat × Nat × Shape)
  | [("nil", t0, []), ("cons", t1, [("head", h), ("tail", _)])] => some (t0, t1, h)
  | _ => none

mutual
/-- `readIn` with a location: a refusal names the JSON path and what the shape wanted. Objects
are read by field name, so their order is free. With `arrays`, a list family reads an array. -/
def readAt (defs : List (String × Shape)) (arrays : Bool) :
    Nat → List String → Shape → Json → Except Miss Val
  | 0, p, _, _ => .error ⟨p, "within the budget"⟩
  | n + 1, p, s, j =>
    let miss : Except Miss Val := .error ⟨p, wantedOf defs s⟩
    match headShape defs s, j with
    | .unit, .null => .ok .unit
    | .option _, .null => .ok .none
    | .option item, j' => (readAt defs arrays n p item j').map .some
    | .bool, .bool b => .ok (.bool b)
    | .nat, .number x =>
      match natOfBinary64 x.bits with
      | some k => .ok (.nat k)
      | none => miss
    | .string, .str t => .ok (.str t)
    | .list item, .arr js => (readAtList defs arrays n p item 0 js).map .list
    | .pair f g, .arr [a, b] => do
      let x ← readAt defs arrays n (p ++ ["0"]) f a
      let y ← readAt defs arrays n (p ++ ["1"]) g b
      .ok (.pair x y)
    | .struct _ fields, .obj entries =>
      (readAtFields defs arrays n p fields entries).map (.ctor 0)
    | .sum _ cases, .arr js =>
      match arrays, listFamily? cases with
      | true, some (t0, t1, h) => readAtSpine defs arrays n p t0 t1 h 0 js
      | _, _ => miss
    | .sum _ cases, .str name =>
      if allNullary cases then
        match tagOfName name cases with
        | some (tag, []) => .ok (.ctor tag [])
        | _ => .error ⟨p, s!"{wantedOf defs s}; found {name}"⟩
      else miss
    | .sum _ cases, .obj entries =>
      if allNullary cases then miss
      else
        match entryOf "_tag" entries with
        | some (.str name) =>
          match tagOfName name cases with
          | some (tag, fields) =>
            (readAtFields defs arrays n p fields (entries.filter (·.1 != "_tag"))).map (.ctor tag)
          | none => .error ⟨p ++ ["_tag"], s!"{wantedOf defs s}; found {name}"⟩
        | _ => .error ⟨p ++ ["_tag"], wantedOf defs s⟩
    | _, _ => miss
def readAtList (defs : List (String × Shape)) (arrays : Bool) :
    Nat → List String → Shape → Nat → List Json → Except Miss (List Val)
  | 0, p, _, _, _ => .error ⟨p, "within the budget"⟩
  | _ + 1, _, _, _, [] => .ok []
  | n + 1, p, item, i, j :: js => do
    let x ← readAt defs arrays n (p ++ [toString i]) item j
    let xs ← readAtList defs arrays n p item (i + 1) js
    .ok (x :: xs)
def readAtSpine (defs : List (String × Shape)) (arrays : Bool) :
    Nat → List String → Nat → Nat → Shape → Nat → List Json → Except Miss Val
  | 0, p, _, _, _, _, _ => .error ⟨p, "within the budget"⟩
  | _ + 1, _, t0, _, _, _, [] => .ok (.ctor t0 [])
  | n + 1, p, t0, t1, h, i, j :: js => do
    let x ← readAt defs arrays n (p ++ [toString i]) h j
    let rest ← readAtSpine defs arrays n p t0 t1 h (i + 1) js
    .ok (.ctor t1 [x, rest])
def readAtFields (defs : List (String × Shape)) (arrays : Bool) :
    Nat → List String → List (String × Shape) → List (String × Json) → Except Miss (List Val)
  | 0, p, _, _ => .error ⟨p, "within the budget"⟩
  | _ + 1, p, [], entries =>
    match entries with
    | [] => .ok []
    | (k, _) :: _ => .error ⟨p ++ [k], "no field of this name"⟩
  | n + 1, p, (k, s) :: fields, entries =>
    match entryOf k entries with
    | none => .error ⟨p ++ [k], s!"the field {k}: {wantedOf defs s}"⟩
    | some j => do
      let x ← readAt defs arrays n (p ++ [k]) s j
      let xs ← readAtFields defs arrays n p fields (entries.filter (·.1 != k))
      .ok (x :: xs)
end

mutual
/-- `printIn` with the carrier rule: with `arrays`, a list family prints as an array. -/
def printAt (defs : List (String × Shape)) (arrays : Bool) : Nat → Shape → Val → Json
  | 0, s, v => printIn defs s v
  | n + 1, s, v =>
    match headShape defs s, v with
    | .sum _ cases, .ctor tag args =>
      match arrays, listFamily? cases with
      | true, some (_, _, h) => .arr (spineAt defs arrays n h v)
      | _, _ =>
        match caseAt tag cases with
        | some (name, fields) =>
          if allNullary cases then .str name
          else .obj (("_tag", .str name) :: fieldsAt defs arrays n fields args)
        | none => printIn defs s v
    | .struct _ fields, .ctor _ args => .obj (fieldsAt defs arrays n fields args)
    | .option item, .some a => printAt defs arrays n item a
    | .list item, .list xs => .arr (listAt defs arrays n item xs)
    | .pair f g, .pair a b => .arr [printAt defs arrays n f a, printAt defs arrays n g b]
    | _, _ => printIn defs s v
def spineAt (defs : List (String × Shape)) (arrays : Bool) : Nat → Shape → Val → List Json
  | 0, _, _ => []
  | n + 1, h, .ctor _ [x, rest] => printAt defs arrays n h x :: spineAt defs arrays n h rest
  | _, _, _ => []
def fieldsAt (defs : List (String × Shape)) (arrays : Bool) :
    Nat → List (String × Shape) → List Val → List (String × Json)
  | n + 1, (k, s) :: fs, a :: as => (k, printAt defs arrays n s a) :: fieldsAt defs arrays n fs as
  | _, _, _ => []
def listAt (defs : List (String × Shape)) (arrays : Bool) : Nat → Shape → List Val → List Json
  | n + 1, item, x :: xs => printAt defs arrays n item x :: listAt defs arrays n item xs
  | _, _, _ => []
end

/-- A program from JSON text: parsed, then read under `NativeEff`'s shape. -/
def readProgram (arrays : Bool) (src : String) : Except Miss NativeEff := do
  let lj ← match Lean.Json.parse src with
    | .ok j => .ok j
    | .error e => .error ⟨[], s!"JSON text: {e}"⟩
  let j ← match Tools.JsonBridge.ofLeanJson 4096 lj with
    | some j => .ok j
    | none => .error ⟨[], "JSON numbers within binary64 naturals"⟩
  let doc := Canonical.shape NativeEff
  let v ← readAt doc.defs arrays (readBudget j) [] doc.root j
  match Canonical.ofVal v with
  | some e => .ok e
  | none => .error ⟨[], "a value of the carrier"⟩

def printProgram (arrays : Bool) (e : NativeEff) : String :=
  let doc := Canonical.shape NativeEff
  (Tools.JsonBridge.toLeanJson (printAt doc.defs arrays 100000 doc.root (Canonical.toVal e))).compress

def readsAs (r : Except Miss NativeEff) (e : NativeEff) : Bool :=
  match r with
  | .ok e' => decide (e' = e)
  | .error _ => false

def missAt (r : Except Miss NativeEff) (p : List String) : Option String :=
  match r with
  | .error m => if m.path = p then some m.wanted else some s!"elsewhere: {m.path}: {m.wanted}"
  | .ok _ => none

/-- The canonical print, as the session tool prints it. -/
def canonical (e : NativeEff) : String := (Tools.JsonBridge.printJson e).compress

-- Without the rule, the located reader reads the canonical print, as the session tool does.
#guard readsAs (readProgram false (canonical todoEff)) todoEff
#guard (Tools.Session.programOfJson (Tools.JsonBridge.printJson todoEff)).isSome
-- Without the rule, the printer is the canonical printer.
#guard printProgram false todoEff == canonical todoEff
-- With the rule, a list family prints as an array, and reads back.
#guard readsAs (readProgram true (printProgram true todoEff)) todoEff
-- The print with the rule is the encoding of `ts/eff/eff.gen.ts` (P1 as the agent wrote it).
def tsEncoded : String :=
  "{\"_tag\":\"bind\",\"first\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"app\",\"atom\":\"cons\",\"args\":[{\"_tag\":\"lit\",\"value\":{\"_tag\":\"str\",\"value\":\"buy milk\"}},{\"_tag\":\"app\",\"atom\":\"nil\",\"args\":[]}]}},\"rest\":{\"_tag\":\"bind\",\"first\":{\"_tag\":\"perform\",\"op\":{\"_tag\":\"refMake\"},\"request\":{\"_tag\":\"var\",\"index\":0}},\"rest\":{\"_tag\":\"bind\",\"first\":{\"_tag\":\"perform\",\"op\":{\"_tag\":\"refGet\"},\"request\":{\"_tag\":\"var\",\"index\":1}},\"rest\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"app\",\"atom\":\"length\",\"args\":[{\"_tag\":\"var\",\"index\":2}]}}}}}"
#guard readsAs (readProgram true tsEncoded) todoEff
#guard (Lean.Json.parse tsEncoded).toOption == (Lean.Json.parse (printProgram true todoEff)).toOption
-- Without the rule, the same text is refused where the first array stands.
#eval missAt (readProgram false tsEncoded) ["first", "value", "args"]
-- A missing field is refused at its name.
#eval missAt (readProgram true "{\"_tag\":\"bind\",\"first\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":1}}}}") ["rest"]
-- A guessed tag is refused at the tag, with the cases there are.
#eval missAt (readProgram true "{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"string\",\"value\":\"x\"}}}") ["value", "value", "_tag"]

end FluentProbe
