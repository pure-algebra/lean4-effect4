import Conform.Layout.Layout
import Conform.Core.Report
import Conform.Core.Obligation
import Conform.Core.Policy

/-!
# Conform.Layout.Check — the three checks over a layout datum, as `Conform.Report` rows

**What it is.** `layout.covers`, `layout.injective` and `layout.coherent`, each a function from
a `Target` and a `World` to rows of the one report format, plus the audit form of coherence for
an emitter that is not generated from the datum.

**Depends on.** `Conform.Layout.Layout`, `Conform.Core.{Report,Obligation}`.

**Properties.**
* **The subjects are the nestings the world uses.** `subjects` is every field type of every
  constructor of every type in the world, every ground type of the world, and the target's
  declared usages, deduplicated by spelling — so `Option (Option Ty)` is a subject exactly
  because `GenTy.joinAnswer` returns one and the target declares it, and `Option Ty` is one
  because `GenTy.answer` is one — *by construction*.
* **A counterexample is produced, not asserted.** When `admissible` refuses, the check encodes
  the enumerated values with the target's own `encodeAt` and looks for two distinct source
  values with one target value; the row carries both, rendered, and the target value they
  share — *by construction* (`findCollision`).
* **Coherence is the same rule read backwards.** The derived form round-trips
  `decodeAt ∘ encodeAt`; since both are derived from one `Rule`, a failure is a failure of the
  *rule*, never of two emitters disagreeing — *by construction*.
* **An unresolved subject is a row.** Every subject reaches exactly one row, and `expected` is
  the subject count, so `Report.complete` refuses a run that dropped one — *by construction*.
-/

namespace Conform.Layout

open Lean (Name Json ToJson toJson)

/-- What a run of the checks is allowed to spend. -/
structure Config where
  /-- Enumeration depth: the nesting of constructors in a sample value. -/
  depth : Nat := 6
  /-- How many values are kept per field position, so a wide product does not explode. -/
  width : Nat := 2
  /-- The encode/decode recursion budget. -/
  fuel : Nat := 32
  /-- How many enumerated values one subject is checked on. -/
  sample : Nat := 512
deriving Inhabited

/-! ## Subjects -/

private def dedupRefs (xs : Array TypeRef) : Array TypeRef :=
  xs.foldl (fun acc t => if acc.any (· == t) then acc else acc.push t) #[]

/-- Every nesting the world actually uses, plus the target's declared usages. -/
def subjects (T : Target) (W : World) : Array TypeRef :=
  let ground := W.types.filterMap fun tv =>
    if tv.params.isEmpty then some (TypeRef.con tv.name []) else none
  let fields := W.types.flatMap fun tv =>
    (tv.ctors.flatMap fun cv => cv.fields.map (·.type)).toArray
  let declared := T.usages.map (·.type)
  dedupRefs (ground ++ fields ++ declared ++ W.applications) |>.filter fun t => !t.hasParam

/-! ## `layout.covers` -/

private def subjectOf (kind : String) (path : List String) : Subject := { kind, path }

/-- Every type, constructor and payload position of the world has a rule, and the rule's
declared container is the one its discrimination induces. -/
def checkCovers (T : Target) (W : World) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  for tv in W.types do
    let subj := subjectOf "type" [T.name, tv.name.toString]
    match T.rule? tv.name with
    | none =>
      rows := rows.push (Row.unresolved "layout.covers" subj
        s!"target {T.name} has no rule for {tv.name}")
      for cv in tv.ctors do
        rows := rows.push (Row.unresolved "layout.covers"
          (subjectOf "constructor" [T.name, tv.name.toString, cv.name])
          s!"target {T.name} has no rule for {tv.name}, so none for {tv.name}.{cv.name}")
    | some r =>
      if r.container != derivedContainer r.discrimination then
        rows := rows.push (Row.refused "layout.covers" subj
          s!"declared container {r.container}, but {r.discrimination} induces \
{derivedContainer r.discrimination}")
      else
        rows := rows.push (Row.pass "layout.covers" subj .tested
          s!"{r.discrimination}, container {r.container}"
          (Json.mkObj [("discrimination", Json.str (toString r.discrimination)),
            ("container", Json.str (toString r.container)),
            ("scalar", match r.scalar with
              | some s => Json.str (toString s) | none => Json.null)]))
      for cv in tv.ctors do
        let csubj := subjectOf "constructor" [T.name, tv.name.toString, cv.name]
        match Target.ctorRule? r cv.name with
        | none =>
          rows := rows.push (Row.unresolved "layout.covers" csubj
            s!"target {T.name} has no rule for {tv.name}.{cv.name}")
        | some cr =>
          let want := cv.fields.length
          let got := match cr.payload with
            | .named fs => fs.length
            | .positional => want
            | .erased => 0
            | .single => 1
          if got != want then
            rows := rows.push (Row.refused "layout.covers" csubj
              s!"the rule carries {got} payload positions, the declaration has {want} relevant \
fields ({", ".intercalate (cv.fields.map (·.name))})")
          else
            rows := rows.push (Row.pass "layout.covers" csubj .tested
              s!"tag `{cr.tag}`/{cr.intTag}, payload {cr.payload}"
              (Json.mkObj [("tag", Json.str cr.tag), ("intTag", Json.num cr.intTag),
                ("payload", Json.str (toString cr.payload)),
                ("fields", Json.arr ((cv.fields.map (·.name)).toArray.map Json.str))]))
  -- a rule for a type the world does not describe: a scalar needs none, anything else is
  -- unchecked and says so.
  for r in T.rules do
    if (W.find? r.type).isSome then continue
    let subj := subjectOf "type" [T.name, r.type.toString]
    match r.discrimination with
    | .nativeScalar _ =>
      rows := rows.push (Row.pass "layout.covers" subj .tested
        s!"{r.discrimination}, container {r.container}: a scalar needs no constructor information"
        (Json.mkObj [("discrimination", Json.str (toString r.discrimination)),
          ("scalar", match r.scalar with | some s => Json.str (toString s) | none => Json.null)]))
    | _ =>
      rows := rows.push (Row.unresolved "layout.covers" subj
        s!"the rule for {r.type} is {r.discrimination}, and the world carries no constructor information for it, so nothing checked it")
  return rows

/-- The subjects `checkCovers` sets out to cover. -/
def coversExpected (T : Target) (W : World) : Nat :=
  W.types.foldl (init := 0) (fun n tv => n + 1 + tv.ctors.length)
    + (T.rules.filter fun r => (W.find? r.type).isNone).size

/-- Coverage identities are planned from the world and target, before any check runs. -/
def coversRequired (T : Target) (W : World) : Array CheckId :=
  (W.types.flatMap fun tv =>
    #[⟨"layout.covers", ⟨"type", [T.name, tv.name.toString]⟩⟩] ++
    tv.ctors.toArray.map (fun cv =>
      ⟨"layout.covers", ⟨"constructor", [T.name, tv.name.toString, cv.name]⟩⟩)) ++
  ((T.rules.filter fun r => (W.find? r.type).isNone).map fun r =>
    ⟨"layout.covers", ⟨"type", [T.name, r.type.toString]⟩⟩)

def required (T : Target) (W : World) : Array CheckId :=
  coversRequired T W ++ #["layout.injective", "layout.coherent"].flatMap (fun check =>
    (subjects T W).map fun ty => ⟨check, ⟨"nesting", [T.name, (Lean.toJson ty).compress]⟩⟩)

/-! ## `layout.injective` -/

/-- Two distinct source values with one target value, found by running the target's own
encoder over the enumerated values of the type. -/
def findCollision (T : Target) (W : World) (cfg : Config) (ty : TypeRef) :
    Option (DataValue × DataValue × TVal) := Id.run do
  let vs := (valuesAt T W cfg.depth cfg.width ty).take cfg.sample
  -- keyed by the *rendered* target value, which is what a counterexample row prints; the first
  -- source value that reached a key is the one the row names as `left`.
  let mut seen : Std.HashMap String (DataValue × TVal) := {}
  for v in vs do
    match encodeAt T W cfg.fuel ty v with
    | .error _ => continue
    | .ok t =>
      let key := t.render
      match seen[key]? with
      | some (w, tw) => if w != v then return some (w, v, tw)
      | none => seen := seen.insert key (v, t)
  return none

/-- The rule's admissibility condition at every nesting the world uses. -/
def checkInjective (T : Target) (W : World) (cfg : Config) : Array Row × Array Obligation :=
  Id.run do
  let mut rows : Array Row := #[]
  let mut obligations : Array Obligation := #[]
  for ty in subjects T W do
    let subj := subjectOf "nesting" [T.name, (Lean.toJson ty).compress]
    match admissible T W ty with
    | .admissible law =>
      let scalarNote := match T.ruleFor? ty with
        | some r => match r.scalar, r.domainRestriction with
          | some (.bounded bits), some restriction =>
            some (bits, restriction)
          | _, _ => none
        | none => none
      match scalarNote with
      | some (bits, restriction) =>
        obligations := obligations.push
          { kind := "representation.scalar-domain"
            subject := subj
            status := .unproved
            profile := T.name
            statement := s!"every {ty.render} this target carries satisfies `{restriction}` \
(the target scalar is exact only below 2^{bits}); the layout check does not see the use sites"
            detail := Json.mkObj [("bits", Json.num bits),
              ("restriction", Json.str restriction)] }
      | none => pure ()
      rows := rows.push (Row.pass "layout.injective" subj .tested
        s!"admissible: {law}"
        (Json.mkObj [("law", Json.str law), ("type", Json.str ty.render)]))
    | .inadmissible reason law =>
      match findCollision T W cfg ty with
      | some (a, b, t) =>
        rows := rows.push (Row.counterexample "layout.injective" subj
          s!"{reason}; {a.render} and {b.render} are both {t.render}"
          (Json.mkObj [("reason", Json.str reason), ("law", Json.str law),
            ("type", Json.str ty.render),
            ("left", Json.str a.render), ("right", Json.str b.render),
            ("target", Json.str t.render)]))
      | none =>
        rows := rows.push (Row.refused "layout.injective" subj
          s!"{reason} (no collision inside depth {cfg.depth}, width {cfg.width})"
          (Json.mkObj [("reason", Json.str reason), ("law", Json.str law),
            ("type", Json.str ty.render), ("searchDepth", Json.num cfg.depth)]))
    | .undecided reason =>
      rows := rows.push (Row.unresolved "layout.injective" subj reason
        (Json.mkObj [("type", Json.str ty.render)]))
  return (rows, obligations)

/-! ## `layout.coherent`, derived form -/

/-- Construction, destruction and projection read one rule: the round trip on the enumerated
values of every subject. -/
def checkCoherent (T : Target) (W : World) (cfg : Config) : Array Row := Id.run do
  let mut rows : Array Row := #[]
  for ty in subjects T W do
    let subj := subjectOf "nesting" [T.name, (Lean.toJson ty).compress]
    let vs := (valuesAt T W cfg.depth cfg.width ty).take cfg.sample
    let mut failure : Option Row := none
    let mut checked : Nat := 0
    for v in vs do
      if failure.isSome then continue
      match encodeAt T W cfg.fuel ty v with
      | .error e =>
        failure := some (Row.refused "layout.coherent" subj
          s!"construction refused {v.render}: {e.render}"
          (Json.mkObj [("value", Json.str v.render), ("error", e.toJson)]))
      | .ok t =>
        match decodeAt T W cfg.fuel ty t with
        | .error e =>
          failure := some (Row.refused "layout.coherent" subj
            s!"destruction refused the construction of {v.render} ({t.render}): {e.render}"
            (Json.mkObj [("value", Json.str v.render), ("target", Json.str t.render),
              ("error", e.toJson)]))
        | .ok w =>
          if v == w then checked := checked + 1
          else
            failure := some (Row.counterexample "layout.coherent" subj
              s!"{v.render} constructs as {t.render} and destructs as {w.render}"
              (Json.mkObj [("value", Json.str v.render), ("target", Json.str t.render),
                ("recovered", Json.str w.render)]))
    match failure with
    | some r => rows := rows.push r
    | none =>
      if vs.isEmpty then
        rows := rows.push (Row.unresolved "layout.coherent" subj
          s!"no value of {ty.render} could be enumerated at depth {cfg.depth}")
      else
        rows := rows.push (Row.pass "layout.coherent" subj .tested
          s!"{checked} values construct and destruct to themselves"
          (Json.mkObj [("values", Json.num checked), ("depth", Json.num cfg.depth)]))
  return rows

/-! ## `layout.coherent`, audit form: an emitter that is not generated from the datum -/

/-- One `(type, constructor)` row of a table recovered from an emitter's output, in the datum's
own vocabulary: `<discrimination>/<payload>`. -/
structure EmitterRow where
  type : Name
  ctor : String
  shape : String
  /-- The source text the row was recovered from, so a reader can check the recovery. -/
  evidence : String := ""
deriving Inhabited, ToJson

/-- The two tables recovered from one emitter: how it *builds* each constructor and how it
*takes it apart*. Its JSON is a report artefact (`ocaml-recovered-table.json`), and the record
*is* that schema, so the encoder is derived; the *reader* stays on `Conform.Policy`, because a
recovered table arrives from a fixture file and an unknown key there must be refused. -/
structure EmitterTable where
  name : String
  construction : Array EmitterRow := #[]
  destruction : Array EmitterRow := #[]
deriving Inhabited, ToJson

namespace EmitterTable

private def rowReader (j : Json) : Policy.Reader EmitterRow := do
  let get ← Policy.object j ["type", "ctor", "shape", "evidence"]
  let type ← Policy.field get "type" Policy.name
  let ctor ← Policy.field get "ctor" Policy.string
  let shape ← Policy.field get "shape" Policy.string
  let evidence ← Policy.field? get "evidence" Policy.string
  pure { type, ctor, shape, evidence := evidence.getD "" }

/-- A recovered table read from a fixture file: the format `Conform.Policy` refuses an unknown
key of. -/
def reader (j : Json) : Policy.Reader EmitterTable := do
  let get ← Policy.object j ["name", "note", "construction", "destruction"]
  let name ← Policy.field get "name" Policy.string
  let _ ← Policy.field? get "note" Policy.string
  let construction ← Policy.field get "construction" fun a => Policy.array a rowReader
  let destruction ← Policy.field get "destruction" fun a => Policy.array a rowReader
  pure { name, construction, destruction }

def load (file : System.FilePath) : IO EmitterTable := Policy.load file reader

end EmitterTable

/-- The shape the datum itself prescribes for one constructor. -/
def shapeOf (T : Target) (type : Name) (ctor : String) : Option String := do
  let r ← T.rule? type
  let cr ← Target.ctorRule? r ctor
  pure (toString r.discrimination ++ "/" ++ toString cr.payload)

/-- The audit: a construction rule and a destruction rule that disagree are refused, and a
rule that disagrees with the target datum is refused, whichever side it is on. -/
def auditRequired (tbl : EmitterTable) : Array CheckId :=
  ((tbl.construction ++ tbl.destruction).toList.map fun r =>
    (⟨"layout.coherent", ⟨"constructor", [tbl.name, r.type.toString, r.ctor]⟩⟩ : CheckId)).eraseDups.toArray

def auditCoherence (T : Target) (tbl : EmitterTable) : Array Row := Id.run do
  -- one index per side: the *first* row for a `(type, constructor)` is the one compared, which
  -- is what the linear `Array.find?` this replaces answered.
  let index (rows : Array EmitterRow) : Std.HashMap (Name × String) EmitterRow :=
    rows.foldl (init := {}) fun m r => if m.contains (r.type, r.ctor) then m else m.insert (r.type, r.ctor) r
  let consIdx := index tbl.construction
  let destIdx := index tbl.destruction
  let mut keys : Array (Name × String) := #[]
  let mut seen : Std.HashSet (Name × String) := {}
  for r in tbl.construction ++ tbl.destruction do
    unless seen.contains (r.type, r.ctor) do
      seen := seen.insert (r.type, r.ctor)
      keys := keys.push (r.type, r.ctor)
  let mut rows : Array Row := #[]
  for (ty, c) in keys do
    let subj := subjectOf "constructor" [tbl.name, ty.toString, c]
    let cons := consIdx[(ty, c)]?
    let dest := destIdx[(ty, c)]?
    match cons, dest with
    | none, none => rows := rows.push (Row.unresolved "layout.coherent" subj "no row on either side")
    | some _, none =>
      rows := rows.push (Row.unresolved "layout.coherent" subj
        s!"{tbl.name} builds {ty}.{c} and never takes it apart: no destruction rule to compare")
    | none, some _ =>
      rows := rows.push (Row.unresolved "layout.coherent" subj
        s!"{tbl.name} takes {ty}.{c} apart and never builds it: no construction rule to compare")
    | some k, some d =>
      if k.shape != d.shape then
        rows := rows.push (Row.refused "layout.coherent" subj
          s!"{tbl.name} builds {ty}.{c} as {k.shape} and destructs it as {d.shape}"
          (Json.mkObj [("construction", Json.str k.shape), ("destruction", Json.str d.shape),
            ("constructionEvidence", Json.str k.evidence),
            ("destructionEvidence", Json.str d.evidence)]))
      else match shapeOf T ty c with
        | none =>
          rows := rows.push (Row.unresolved "layout.coherent" subj
            s!"target {T.name} has no rule for {ty}.{c}, so the emitter's {k.shape} cannot be \
compared with a declared layout")
        | some want =>
          if want != k.shape then
            rows := rows.push (Row.refused "layout.coherent" subj
              s!"{tbl.name} builds and destructs {ty}.{c} as {k.shape}, and the {T.name} layout \
says {want}"
              (Json.mkObj [("emitter", Json.str k.shape), ("declared", Json.str want),
                ("constructionEvidence", Json.str k.evidence)]))
          else
            rows := rows.push (Row.pass "layout.coherent" subj .tested
              s!"construction, destruction and the {T.name} layout all say {want}"
              (Json.mkObj [("shape", Json.str want),
                ("constructionEvidence", Json.str k.evidence),
                ("destructionEvidence", Json.str d.evidence)]))
  return rows

/-! ## The obligation kinds this module emits -/

def registry : Obligation.Registry :=
  [ { id := "representation.scalar-domain"
      description := "the target's scalar is exact only on part of the source domain, and the \
rule declares the restriction it assumes; nothing here checks the use sites" }
  , { id := "representation.image-missing"
      description := "a container model needs an element model that was not supplied" }
  , { id := "representation.law-missing"
      description := "a container model needs a law of its element that was not supplied" }
  , { id := "representation.membership-missing"
      description := "an image has no `hasTy` theorem: it needs a premise the model cannot \
supply (an allocation table), or its type is uninhabited today" } ]

end Conform.Layout
