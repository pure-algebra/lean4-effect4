import Lean
import Conform.Core.Report
import Conform.Core.Policy

/-!
# Conform.Lcnf.Rules — a typing algorithm's rules as data, and the three-column join

**What it is.** Two things.

*The extraction* (§1–§3): for a configured **algorithm** declaration and the family it is structural
in, the top-level `cases` of its mono-phase LCNF is split into one *rule summary* per constructor —
the callees the arm invokes, in order; the literals it writes; how many list appends and conses it
performs (the shape an environment extension takes after compilation); whether it has a path that
refuses; and the join points, jumps and nested `cases` the compiler left. It is a **summary**, not
a semantics: §3.1 says exactly what mono LCNF loses.

*The join* (§4–§6): one object per constructor with three columns —

1. **Lean**, the extracted rule summary above;
2. **the target**, a head table measured from the target's own checker (`rows[].ctor`,
   `.checker.{A,E,R}`, `.lean.{A,E,R}`, `.wellTyped`, `.diagnostics`);
3. **the second implementation**, a coverage table of qualified constructor names with the count of
   uses in a golden corpus its own checker is run against,

and a set of **signals**: mechanically computed reasons the three do not line up. A signal is not a
verdict. The configuration *declares* the signals the record already knows about, each with the
register row that owns it, and the check is the two-way comparison: an undeclared signal is a
counterexample, a declared signal that has gone away is a refusal (the declaration is stale), and a
declared signal still present passes at evidence **assumed** — never higher, because a declared
disagreement is an open defect, not a proof of anything.

**Depends on.** `Lean`, `Conform.Core.Report`, `Conform.Core.Policy`. No repository module: which
algorithm, which family, which head table, which normalisation and which disagreements are known
are all configuration (`tools/Conform/Effect4/rules.json` for this tree).
-/

namespace Conform.Lcnf

open Lean Compiler LCNF

/-! ## 1. The rule summary -/

/-- What one alternative of the algorithm's top-level `cases` does, as the compiler left it. -/
structure ArmSummary where
  /-- The constructor, as a short name; `_default` for a default arm. -/
  ctor : Name
  /-- Every constant the arm applies, in walk order, with repeats: the arm's call sequence. -/
  callees : Array Name
  /-- Those of `callees` under one of the configured salient prefixes — the algorithm's own
  vocabulary, with the runtime's `Option`/`List` plumbing dropped. -/
  salient : Array Name
  /-- The literals the arm writes. -/
  literals : Array String
  /-- Applications of the configured list-append constant: an environment extension
  (`env ++ [t]`) after compilation. -/
  appends : Nat
  /-- Applications of the configured list-cons constant: how long the appended list is. -/
  conses : Nat
  /-- Applications of the configured refusal constant (`Option.none`): the arm has a path that
  refuses. `0` means it cannot refuse *at this level* — a callee may still. -/
  refusals : Nat
  /-- Join points the compiler introduced in this arm. -/
  joinPoints : Nat
  jumps : Nat
  /-- The scrutinee families of the `cases` nodes nested inside this arm, in order. -/
  nestedCases : Array Name
  /-- The binder names of the **bound functions** the arm applies, in order. After a structure's
  `cases` these are that structure's field names, so `sig.dom op` shows up here as `dom` — which
  is how a landed guard on a record field is pinned at all: a field is a projection, never a
  callee, so `callees` cannot see it. -/
  applied : Array Name
  /-- `<structure>#<index>` for each projection the arm takes. -/
  projections : Array String
  /-- Nodes walked: the arm's size, so a summary can be read against how much was summarised. -/
  nodes : Nat
deriving Inhabited

namespace ArmSummary

def toJson (a : ArmSummary) : Json :=
  Json.mkObj
    [ ("constructor", Json.str a.ctor.toString)
    , ("callees", Json.arr (a.callees.map fun c => Json.str c.toString))
    , ("salientCallees", Json.arr (a.salient.map fun c => Json.str c.toString))
    , ("literals", Json.arr (a.literals.map Json.str))
    , ("envExtensions", Json.mkObj [("appends", Json.num a.appends), ("conses", Json.num a.conses)])
    , ("canRefuse", Json.bool (a.refusals > 0))
    , ("refusals", Json.num a.refusals)
    , ("joinPoints", Json.num a.joinPoints)
    , ("jumps", Json.num a.jumps)
    , ("nestedCases", Json.arr (a.nestedCases.map fun c => Json.str c.toString))
    , ("appliedBinders", Json.arr (a.applied.map fun c => Json.str c.toString))
    , ("projections", Json.arr (a.projections.map Json.str))
    , ("nodes", Json.num a.nodes) ]

end ArmSummary

/-- What the extractor is told to look for. Every constant name here is configuration: the module
knows the *shapes* (a refusal, an append, a cons), not the names. -/
structure Algorithm where
  /-- The declaration whose mono LCNF is read. -/
  name : Name
  /-- The family its top-level `cases` scrutinises. -/
  family : Name
  /-- Name prefixes that make a callee salient. -/
  salient : Array Name
  /-- The constant an arm applies to refuse (`Option.none`). -/
  refusal : Name
  /-- The list-append constant (`List.append`). -/
  append : Name
  /-- The list-cons constant (`List.cons`). -/
  cons : Name
  /-- Per constructor, the callees the arm **must** contain. This is how a landed guard is pinned:
  DI-54's domain check is "the `perform` arm calls `Signature.dom`", and that is a fact about the
  compiled code, not about a comment. -/
  requires : Array (Name × Array Name) := #[]
deriving Inhabited

/-! ## 2. The walk -/

private structure ArmState where
  callees : Array Name := #[]
  literals : Array String := #[]
  appends : Nat := 0
  conses : Nat := 0
  refusals : Nat := 0
  joinPoints : Nat := 0
  jumps : Nat := 0
  nested : Array Name := #[]
  applied : Array Name := #[]
  projections : Array String := #[]
  nodes : Nat := 0

private def litText : LetValue .pure → Option String
  | .lit (.nat n) => some s!"nat {n}"
  | .lit (.str s) => some s!"str {s}"
  | .lit (.uint8 n) => some s!"uint8 {n}"
  | .lit (.uint16 n) => some s!"uint16 {n}"
  | .lit (.uint32 n) => some s!"uint32 {n}"
  | .lit (.uint64 n) => some s!"uint64 {n}"
  | .lit (.usize n) => some s!"usize {n}"
  | _ => none

private abbrev Binders := Std.HashMap FVarId Name

private def bindParams (ns : Binders) (ps : Array (Param .pure)) : Binders :=
  ps.foldl (fun ns p => ns.insert p.fvarId p.binderName) ns

private partial def walkArm (alg : Algorithm) (ns : Binders) : Code .pure → StateM ArmState Unit
  | .let decl k => do
    modify fun s => { s with nodes := s.nodes + 1 }
    match decl.value with
    | .const n _ _ =>
      modify fun s => { s with
        callees := s.callees.push n
        appends := if n == alg.append then s.appends + 1 else s.appends
        conses := if n == alg.cons then s.conses + 1 else s.conses
        refusals := if n == alg.refusal then s.refusals + 1 else s.refusals }
    | .fvar f args =>
      -- a bound function applied: after a structure `cases`, this is a FIELD of that structure
      -- being called, and the binder name is the field's name (`sig.dom op` ↦ `dom`)
      if !args.isEmpty then
        modify fun s => { s with applied := s.applied.push (ns.getD f `_unknown) }
    | .proj typeName idx _ =>
      modify fun s => { s with projections := s.projections.push s!"{typeName}#{idx}" }
    | v =>
      match litText v with
      | some t => modify fun s => { s with literals := s.literals.push t }
      | none => pure ()
    walkArm alg (ns.insert decl.fvarId decl.binderName) k
  | .fun d k => do
    modify fun s => { s with nodes := s.nodes + 1 }
    let ns' := ns.insert d.fvarId d.binderName
    walkArm alg (bindParams ns' d.params) d.value
    walkArm alg ns' k
  | .jp d k => do
    modify fun s => { s with nodes := s.nodes + 1, joinPoints := s.joinPoints + 1 }
    let ns' := ns.insert d.fvarId d.binderName
    walkArm alg (bindParams ns' d.params) d.value
    walkArm alg ns' k
  | .jmp .. => modify fun s => { s with nodes := s.nodes + 1, jumps := s.jumps + 1 }
  | .return _ => modify fun s => { s with nodes := s.nodes + 1 }
  | .unreach _ => modify fun s => { s with nodes := s.nodes + 1 }
  | .cases c => do
    modify fun s => { s with nodes := s.nodes + 1, nested := s.nested.push c.typeName }
    for a in c.alts do
      match a with
      | .alt _ params code => walkArm alg (bindParams ns params) code
      | .default code => walkArm alg ns code

private def summarise (alg : Algorithm) (ctor : Name) (code : Code .pure) : ArmSummary :=
  let (_, st) := (walkArm alg {} code).run {}
  { ctor
  , callees := st.callees
  , salient := st.callees.filter fun c => alg.salient.any fun p => p.isPrefixOf c
  , literals := st.literals
  , appends := st.appends, conses := st.conses, refusals := st.refusals
  , joinPoints := st.joinPoints, jumps := st.jumps
  , nestedCases := st.nested, applied := st.applied, projections := st.projections
  , nodes := st.nodes }

/-- The first `cases` on `alg.family` in the declaration's code, in pre-order. Returns `none` when
the declaration has no mono code, is an `extern` stub, or never scrutinises the family. -/
private partial def topCases (family : Name) : Code .pure → Option (Cases .pure)
  | .let _ k => topCases family k
  | .fun d k => (topCases family d.value).orElse fun _ => topCases family k
  | .jp d k => (topCases family d.value).orElse fun _ => topCases family k
  | .jmp .. => none
  | .return _ => none
  | .unreach _ => none
  | .cases c =>
    if c.typeName == family then some c
    else c.alts.foldl (init := none) fun acc a =>
      acc.orElse fun _ => topCases family a.getCode

/-! ## 3. Extraction

### 3.1 What mono LCNF loses here, exactly

Measured on this tree's `effTy` (§ of the seat note) and true of any algorithm read this way:

* **The `do`-notation is gone.** An `Option` `do` block is compiled to nested `cases` on `Option`,
  so "the arm binds `a ← effTy …` and refuses when it is `none`" appears as a `cases Option` whose
  `none` alternative returns the configured refusal constant. `refusals > 0` therefore means "the
  arm has an explicit refusal in *its own* code" — a callee that refuses is invisible here.
* **Join points and inlining move code across arms.** A shared tail (`some ⟨answer, …⟩`) becomes a
  `jp` above the `cases`, so it is counted in no arm; a small callee is inlined into an arm and its
  own callees then appear as that arm's. `joinPoints`/`jumps` are reported so a reader can see when
  this happened rather than being surprised by it.
* **`cases` grouping is the compiler's.** Constructors whose arms compiled to the same code share
  one alternative or fall into a default; the extraction reports what the compiler wrote, which is
  why a constructor can be missing from the summary while its rule exists in the source.
* **Types are erased.** `EffTy`'s three fields are projections by index; nothing here recovers
  "the answer column". That is why the target column cannot be *derived* from this one and the join
  is a join, not a comparison.

The extraction therefore answers precise questions — *which constants does this rule call, can it
refuse, how many environment extensions does it build* — and does not answer "what type does this
rule assign". -/

structure Extraction where
  algorithm : Name
  /-- The declaration whose code was actually summarised: `algorithm`, or the end of its
  forwarder chain. -/
  body : Name
  /-- The forwarder chain from `algorithm` to `body`, inclusive. -/
  chain : Array Name
  family : Name
  /-- The constructors of the family, in declaration order. -/
  constructors : Array Name
  arms : Array ArmSummary
  /-- Constructors of the family with no alternative of their own at the top-level `cases`. -/
  withoutArm : Array Name
  hasDefault : Bool
deriving Inhabited

namespace Extraction

def armOf? (e : Extraction) (c : Name) : Option ArmSummary := e.arms.find? fun a => a.ctor == c

def toJson (e : Extraction) : Json :=
  Json.mkObj
    [ ("algorithm", Json.str e.algorithm.toString)
    , ("body", Json.str e.body.toString)
    , ("forwarderChain", Json.arr (e.chain.map fun c => Json.str c.toString))
    , ("family", Json.str e.family.toString)
    , ("constructors", Json.arr (e.constructors.map fun c => Json.str c.toString))
    , ("withoutArm", Json.arr (e.withoutArm.map fun c => Json.str c.toString))
    , ("hasDefault", Json.bool e.hasDefault)
    , ("rules", Json.arr (e.arms.map ArmSummary.toJson)) ]

end Extraction

/-- A declaration whose whole mono code is `let x := f a b c; return x` is a **forwarder**: the
compiler moved the body to `f` and left a tail call. `Effect4.Program.effTy` is exactly this — its
mono code is one line calling `Effect4.Program.effTy._redArg`, and the twenty-seven arms are in
*that* declaration, which is not an environment constant at all.

Following the call is therefore not a convenience, it is the difference between reading the rules
and reading nothing. The chain is bounded and reported, so a reader always knows which declaration
was actually summarised. -/
private def forwardsTo? : Code .pure → Option Name
  | .let decl (.return x) =>
    if decl.fvarId == x then
      match decl.value with
      | .const n _ _ => some n
      | _ => none
    else none
  | _ => none

/-- Read the algorithm's mono LCNF and summarise every alternative of its top-level `cases`. -/
def extractAlgorithm (alg : Algorithm) : CoreM (Except String Extraction) := do
  let env ← getEnv
  let ctors : Array Name ← match env.find? alg.family with
    | some (.inductInfo i) => pure (i.ctors.toArray.map fun c => c.getString!.toName)
    | some _ => return .error s!"`{alg.family}` is a constant but not an inductive type"
    | none => return .error s!"`{alg.family}` is not a constant of the imported environment"
  -- follow forwarders to the declaration that actually holds the code
  let mut current := alg.name
  let mut chain : Array Name := #[alg.name]
  let mut code : Code .pure := .unreach default
  for _ in [0:4] do
    let some decl ← getMonoDecl? current
      | return .error s!"`{current}` has no mono-phase LCNF entry (no code, or its module was \
                         built by a compiler that did not persist the mono phase)"
    match decl.value with
    | .extern _ => return .error s!"`{current}`'s mono entry is an `extern` stub, not code"
    | .code c =>
      code := c
      match forwardsTo? c with
      | some next =>
        if chain.contains next then
          return .error s!"`{alg.name}`'s forwarder chain loops at `{next}`"
        current := next
        chain := chain.push next
      | none => break
  let some cs := topCases alg.family code
    | return .error s!"`{current}` has mono code but no `cases` on `{alg.family}` in it \
                       (followed from {" → ".intercalate (chain.toList.map (·.toString))})"
  let mut arms : Array ArmSummary := #[]
  let mut hasDefault := false
  for a in cs.alts do
    match a with
    | .alt ctor _ armCode => arms := arms.push (summarise alg (ctor.getString!.toName) armCode)
    | .default armCode => hasDefault := true; arms := arms.push (summarise alg `_default armCode)
  let named := arms.map (·.ctor)
  return .ok
    { algorithm := alg.name, body := current, chain, family := alg.family
    , constructors := ctors, arms
    , withoutArm := ctors.filter fun c => !named.contains c
    , hasDefault }

/-! ## 4. The other two columns -/

/-- One row of a target head table, as measured by the target's own checker. -/
structure HeadRow where
  /-- The row's key: `<constructor>` or `<constructor>/<variant>`. -/
  key : String
  /-- The constructor the row belongs to: `key` up to the first `/`. -/
  ctor : String
  /-- The target checker's three columns, verbatim. -/
  checker : String × String × String
  /-- The model's three columns as the table's author transcribed them — **a human's column**,
  which in this tree carries prose in places, so a textual difference is a *spelling* signal and
  never a verdict on its own. -/
  model : String × String × String
  wellTyped : Bool
  diagnostics : Nat
deriving Inhabited

/-- How the two text columns are made comparable before they are compared: `import("…").` wrappers
dropped, then the declared substrings removed and the declared replacements applied, then
whitespace collapsed. Every step is configuration, so the report can say what it normalised. -/
structure Normalisation where
  stripImports : Bool := true
  strip : Array String := #[]
  replace : Array (String × String) := #[]
deriving Inhabited

namespace Normalisation

/-- Replace every `import("…").` run by nothing, keeping the member name that follows. -/
private def dropImports (s : String) : String := Id.run do
  let parts := s.splitOn "import(\""
  match parts with
  | [] => return s
  | head :: rest =>
    let mut out := head
    for p in rest do
      match p.splitOn "\")." with
      | _ :: tail => out := out ++ "\").".intercalate tail
      | [] => out := out ++ p
    return out

def apply (n : Normalisation) (s : String) : String := Id.run do
  let mut t := if n.stripImports then dropImports s else s
  for x in n.strip do t := t.replace x ""
  for (a, b) in n.replace do t := t.replace a b
  -- collapse runs of whitespace
  let mut out : List Char := []
  let mut space := false
  for c in t.toList do
    if c == ' ' || c == '\n' || c == '\t' then space := true
    else
      if space && !out.isEmpty then out := ' ' :: out
      space := false
      out := c :: out
  return String.ofList out.reverse

end Normalisation

/-- The head table, read from JSON. The shape is `{"rows": [{"ctor", "checker": {"A","E","R"},
"lean": {"A","E","R"}, "wellTyped", "diagnostics"}]}` — the shape a target-side oracle writes. -/
def readHeads (text : String) : Except String (Array HeadRow) := do
  let j ← Json.parse text
  let rows ← match j.getObjVal? "rows" with
    | .ok (.arr xs) => pure xs
    | .ok _ => throw "`rows` is not an array"
    | .error e => throw s!"no `rows` key: {e}"
  let str (o : Json) (k : String) : Except String String :=
    match o.getObjVal? k with
    | .ok (.str s) => .ok s
    | .ok (.null) => .ok "null"
    | .ok other => .ok other.compress
    | .error e => .error s!"no `{k}`: {e}"
  let triple (o : Json) (k : String) : Except String (String × String × String) := do
    let inner ← match o.getObjVal? k with
      | .ok v => pure v
      | .error e => throw s!"no `{k}`: {e}"
    return (← str inner "A", ← str inner "E", ← str inner "R")
  let mut out : Array HeadRow := #[]
  for r in rows do
    let key ← str r "ctor"
    let ctor := (key.splitOn "/").headD key
    let checker ← triple r "checker"
    let model ← triple r "lean"
    let wellTyped ← match r.getObjVal? "wellTyped" with
      | .ok (.bool b) => pure b
      | _ => throw s!"`{key}`: no boolean `wellTyped`"
    let diagnostics ← match r.getObjVal? "diagnostics" with
      | .ok (.arr xs) => pure xs.size
      | _ => pure 0
    out := out.push { key, ctor, checker, model, wellTyped, diagnostics }
  return out

/-- `Effect4.Program.Eff.scoped\t3` — a generated coverage table: a qualified constructor name, a
tab, the number of times a golden corpus uses it. -/
def readCoverage (text : String) (prefix_ : String) : Except String (Array (String × Nat)) := do
  let mut out : Array (String × Nat) := #[]
  for l in (text.splitOn "\n") do
    let t := l.trimAscii.toString
    if t.isEmpty then continue
    match t.splitOn "\t" with
    | [name, count] =>
      if name.startsWith prefix_ then
        match count.toNat? with
        | some n => out := out.push ((name.drop prefix_.length).toString, n)
        | none => throw s!"`{t}`: `{count}` is not a count"
    | _ => throw s!"`{t}`: expected `<name>\\t<count>`"
  return out

/-! ## 5. Signals -/

/-- A mechanically computed reason the three columns do not line up. The strings are the check's
stable vocabulary; a configuration declares which of them are known, per constructor. -/
inductive Signal
  /-- The algorithm has no alternative for this constructor at its top-level `cases`. -/
  | leanArmMissing
  /-- A callee the configuration requires of this arm is absent from the compiled code. -/
  | leanGuardMissing (callee : Name)
  /-- The head table has no row for this constructor. -/
  | targetMissing
  /-- Some head row for this constructor is ill-typed under the target's checker. -/
  | targetIllTyped (row : String)
  /-- The two columns of some head row differ after normalisation. -/
  | targetSpelling (column : String) (row : String) (checker : String) (model : String)
  /-- The second implementation's corpus never exercises this constructor. -/
  | secondUnexercised
deriving Inhabited

namespace Signal

/-- The stable id a configuration declares. -/
def id : Signal → String
  | .leanArmMissing => "lean.arm.missing"
  | .leanGuardMissing c => s!"lean.guard.missing:{c}"
  | .targetMissing => "target.missing"
  | .targetIllTyped _ => "target.illTyped"
  | .targetSpelling col _ _ _ => s!"target.spelling:{col}"
  | .secondUnexercised => "second.unexercised"

def detail : Signal → Json
  | .leanArmMissing => Json.null
  | .leanGuardMissing c => Json.str c.toString
  | .targetMissing => Json.null
  | .targetIllTyped r => Json.str r
  | .targetSpelling col r c m =>
    Json.mkObj [("column", Json.str col), ("row", Json.str r)
               , ("checker", Json.str c), ("model", Json.str m)]
  | .secondUnexercised => Json.null

def toJson (s : Signal) : Json :=
  Json.mkObj [("id", Json.str s.id), ("detail", s.detail)]

end Signal

/-- One declared disagreement: the signals the record already owns for a constructor, and where. -/
structure Known where
  ctor : Name
  signals : Array String
  /-- The register row or note that owns it. -/
  register : String
  reason : String
deriving Inhabited

/-- The whole A4 configuration. -/
structure RulesSpec where
  algorithm : Algorithm
  /-- The target's head table. -/
  heads : Option System.FilePath
  normalisation : Normalisation
  /-- The second implementation's coverage table, and the prefix its rows carry. -/
  coverage : Option System.FilePath
  coveragePrefix : String
  known : Array Known
  note : Option String := none
deriving Inhabited

/-! ### 5.1 The reader -/

namespace RulesSpec

open Conform.Policy

private def readAlgorithm (j : Json) : Policy.Reader Algorithm := do
  let get ← object j ["name", "family", "salient", "refusal", "append", "cons", "requires"]
  let name ← field get "name" Policy.name
  let family ← field get "family" Policy.name
  let salient ← field get "salient" fun s => array s Policy.name
  let refusal ← field get "refusal" Policy.name
  let append ← field get "append" Policy.name
  let cons ← field get "cons" Policy.name
  let requires ← field? get "requires" fun r => array r fun e => do
    let g ← object e ["constructor", "callees"]
    let c ← field g "constructor" Policy.name
    let cs ← field g "callees" fun x => array x Policy.name
    pure (c, cs)
  return { name, family, salient, refusal, append, cons, requires := requires.getD #[] }

private def readNormalisation (j : Json) : Policy.Reader Normalisation := do
  let get ← object j ["stripImports", "strip", "replace"]
  let stripImports ← field? get "stripImports" bool
  let strip ← field? get "strip" strings
  let replace ← field? get "replace" fun r => array r fun e => do
    let g ← object e ["from", "to"]
    let f ← field g "from" string
    let t ← field g "to" string
    pure (f, t)
  return { stripImports := stripImports.getD true, strip := strip.getD #[]
         , replace := replace.getD #[] }

private def readKnown (j : Json) : Policy.Reader Known := do
  let get ← object j ["constructor", "signals", "register", "reason"]
  let ctor ← field get "constructor" Policy.name
  let signals ← field get "signals" strings
  let register ← field get "register" string
  let reason ← field get "reason" string
  return { ctor, signals, register, reason }

def read (j : Json) : Policy.Reader RulesSpec := do
  let get ← object j
    ["algorithm", "heads", "normalisation", "coverage", "coveragePrefix", "known", "note"]
  let algorithm ← field get "algorithm" readAlgorithm
  let heads ← field? get "heads" string
  let normalisation ← field? get "normalisation" readNormalisation
  let coverage ← field? get "coverage" string
  let coveragePrefix ← field? get "coveragePrefix" string
  let known ← field? get "known" fun k => array k readKnown
  let note ← field? get "note" string
  return { algorithm
         , heads := heads.map fun (s : String) => (s : System.FilePath)
         , normalisation := normalisation.getD {}
         , coverage := coverage.map fun (s : String) => (s : System.FilePath)
         , coveragePrefix := coveragePrefix.getD ""
         , known := known.getD #[], note }

def load (file : System.FilePath) : IO RulesSpec := Policy.load file read

end RulesSpec

/-! ## 6. The join and its check -/

private def strList (xs : Array String) : String :=
  if xs.isEmpty then "none" else ", ".intercalate xs.toList

/-- Everything known about one constructor, in three columns plus the signals. -/
structure JoinRow where
  ctor : Name
  lean : Option ArmSummary
  heads : Array HeadRow
  exercised : Option Nat
  signals : Array Signal
deriving Inhabited

def JoinRow.toJson (r : JoinRow) (n : Normalisation) : Json :=
  Json.mkObj
    [ ("constructor", Json.str r.ctor.toString)
    , ("lean", match r.lean with | some a => a.toJson | none => Json.null)
    , ("target", Json.arr (r.heads.map fun h =>
        Json.mkObj
          [ ("row", Json.str h.key)
          , ("wellTyped", Json.bool h.wellTyped)
          , ("diagnostics", Json.num h.diagnostics)
          , ("checker", Json.mkObj
              [ ("A", Json.str h.checker.1), ("E", Json.str h.checker.2.1)
              , ("R", Json.str h.checker.2.2) ])
          , ("model", Json.mkObj
              [ ("A", Json.str h.model.1), ("E", Json.str h.model.2.1)
              , ("R", Json.str h.model.2.2) ])
          , ("normalised", Json.mkObj
              [ ("checkerA", Json.str (n.apply h.checker.1))
              , ("modelA", Json.str (n.apply h.model.1))
              , ("checkerE", Json.str (n.apply h.checker.2.1))
              , ("modelE", Json.str (n.apply h.model.2.1))
              , ("checkerR", Json.str (n.apply h.checker.2.2))
              , ("modelR", Json.str (n.apply h.model.2.2)) ]) ]))
    , ("second", match r.exercised with
        | some c => Json.mkObj [("exercised", Json.num c)]
        | none => Json.null)
    , ("signals", Json.arr (r.signals.map Signal.toJson)) ]

/-- The signals of one constructor: the whole of the join's mechanical content. -/
def signalsOf (spec : RulesSpec) (e : Extraction) (heads : Option (Array HeadRow))
    (coverage : Option (Array (String × Nat))) (c : Name) : Array Signal := Id.run do
  let mut out : Array Signal := #[]
  match e.armOf? c with
  | none => out := out.push .leanArmMissing
  | some arm =>
    for (ctor, callees) in spec.algorithm.requires do
      if ctor == c then
        for callee in callees do
          unless arm.callees.contains callee || arm.applied.contains callee do
            out := out.push (.leanGuardMissing callee)
  if let some hs := heads then
    let mine := hs.filter fun h => h.ctor == c.toString
    if mine.isEmpty then out := out.push .targetMissing
    for h in mine do
      unless h.wellTyped do out := out.push (.targetIllTyped h.key)
      let cols : List (String × String × String) :=
        [("A", h.checker.1, h.model.1), ("E", h.checker.2.1, h.model.2.1)
        , ("R", h.checker.2.2, h.model.2.2)]
      for (col, ck, md) in cols do
        let ck' := spec.normalisation.apply ck
        let md' := spec.normalisation.apply md
        if ck' != md' then out := out.push (.targetSpelling col h.key ck' md')
  if let some cov := coverage then
    match cov.find? fun (n, _) => n == c.toString with
    | some (_, 0) => out := out.push .secondUnexercised
    | some _ => pure ()
    | none => out := out.push .secondUnexercised
  return out

/-- The A4 run: extract, join, and judge each constructor against the declared disagreements.
Returns the table (for `--rules-out`), the rows and the subject count. -/
def extract (spec : RulesSpec) : CoreM (Json × Array Row × Nat) := do
  let algSubject : Subject :=
    { kind := "algorithm", path := [spec.algorithm.name.toString, spec.algorithm.family.toString] }
  match ← extractAlgorithm spec.algorithm with
  | .error e =>
    return (Json.null, #[Row.unresolved "rules.extract" algSubject e], 1)
  | .ok extraction =>
    let mut rows : Array Row := #[]
    let mut inputs : Array String := #[]
    rows := rows.push <| Row.pass "rules.extract" algSubject .tested
      s!"`{spec.algorithm.name}` has {extraction.arms.size} alternatives on `{spec.algorithm.family}`'s \
         {extraction.constructors.size} constructors\
         {if extraction.withoutArm.isEmpty then "" else s!"; without an arm of their own: {strList (extraction.withoutArm.map (·.toString))}"}"
      extraction.toJson
    -- the other two columns
    let heads ← match spec.heads with
      | none => pure none
      | some f =>
        if ← System.FilePath.pathExists f then
          match readHeads (← IO.FS.readFile f) with
          | .ok hs => inputs := inputs.push f.toString; pure (some hs)
          | .error e =>
            rows := rows.push <| Row.unresolved "rules.join.target"
              { kind := "file", path := [f.toString] } s!"the head table did not parse: {e}"
            pure none
        else
          rows := rows.push <| Row.unresolved "rules.join.target"
            { kind := "file", path := [f.toString] }
            "the head table named by the configuration does not exist"
          pure none
    let coverage ← match spec.coverage with
      | none => pure none
      | some f =>
        if ← System.FilePath.pathExists f then
          match readCoverage (← IO.FS.readFile f) spec.coveragePrefix with
          | .ok cs => inputs := inputs.push f.toString; pure (some cs)
          | .error e =>
            rows := rows.push <| Row.unresolved "rules.join.second"
              { kind := "file", path := [f.toString] } s!"the coverage table did not parse: {e}"
            pure none
        else
          rows := rows.push <| Row.unresolved "rules.join.second"
            { kind := "file", path := [f.toString] }
            "the coverage table named by the configuration does not exist"
          pure none
    -- one join row per constructor
    let mut joinRows : Array JoinRow := #[]
    for c in extraction.constructors do
      let signals := signalsOf spec extraction heads coverage c
      let jr : JoinRow :=
        { ctor := c
        , lean := extraction.armOf? c
        , heads := (heads.getD #[]).filter fun h => h.ctor == c.toString
        , exercised := (coverage.getD #[]).find? (fun (n, _) => n == c.toString) |>.map (·.2)
        , signals }
      joinRows := joinRows.push jr
      let subject : Subject :=
        { kind := "typingRule", path := [spec.algorithm.name.toString, c.toString] }
      -- ids, deduplicated: a constructor with four head-table variants can raise the same
      -- signal four times, and the declaration should name it once. The full list, with the
      -- rows it came from, stays in the row's detail.
      let observed := signals.map Signal.id |>.foldl (init := #[])
        fun acc i => if acc.contains i then acc else acc.push i
      let known? := spec.known.find? fun k => k.ctor == c
      let declared := (known?.map (·.signals)).getD #[]
      let unexpected := observed.filter fun s => !declared.contains s
      let vanished := declared.filter fun s => !observed.contains s
      let detail := jr.toJson spec.normalisation
      if !unexpected.isEmpty then
        rows := rows.push <| Row.counterexample "rules.join" subject
          s!"`{c}`: {strList unexpected} \
             {if unexpected.size == 1 then "is" else "are"} not a declared disagreement" detail
      else if !vanished.isEmpty then
        rows := rows.push <| Row.refused "rules.join" subject
          s!"`{c}`: the configuration declares {strList vanished}, which the join no longer \
             observes — either the defect was fixed and the declaration is stale, or the join \
             stopped looking{match known? with | some k => s!" ({k.register})" | none => ""}"
          detail
      else if declared.isEmpty then
        rows := rows.push <| Row.pass "rules.join" subject .tested
          s!"`{c}`: the three columns line up" detail
      else
        let k := known?.get!
        rows := rows.push <| Row.pass "rules.join" subject .assumed
          s!"`{c}`: declared disagreement, still present — {strList declared} ({k.register}: {k.reason})"
          detail
    let table := Json.mkObj
      [ ("algorithm", Json.str spec.algorithm.name.toString)
      , ("family", Json.str spec.algorithm.family.toString)
      , ("inputs", Json.arr (inputs.map Json.str))
      , ("extraction", extraction.toJson)
      , ("join", Json.arr (joinRows.map fun r => r.toJson spec.normalisation)) ]
    return (table, rows, rows.size)

end Conform.Lcnf
