import Lean
import Effect4.Store.Digest

/-!
# Tools.Variances — declaration-site variance, read off rc.112

    lake env lean -M4096 --run tools/Tools/Variances.lean tools/Effect4Gen/variances.json

Effect rc.112 declares the variance of a generic parameter **at the declaration site**, the way
TypeScript 4.7 spells it: `Ref<in out A>` (`Ref.ts:59`), `Fiber<out A, out E>` (`Fiber.ts:70`),
`Layer<in ROut, out E, out RIn>` (`Layer.ts:54`). Decisions row 55 took that as the source of
truth for `Ty.sub`'s congruence arms; until now it was transcribed by hand into a comment. This
driver reads it off the vendored source instead, so `tools/Effect4Gen/variances.json` — the input
of the `TyView` generator — is never hand-typed and the second source of truth disappears
(tooling plan 1.4a; the proof-engineering seat's fourth risk).

## The method, and why it is text and not a parser

The census idiom of `scripts/generate-effect-runtime-census.sh:1-18`: a literal anchor that must
occur exactly once, a line span, and a SHA-256 of exactly those bytes, so an upstream edit *above*
a declaration moves its line number without disturbing the digest while any edit *inside* it fails
the run. Here the span is one line — the declaration's own — and the anchor is the declaration
itself.

The reader finds `export interface <Name><…>` and `export type <Name><…> =` with balanced angle
brackets, splits the parameter list at top-level commas, and reads the leading `in`/`out`
modifiers. It is about a hundred and fifty lines and no TypeScript grammar: the modifiers are the
first words of a parameter and nothing else in the span can be mistaken for them. Every refusal is
fatal and names the file and the line.

## What is declared and what is inferred

`Exit` (`Exit.ts:59`) and `Option` (`Option.ts:55`) are **type aliases of unions**, so TypeScript
infers their variance from the constituents rather than reading a modifier. Their rows carry
`inferred`, and the inference is performed here, not assumed: the constituent interface names are
read out of the alias's right-hand side, each is looked up in the same file, and a parameter's
variance is the constituents' common declaration at that position — a disagreement is fatal rather
than resolved. `Success<out A, out E>` (`Exit.ts:118`) and `Failure<out A, out E>` (`:154`) give
`Exit` `[co, co]`; `None<out A>` (`Option.ts:75`) and `Some<out A>` (`:128`) give `Option` `[co]`.

## The head map

`Ty`'s parametrised constructors and the rc.112 declaration each one spells. Six are rc.112's own
(`refOf`, `deferredOf`, `fiberOf`, `causeOf`, `exitOf`, `option`); four are TypeScript's own
spelling or the printer's, carry `source: "printer"`, and get their variance from the printed form
(`Ty.renderRaw`, `src/Effect4/Program/Ty.lean:86-103`) rather than from a vendored interface. The
map itself is this module's one hand list, in the shape of `LayerView.leafSort`: a head with no
entry is refused rather than defaulted, so a new parametrised constructor cannot be generated
against a guess.

## The red controls

Checked here, fatal, and printed on every run: `Ref` reads `inv`, `Fiber` reads `co` at both
parameters, `Layer` reads `[contra, co, co]`, `Context` reads `contra`. A reader that lost the
`in` keyword, or that read the modifiers of the wrong parameter, fails on one of the four.

The cross-check is `ts/eff/ingest/census/decls-ck.ts:21-28`, whose `hasVariance` is "some type
parameter of this declaration carries an `in` or an `out` modifier" under `typescript@5.9.2`'s
own parser: this driver records the same boolean per declaration, so the two notions can be
compared without sharing a line of code.
-/

open Lean

namespace Tools.Variances

/-- The pinned Effect release this driver reads. -/
def version : String := "4.0.0-rc.112"

/-- The vendored source root, relative to the repository. -/
def root : String := "vendor/effect-4.0.0-rc.112/src"

/-- The output, relative to the repository. -/
def defaultOut : String := "tools/Effect4Gen/variances.json"

/-- The modules read, in the order their rows are written. The twelve of tooling plan 1.4a:
the six `Ty` heads take their declaration from the first six, `Effect`/`Scope`/`Layer`/`Context`
are read for the record and for the red controls, and `Queue`/`PubSub` are read ahead of the L7
service carriers so nobody writes a `sub` arm for them from memory. -/
def modules : List String :=
  ["Ref", "Deferred", "Fiber", "Cause", "Exit", "Effect",
   "Scope", "Context", "Layer", "Queue", "PubSub", "Option"]

/-! ## Variance -/

inductive Variance where
  /-- `out`: the parameter occurs only in output position. -/
  | co
  /-- `in`: only in input position. -/
  | contra
  /-- `in out`: both. -/
  | inv
  /-- No modifier on a declaration that carries modifiers elsewhere, or on one that carries none. -/
  | none
  /-- A type alias: TypeScript computes it from the constituents. -/
  | inferred
deriving BEq, Repr

def Variance.text : Variance → String
  | .co => "co"
  | .contra => "contra"
  | .inv => "inv"
  | .none => "none"
  | .inferred => "inferred"

/-- The modifiers as read, in the source's own spelling. -/
def Variance.ofModifiers (hasIn hasOut : Bool) : Variance :=
  match hasIn, hasOut with
  | true, true => .inv
  | true, false => .contra
  | false, true => .co
  | false, false => .none

/-! ## The text reader -/

structure Param where
  index : Nat
  name : String
  modifiers : String
  variance : Variance
deriving Repr

inductive Kind where
  | «interface»
  | «alias»
deriving BEq, Repr

def Kind.text : Kind → String
  | .«interface» => "interface"
  | .«alias» => "alias"

structure Decl where
  «module» : String
  name : String
  kind : Kind
  /-- One-based, as an editor and a `cite` count. -/
  line : Nat
  /-- The declaration line verbatim: the span the digest covers. -/
  text : String
  params : List Param
  /-- The alias's right-hand side, empty for an interface. -/
  rhs : String
deriving Repr

def Decl.cite (d : Decl) : String := s!"{root}/{d.«module»}.ts:{d.line}"

/-- `decls-ck.ts:21-28`'s notion, computed the other way: some parameter carries `in` or `out`. -/
def Decl.hasVariance (d : Decl) : Bool :=
  d.params.any fun p => p.modifiers != ""

private def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- `String.trim` is deprecated in this toolchain and `String.trimAscii` answers a slice; the
reader keeps its own so nothing downstream has to hold a `String.Slice`. -/
def trimS (s : String) : String :=
  String.ofList (s.toList.dropWhile (·.isWhitespace) |>.reverse.dropWhile (·.isWhitespace) |>.reverse)

/-- The identifier at the head of `cs`, and what follows it. The scan is over `List Char`: in
this toolchain `String.Pos` is indexed by its string and the raw byte offset moved to
`String.Pos.Raw`, so a character list is the portable spelling. -/
def readIdent (cs : List Char) : String × List Char :=
  (String.ofList (cs.takeWhile isIdentChar), cs.dropWhile isIdentChar)

/-- The span of a balanced `<…>` at the head of `cs` (whose first character must be `<`), as the
inner text and what follows the closing `>`; `none` when the line does not close it. Depth counts
`<`, `(` and `[` alike, so a parameter default of `readonly [A, B]` or `(_: A) => void` cannot
hide a comma or a bracket from the split. -/
def balancedAngle : List Char → Option (String × List Char)
  | '<' :: rest => go rest 1 []
  | _ => none
where
  go : List Char → Nat → List Char → Option (String × List Char)
    | [], _, _ => none
    -- `=>` is a function arrow, not a closing bracket: rc.112 spells its variance markers
    -- `Covariant<A> = (_: never) => A` (`Types.ts:672`), so a parameter default may carry one
    | '=' :: '>' :: rest, depth, acc => go rest depth ('>' :: '=' :: acc)
    | c :: rest, depth, acc =>
      if c == '<' || c == '(' || c == '[' then go rest (depth + 1) (c :: acc)
      else if c == ')' || c == ']' then go rest (depth - 1) (c :: acc)
      else if c == '>' then
        if depth == 1 then some (String.ofList acc.reverse, rest)
        else go rest (depth - 1) (c :: acc)
      else go rest depth (c :: acc)

/-- The parameter list split at top-level commas. -/
private def splitTop (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur := ""
  let mut depth : Nat := 0
  let mut prev : Char := ' '
  for c in s.toList do
    if c == '<' || c == '(' || c == '[' || c == '{' then
      depth := depth + 1
      cur := cur.push c
    else if c == '>' && prev == '=' then
      -- the function arrow of a default, not a bracket (see `balancedAngle`)
      cur := cur.push c
    else if c == '>' || c == ')' || c == ']' || c == '}' then
      depth := depth - 1
      cur := cur.push c
    else if c == ',' && depth == 0 then
      out := out ++ [cur]
      cur := ""
    else
      cur := cur.push c
    prev := c
  if trimS cur != "" || !out.isEmpty then
    out := out ++ [cur]
  return out

/-- One parameter: the leading `in`/`out` modifiers, then the name. `in`/`out` are reserved at
this position in TypeScript, so a parameter genuinely named `in` cannot occur and the read is
unambiguous; anything after the name (a constraint or a default) is not read. -/
def readParam (index : Nat) (raw : String) : Except String Param := Id.run do
  let words := ((trimS raw).splitOn " ").filter (· != "")
  let mut hasIn := false
  let mut hasOut := false
  let mut rest := words
  let mut go := true
  while go do
    match rest with
    | "in" :: more => hasIn := true; rest := more
    | "out" :: more => hasOut := true; rest := more
    | _ => go := false
  match rest with
  | [] => return .error s!"type parameter {index} has modifiers but no name: {trimS raw}"
  | w :: _ =>
    let (name, _) := readIdent w.toList
    if name == "" then
      return .error s!"type parameter {index} has no name: {trimS raw}"
    let modifiers :=
      match hasIn, hasOut with
      | true, true => "in out"
      | true, false => "in"
      | false, true => "out"
      | false, false => ""
    return .ok { index, name, modifiers, variance := Variance.ofModifiers hasIn hasOut }

/-- Every top-level `export interface`/`export type` of one file, with its parameters. A
declaration whose parameter list does not close on its own line is refused by name rather than
continued: rc.112 writes every one of them on one line, and a silent continuation would read the
next declaration's modifiers. -/
def readFile («module» : String) (text : String) : Except String (List Decl) := Id.run do
  let mut out : List Decl := []
  let mut lineNo : Nat := 0
  for line in text.splitOn "\n" do
    lineNo := lineNo + 1
    let line := line.replace "\r" ""
    let kind : Option Kind :=
      if line.startsWith "export interface " then some .«interface»
      else if line.startsWith "export type " then some .«alias»
      else Option.none
    let some kind := kind | continue
    let after : List Char :=
      line.toList.drop (if kind == .«interface» then "export interface ".length
                        else "export type ".length)
    let (name, afterName) := readIdent after
    if name == "" then
      return .error s!"{«module»}.ts:{lineNo}: export with no name: {line}"
    let (params, rhs) ←
      if afterName.head? == some '<' then
        match balancedAngle afterName with
        | Option.none =>
          return .error s!"{«module»}.ts:{lineNo}: type parameter list does not close on its \
            own line, which this reader refuses: {line}"
        | some (inner, afterAngle) =>
          let mut ps : List Param := []
          let mut i : Nat := 0
          for raw in splitTop inner do
            match readParam i raw with
            | .error e => return .error s!"{«module»}.ts:{lineNo}: {e}"
            | .ok p => ps := ps ++ [p]
            i := i + 1
          pure (ps, String.ofList afterAngle)
      else
        pure ([], String.ofList afterName)
    out := out ++ [{ «module», name, kind, line := lineNo, text := line, params, rhs }]
  return .ok out

/-! ## Inference for the two aliases -/

/-- One reference in an alias's right-hand side: a name and the arguments it was applied to.
`= Success<A, E> | Failure<A, E>` gives `[("Success", ["A","E"]), ("Failure", ["A","E"])]`, and
`= Fail<E> | Die | Interrupt` gives `[("Fail", ["E"]), ("Die", []), ("Interrupt", [])]`.
Everything before the first `=` is dropped, so a constraint in the parameter list cannot
contribute. -/
def references (rhs : String) : List (String × List String) := Id.run do
  let body := match rhs.splitOn "=" with
    | _ :: more => String.intercalate "=" more
    | [] => rhs
  let mut out : List (String × List String) := []
  let mut cs := body.toList
  while !cs.isEmpty do
    match cs with
    | [] => cs := []
    | c :: rest =>
      if isIdentChar c then
        let (w, after) := readIdent cs
        if c.isUpper then
          match balancedAngle after with
          | some (inner, afterAngle) =>
            out := out ++ [(w, (splitTop inner).map trimS)]
            cs := afterAngle
          | Option.none =>
            out := out ++ [(w, [])]
            cs := after
        else
          cs := after
      else
        cs := rest
  return out

/-- The alias's inferred variance per parameter, the way TypeScript computes it: a parameter is
constrained by exactly the positions its *name* is passed to in the right-hand side, and each
such position contributes the constituent's own declared variance. A constituent that does not
mention the parameter — `Die` in `Reason<E> = Fail<E> | Die | Interrupt` — contributes nothing,
and a parameter no constituent constrains reads `none`. Two positions that disagree are fatal:
the point of reading rc.112 is that nothing here is decided by this file.

This is deliberately weaker than TypeScript's own `getVariancesWorker`, which probes marker types
through the structure; it agrees on a union of applied interfaces, which is what `Exit` and
`Option` are, and the red controls pin exactly those two. -/
def inferAlias (d : Decl) (decls : List Decl) : Except String (List Decl × List Param) := Id.run do
  let refs := references d.rhs
  let mut parts : List Decl := []
  for (n, _) in refs do
    match decls.find? (fun e => e.name == n && e.kind == .«interface») with
    | some e => if !parts.any (·.name == e.name) then parts := parts ++ [e]
    | Option.none => continue
  let mut ps : List Param := []
  let mut i : Nat := 0
  for p in d.params do
    let mut v : Option Variance := Option.none
    for (n, args) in refs do
      let some e := decls.find? (fun e => e.name == n && e.kind == .«interface») | continue
      let mut j : Nat := 0
      for arg in args do
        if arg == p.name then
          match e.params[j]? with
          | Option.none =>
            return .error s!"{e.cite}: {e.name} is applied to {args.length} arguments but \
              declares {e.params.length}"
          | some q =>
            match v with
            | Option.none => v := some q.variance
            | some w =>
              if w != q.variance then
                return .error s!"{d.cite}: {d.name}'s parameter {p.name} is passed at two \
                  positions of different variance: {w.text} and {q.variance.text}"
        j := j + 1
    ps := ps ++ [{ index := i, name := p.name, modifiers := "",
                   variance := v.getD .none }]
    i := i + 1
  return .ok (parts, ps)

/-! ## The head map -/

/-- A `Ty` head, the declaration it spells, and where that declaration comes from. `rc112` names
a module and an exported name this driver reads; `printer` names a TypeScript form with no
vendored interface, with the variance the printed spelling has and the note that says so. -/
inductive Source where
  | rc112 («module» : String) (name : String)
  | printer (spelling : String) (variance : List Variance) (note : String)

/-- The one hand list: every parametrised `Ty` constructor and what it spells. A head with no
entry is refused (`headRows`), so a new parametrised constructor must be given its declaration
here before `TyView` can be generated. -/
def heads : List (String × Source) :=
  [ ("option", .rc112 "Option" "Option"),
    ("list", .printer "ReadonlyArray<A>" [.co]
      "TypeScript's own; `Ty.renderRaw` prints `ReadonlyArray<…>` \
       (src/Effect4/Program/Ty.lean:91). `ReadonlyArray<T>` is covariant in T."),
    ("prod", .printer "readonly [A, B]" [.co, .co]
      "TypeScript's own; `Ty.renderRaw` prints `readonly [A, B]` \
       (src/Effect4/Program/Ty.lean:92). A readonly tuple is covariant in each element."),
    ("except", .printer "Result.Result<A, E>" [.co, .co]
      "The printer's spelling: `Ty.except error value` prints `Result.Result<value, error>` \
       (src/Effect4/Program/Ty.lean:93). `Ty.sub`'s arm compares the arguments positionally in \
       the constructor's own order, error first."),
    ("exitOf", .rc112 "Exit" "Exit"),
    ("causeOf", .rc112 "Cause" "Cause"),
    ("fiberOf", .rc112 "Fiber" "Fiber"),
    ("union", .printer "A | B" [.co, .co]
      "TypeScript's own union. Not a congruence for `Ty.sub`: the order treats a union by \
       distribution on the left and choice on the right, so `Ty.sameHead` answers `false` on it \
       and the arm never reaches the variance-wise comparison."),
    ("refOf", .rc112 "Ref" "Ref"),
    ("deferredOf", .rc112 "Deferred" "Deferred") ]

/-! ## The red controls -/

/-- What a correct read must say, checked on every run. A reader that dropped the `in` keyword,
or read the modifiers of the wrong parameter, fails one of these. -/
def redControls : List (String × String × List Variance) :=
  [ ("Ref", "Ref", [.inv]),
    ("Fiber", "Fiber", [.co, .co]),
    ("Layer", "Layer", [.contra, .co, .co]),
    ("Context", "Context", [.contra]),
    ("Deferred", "Deferred", [.inv, .inv]),
    ("Cause", "Cause", [.co]),
    ("Effect", "Effect", [.co, .co, .co]),
    ("Queue", "Queue", [.inv, .inv]),
    ("PubSub", "PubSub", [.inv]),
    -- the two aliases: the values below are what the *inference* must produce from
    -- `Success`/`Failure` and `None`/`Some`, so a broken inference fails here and not silently
    ("Exit", "Exit", [.co, .co]),
    ("Option", "Option", [.co]) ]

/-! ## The JSON -/

def digestOf (s : String) : String := (Effect4.Store.sha256 s.toUTF8.data.toList).hex

def paramJson (p : Param) : Json :=
  Json.mkObj [("index", Json.num p.index), ("name", Json.str p.name),
    ("modifiers", Json.str p.modifiers), ("variance", Json.str p.variance.text)]

def declJson (d : Decl) (params : List Param) (constituents : List Json) : Json :=
  let base : List (String × Json) :=
    [("module", Json.str d.«module»), ("name", Json.str d.name),
     ("kind", Json.str d.kind.text), ("cite", Json.str d.cite),
     ("sha256", Json.str (digestOf d.text)),
     ("hasVariance", Json.bool d.hasVariance),
     ("declaration", Json.str (trimS d.text)),
     ("parameters", Json.arr (params.map paramJson).toArray)]
  Json.mkObj (if constituents.isEmpty then base
    else base ++ [("constituents", Json.arr constituents.toArray)])

/-! ## The driver -/

structure Read where
  decls : List Decl
  /-- Per declaration: the parameters as resolved (inference applied for an alias). -/
  resolved : List (Decl × List Param × List Decl)

def variancesOf (r : Read) («module» name : String) : Option (List Variance) :=
  (r.resolved.find? fun (d, _, _) => d.«module» == «module» && d.name == name).map
    fun (_, ps, _) => ps.map (·.variance)

def citeOf (r : Read) («module» name : String) : Option String :=
  (r.resolved.find? fun (d, _, _) => d.«module» == «module» && d.name == name).map
    fun (d, _, _) => d.cite

def kindOf (r : Read) («module» name : String) : Option Kind :=
  (r.resolved.find? fun (d, _, _) => d.«module» == «module» && d.name == name).map
    fun (d, _, _) => d.kind

def constituentsOf (r : Read) («module» name : String) : List Decl :=
  ((r.resolved.find? fun (d, _, _) => d.«module» == «module» && d.name == name).map
    fun (_, _, parts) => parts).getD []

def headJson (r : Read) : Except String (List Json) := Id.run do
  let mut out : List Json := []
  for (head, src) in heads do
    match src with
    | .rc112 m n =>
      let some vs := variancesOf r m n
        | return .error s!"head {head} names {m}.{n}, which is not an exported declaration of \
            {root}/{m}.ts"
      let some cite := citeOf r m n | return .error s!"head {head}: no cite for {m}.{n}"
      let some kind := kindOf r m n | return .error s!"head {head}: no kind for {m}.{n}"
      out := out ++ [Json.mkObj
        ([("head", Json.str head), ("source", Json.str "rc112"),
          ("module", Json.str m), ("declaration", Json.str n),
          ("kind", Json.str kind.text),
          ("cite", Json.str cite),
          ("variance", Json.arr (vs.map (fun v => Json.str v.text)).toArray)] ++
         (if kind == .«alias» then
            [("inferredFrom", Json.arr (constituentsOf r m n |>.map
              (fun e => Json.str e.cite)).toArray)]
          else []))]
    | .printer spelling vs note =>
      out := out ++ [Json.mkObj
        [("head", Json.str head), ("source", Json.str "printer"),
         ("spelling", Json.str spelling), ("note", Json.str note),
         ("variance", Json.arr (vs.map (fun v => Json.str v.text)).toArray)]]
  return .ok out

def read (readModule : String → IO String) : IO Read := do
  let mut decls : List Decl := []
  for m in modules do
    let text ← readModule m
    match readFile m text with
    | .error e => throw (IO.userError s!"variances: {e}")
    | .ok ds => decls := decls ++ ds
  let mut resolved : List (Decl × List Param × List Decl) := []
  for d in decls do
    match d.kind with
    | .«interface» => resolved := resolved ++ [(d, d.params, [])]
    | .«alias» =>
      if d.params.isEmpty then
        resolved := resolved ++ [(d, [], [])]
      else
        match inferAlias d decls with
        | .error e => throw (IO.userError s!"variances: {e}")
        | .ok (parts, ps) => resolved := resolved ++ [(d, ps, parts)]
  return { decls, resolved }

/-- The alias's constituent rows carry their own declared variance, so the json records what the
inference was made from and not only its answer. -/
def constituentJson (parts : List Decl) : List Json :=
  parts.map fun e => Json.mkObj
    [("name", Json.str e.name), ("cite", Json.str e.cite),
     ("sha256", Json.str (digestOf e.text)),
     ("declaration", Json.str (trimS e.text)),
     ("parameters", Json.arr (e.params.map paramJson).toArray)]

/-! ## The reader's own hermetic controls

Planted declaration lines, so the scanner is checked without the vendored tree: they run at
`lake build Tools.Variances`, which `python3 scripts/generate.py --only variances` does before
every regeneration. The mutated lines are the point — a reader that dropped the `in` keyword, or
that split a parameter list inside a bracket, answers differently on them. The controls against
rc.112 itself are `redControls`, checked on every run of the driver. -/

private def varianceTexts (m text : String) (name : String) : List String :=
  match readFile m text with
  | .error _ => ["ERROR"]
  | .ok ds => match ds.find? (·.name == name) with
    | some d => d.params.map (·.variance.text)
    | none => ["MISSING"]

-- the declaration as rc.112 writes it, and the three mutations that must read differently
#guard varianceTexts "Ref" "export interface Ref<in out A> extends Ref.Variance<A>, Pipeable {"
  "Ref" == ["inv"]
#guard varianceTexts "Ref" "export interface Ref<out A> extends Ref.Variance<A>, Pipeable {"
  "Ref" == ["co"]
#guard varianceTexts "Ref" "export interface Ref<in A> extends Ref.Variance<A>, Pipeable {"
  "Ref" == ["contra"]
#guard varianceTexts "Ref" "export interface Ref<A> extends Ref.Variance<A>, Pipeable {"
  "Ref" == ["none"]

-- the modifiers belong to their own parameter and not to the list
#guard varianceTexts "Layer"
  "export interface Layer<in ROut, out E = never, out RIn = never> extends Variance<ROut, E, RIn> {"
  "Layer" == ["contra", "co", "co"]
#guard varianceTexts "Fiber" "export interface Fiber<out A, out E = never> extends Pipeable {"
  "Fiber" == ["co", "co"]

-- a default containing a comma inside brackets is one parameter, not two
#guard varianceTexts "X" "export interface X<out A = readonly [1, 2], in B> extends Y {"
  "X" == ["co", "contra"]
#guard varianceTexts "X" "export interface X<out A = (_: never) => void, in out B> {"
  "X" == ["co", "inv"]

-- an indented declaration is not top-level and is not read (`Exit.ts:86`'s `Proto`)
#guard varianceTexts "Exit" "  export interface Proto<out A, out E = never> extends Effect<A, E> {"
  "Proto" == ["MISSING"]

-- the argument-directed alias inference, and the constituent that constrains nothing
#guard (inferAlias
    { «module» := "X", name := "Exit", kind := .«alias», line := 1,
      text := "", rhs := "<A, E = never> = Success<A, E> | Failure<A, E>",
      params := [⟨0, "A", "", .none⟩, ⟨1, "E", "", .none⟩] }
    [{ «module» := "X", name := "Success", kind := .«interface», line := 2, text := "", rhs := "",
       params := [⟨0, "A", "out", .co⟩, ⟨1, "E", "out", .co⟩] },
     { «module» := "X", name := "Failure", kind := .«interface», line := 3, text := "", rhs := "",
       params := [⟨0, "A", "out", .co⟩, ⟨1, "E", "out", .co⟩] }]
  |>.toOption.map (fun (_, ps) => ps.map (·.variance.text))) == some ["co", "co"]
#guard (inferAlias
    { «module» := "X", name := "Reason", kind := .«alias», line := 1,
      text := "", rhs := "<E> = Fail<E> | Die | Interrupt",
      params := [⟨0, "E", "", .none⟩] }
    [{ «module» := "X", name := "Fail", kind := .«interface», line := 2, text := "", rhs := "",
       params := [⟨0, "E", "out", .co⟩] },
     { «module» := "X", name := "Die", kind := .«interface», line := 3, text := "", rhs := "",
       params := [] }]
  |>.toOption.map (fun (_, ps) => ps.map (·.variance.text))) == some ["co"]
-- a parameter no constituent passes is unconstrained, not guessed
#guard (inferAlias
    { «module» := "X", name := "Opaque", kind := .«alias», line := 1,
      text := "", rhs := "<A> = string", params := [⟨0, "A", "", .none⟩] } []
  |>.toOption.map (fun (_, ps) => ps.map (·.variance.text))) == some ["none"]

def checkRedControls (r : Read) : IO Unit := do
  for (m, n, expected) in redControls do
    let some vs := variancesOf r m n
      | throw (IO.userError s!"variances: red control {m}.{n} is not an exported declaration")
    unless vs.map (·.text) == expected.map (·.text) do
      throw (IO.userError s!"variances: red control {m}.{n} reads \
        [{String.intercalate ", " (vs.map (·.text))}] but rc.112 declares \
        [{String.intercalate ", " (expected.map (·.text))}]")
    IO.println s!"  control {m}.{n} = [{String.intercalate ", " (vs.map (·.text))}]"

end Tools.Variances

open Tools.Variances in
def main (argv : List String) : IO Unit := do
  let out := argv.head?.getD defaultOut
  let r ← read fun m => IO.FS.readFile ⟨s!"{root}/{m}.ts"⟩
  checkRedControls r
  -- the head map's own variance, resolved, so a head that names a missing declaration is fatal
  let headRows ← match headJson r with
    | .error e => throw (IO.userError s!"variances: {e}")
    | .ok rows => pure rows
  -- An alias's parameters carry `modifiers: "inferred"` (rc.112 wrote no modifier there) and
  -- the variance the inference computed, with the constituent declarations it was computed
  -- from beside them, so the row records the evidence and not only the answer.
  let declRows := r.resolved.map fun (d, ps, parts) =>
    declJson d (if d.kind == .«interface» then ps
                else ps.map fun p => { p with modifiers := "inferred" })
      (constituentJson parts)
  let withVariance := r.decls.filter (·.hasVariance)
  let doc := Json.mkObj
    [("format", Json.str "effect4-variances-v1"),
     ("comment", Json.arr #[
       Json.str "GENERATED by tools/Tools/Variances.lean from the vendored Effect sources.",
       Json.str "Regenerate: python3 scripts/generate.py --only variances",
       Json.str ("Declaration-site variance as rc.112 spells it (decisions row 55). " ++
         "`variance` is co for `out`, contra for `in`, inv for `in out`, none for a " ++
         "parameter with no modifier, and inferred for a type alias of a union, whose " ++
         "constituents' declarations are carried beside it."),
       Json.str ("`heads` is what the TyView generator reads: one row per parametrised " ++
         "`Ty` constructor. `source: rc112` names a vendored declaration; `source: printer` " ++
         "names a TypeScript form with no interface of its own, whose variance is the " ++
         "printed spelling's and whose note says which.")]),
     ("pin", Json.mkObj
       [("version", Json.str version), ("root", Json.str root),
        ("modules", Json.arr (modules.map Json.str).toArray)]),
     ("counts", Json.mkObj
       [("declarations", Json.num r.decls.length),
        ("withVariance", Json.num withVariance.length)]),
     ("heads", Json.arr headRows.toArray),
     ("declarations", Json.arr declRows.toArray)]
  IO.FS.writeFile ⟨out⟩ (doc.pretty 100 ++ "\n")
  IO.println s!"variances: {r.decls.length} declarations \
    ({withVariance.length} declaring in/out) from {modules.length} modules -> {out}"
