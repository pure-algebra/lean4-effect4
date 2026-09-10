import Lean
import Conform.Core.Report

/-!
# Conform.Lcnf.Validity — rung 1 of the verification ladder: validity and provenance

**What it is.** Three generic things over `Lean.Compiler.LCNF`, none of which names a
declaration of this repository:

1. a **census** of the constructs a mono-phase `Decl .pure` actually uses — one counter per
   constructor of `Code`, `LetValue`, `LitValue`, `Arg`, `Alt` and `DeclValue` in the pure
   fragment, so a translator's rule table can be compared with the surface it must cover;
2. an **availability** verdict for a constant's mono body, which distinguishes the four
   things `getMonoDecl?` can mean (a body, the module-system's opacity filter, a real
   `@[extern]`, and nothing at all) — `PhaseExt.lean:96-104` replaces the body of a
   public-but-not-transparent declaration with `.extern { entries := [.opaque] }`, and a
   consumer that reads that as "an extern" is reading a *visibility* fact as a *language*
   fact;
3. the compiler's own structural checker, `Decl.check`, run on a decl read back out of
   `monoExt`, plus a **manifest** of everything a generator saw.

**Depends on.** `Lean` and `Conform.Core.Report`. Nothing from this repository; the roots,
the constants a caller treats as primitive, and the closure cap all arrive as arguments.

**Properties.**
* The census names every constructor of the pure fragment, and `Census.constructs` is the
  fixed 26-element list in a fixed order, so two runs over the same closure produce the same
  bytes — *by construction*.
* `checkDecl` never modifies the environment or the fresh-name counter: it runs under
  `runCompilerWithoutModifyingState` — *by construction* (the same door `ppDecl'` uses).
* `checkDecl` is a *refusal*, not an absence: it answers `Except String Unit`, and a
  declaration whose mono body is missing is not checked at all but is recorded as an
  availability row — the two are never mixed (`brief-common.md`, "absence, refusal and
  frontier are three things").
* A closure walk stops at three places and says which: a caller-declared primitive
  (`Walk.Config.primitive`), a constant with no mono code (`missing`), and the cap
  (`frontier`) — *by construction*.
-/

namespace Conform.Lcnf

open Lean Compiler LCNF

/-! ## 1. The construct census -/

/-- The constructor names of the mono/pure fragment, in a fixed order. This is the whole
surface a translator over `Decl .pure` must cover: 7 `Code`, 5 `LetValue`, 7 `LitValue`,
3 `Arg`, 2 `Alt`, 2 `DeclValue`. The impure constructors (`oset`, `uset`, `sset`, `setTag`,
`inc`, `dec`, `del`, `ctor`, `oproj`, `uproj`, `sproj`, `fap`, `pap`, `reset`, `reuse`,
`box`, `unbox`, `isShared`, `Alt.ctorAlt`) carry `h : pu = .impure` and cannot inhabit this
fragment — `Basic.lean:359-385`. -/
def constructs : List String :=
  [ "Code.let", "Code.fun", "Code.jp", "Code.jmp", "Code.cases", "Code.return", "Code.unreach"
  , "LetValue.lit", "LetValue.erased", "LetValue.proj", "LetValue.const", "LetValue.fvar"
  , "LitValue.nat", "LitValue.str", "LitValue.uint8", "LitValue.uint16", "LitValue.uint32"
  , "LitValue.uint64", "LitValue.usize"
  , "Arg.erased", "Arg.fvar", "Arg.type"
  , "Alt.alt", "Alt.default"
  , "DeclValue.code", "DeclValue.extern" ]

/-- One walk's counts: constructor name to occurrences, plus the incidental facts a rule
table is judged against. -/
structure Census where
  counts : Std.HashMap String Nat := {}
  /-- `cases` scrutinee type constants, with how many `cases` nodes each had. -/
  casesTypes : Std.HashMap Name Nat := {}
  /-- Constructor names appearing in `Alt.alt` patterns. -/
  altCtors : Std.HashMap Name Nat := {}
  /-- Constant heads of `LetValue.const`. -/
  constHeads : Std.HashMap Name Nat := {}
  /-- Type constants of `LetValue.proj`. -/
  projTypes : Std.HashMap Name Nat := {}
  /-- The largest number of parameters of a join point / local function seen. -/
  maxFunArity : Nat := 0
  /-- Join points with no parameters (`jmp j` with no arguments — the OCaml rule spells the
  call `j ()`). -/
  nullaryFuns : Nat := 0
  /-- The largest `LitValue.nat` in the closure. A target whose integers are narrower than
  Lean's `Nat` needs this number to know whether its literal rule is ever exercised. -/
  maxNatLit : Nat := 0
  /-- `LitValue.nat`s at or above 2^62, which OCaml's 63-bit `int` cannot hold. -/
  bigNatLits : Nat := 0
  /-- `LitValue.str`s containing a code point above U+007F: the ones for which "a Lean
  string is scalar values, an OCaml string is bytes" is observable. -/
  nonAsciiStrLits : Nat := 0
  deriving Inhabited

namespace Census

def bump (c : Census) (k : String) : Census :=
  { c with counts := c.counts.insert k (c.counts.getD k 0 + 1) }

private def bumpName (m : Std.HashMap Name Nat) (n : Name) : Std.HashMap Name Nat :=
  m.insert n (m.getD n 0 + 1)

def get (c : Census) (k : String) : Nat := c.counts.getD k 0

/-- The union of two censuses. -/
def merge (a b : Census) : Census :=
  { counts := b.counts.fold (init := a.counts) fun m k v => m.insert k (m.getD k 0 + v)
    casesTypes := b.casesTypes.fold (init := a.casesTypes) fun m k v => m.insert k (m.getD k 0 + v)
    altCtors := b.altCtors.fold (init := a.altCtors) fun m k v => m.insert k (m.getD k 0 + v)
    constHeads := b.constHeads.fold (init := a.constHeads) fun m k v => m.insert k (m.getD k 0 + v)
    projTypes := b.projTypes.fold (init := a.projTypes) fun m k v => m.insert k (m.getD k 0 + v)
    maxFunArity := max a.maxFunArity b.maxFunArity
    nullaryFuns := a.nullaryFuns + b.nullaryFuns
    maxNatLit := max a.maxNatLit b.maxNatLit
    bigNatLits := a.bigNatLits + b.bigNatLits
    nonAsciiStrLits := a.nonAsciiStrLits + b.nonAsciiStrLits }

/-- The first `Nat` OCaml's `int` cannot hold: `2^62`. -/
def ocamlIntBound : Nat := 4611686018427387904

def ofLit (c : Census) : LitValue → Census
  | .nat n =>
    let c := c.bump "LitValue.nat"
    { c with maxNatLit := max c.maxNatLit n,
             bigNatLits := c.bigNatLits + (if n ≥ ocamlIntBound then 1 else 0) }
  | .str s =>
    let c := c.bump "LitValue.str"
    { c with nonAsciiStrLits :=
        c.nonAsciiStrLits + (if s.toList.any (fun ch => ch.toNat > 127) then 1 else 0) }
  | .uint8 _ => c.bump "LitValue.uint8"
  | .uint16 _ => c.bump "LitValue.uint16"
  | .uint32 _ => c.bump "LitValue.uint32"
  | .uint64 _ => c.bump "LitValue.uint64"
  | .usize _ => c.bump "LitValue.usize"

def ofArg (c : Census) : Arg .pure → Census
  | .erased => c.bump "Arg.erased"
  | .fvar _ => c.bump "Arg.fvar"
  | .type _ => c.bump "Arg.type"

def ofArgs (c : Census) (as : Array (Arg .pure)) : Census :=
  as.foldl (init := c) ofArg

def ofLetValue (c : Census) : LetValue .pure → Census
  | .lit l => (c.bump "LetValue.lit").ofLit l
  | .erased => c.bump "LetValue.erased"
  | .proj t _ _ =>
    let c := c.bump "LetValue.proj"
    { c with projTypes := bumpName c.projTypes t }
  | .const n _ args =>
    let c := c.bump "LetValue.const"
    let c := { c with constHeads := bumpName c.constHeads n }
    c.ofArgs args
  | .fvar _ args => (c.bump "LetValue.fvar").ofArgs args

mutual

/-- The census of one `Code .pure`, by fuel on the tree's depth-in-nodes. `Code` is a nested
inductive with an `Array (Alt .pure)`; a structural recursion would need a well-founded
measure over the array, so the walk is `partial` — it is a *counter*, not a semantics, and
its termination is the tree's finiteness. -/
partial def ofCode (c : Census) : Code .pure → Census
  | .let decl k => (c.bump "Code.let").ofLetValue decl.value |>.ofCode k
  | .fun decl k =>
    let c := c.bump "Code.fun"
    let c := { c with maxFunArity := max c.maxFunArity decl.params.size,
                      nullaryFuns := c.nullaryFuns + (if decl.params.isEmpty then 1 else 0) }
    (c.ofCode decl.value).ofCode k
  | .jp decl k =>
    let c := c.bump "Code.jp"
    let c := { c with maxFunArity := max c.maxFunArity decl.params.size,
                      nullaryFuns := c.nullaryFuns + (if decl.params.isEmpty then 1 else 0) }
    (c.ofCode decl.value).ofCode k
  | .jmp _ args => (c.bump "Code.jmp").ofArgs args
  | .return _ => c.bump "Code.return"
  | .unreach _ => c.bump "Code.unreach"
  | .cases cs =>
    let c := c.bump "Code.cases"
    let c := { c with casesTypes := bumpName c.casesTypes cs.typeName }
    cs.alts.foldl (init := c) ofAlt

partial def ofAlt (c : Census) : Alt .pure → Census
  | .default k => (c.bump "Alt.default").ofCode k
  | .alt ctor _ k =>
    let c := c.bump "Alt.alt"
    let c := { c with altCtors := bumpName c.altCtors ctor }
    c.ofCode k

end

/-- The census of one declaration, its body and its parameter list. -/
def ofDecl (c : Census) (d : Decl .pure) : Census :=
  match d.value with
  | .code code => (c.bump "DeclValue.code").ofCode code
  | .extern _ => c.bump "DeclValue.extern"

/-- The census as JSON: every construct in `constructs` order, zeros included, so a reader
can see what did *not* occur. -/
def toJson (c : Census) : Json :=
  Json.mkObj (constructs.map (fun k => (k, Json.num (c.get k)))
    ++ [ ("maxFunArity", Json.num c.maxFunArity)
       , ("nullaryFuns", Json.num c.nullaryFuns)
       , ("maxNatLit", Json.str (toString c.maxNatLit))
       , ("bigNatLits", Json.num c.bigNatLits)
       , ("nonAsciiStrLits", Json.num c.nonAsciiStrLits) ])

private def nameCounts (m : Std.HashMap Name Nat) : List (Name × Nat) :=
  (m.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)).toList

def casesTypesList (c : Census) : List (Name × Nat) := nameCounts c.casesTypes
def altCtorsList (c : Census) : List (Name × Nat) := nameCounts c.altCtors
def constHeadsList (c : Census) : List (Name × Nat) := nameCounts c.constHeads
def projTypesList (c : Census) : List (Name × Nat) := nameCounts c.projTypes

end Census

/-! ## 2. Availability -/

/-- What `getMonoDecl?` gave back, with the module system's filter told apart from a real
`@[extern]`. -/
inductive Availability
  /-- A `.code` body: the phase's own text. -/
  | code
  /-- `.extern { entries := [.opaque] }`, which `PhaseExt.exportEntriesFnEx` writes for a
  declaration that is public but not transparent in a `module` file. It is a *visibility*
  verdict, not a language one; the body exists, it was not exported. -/
  | opaqueByVisibility
  /-- A genuine `@[extern]`/`@[implemented_by]` declaration: entries naming a backend. -/
  | extern (entries : Nat)
  /-- No entry in `monoExt` at all: an inductive, a constructor, a `Prop`, a
  `noncomputable`, or a declaration whose module never persisted the phase. -/
  | absent
  deriving Inhabited, DecidableEq

namespace Availability

protected def toString : Availability → String
  | .code => "code"
  | .opaqueByVisibility => "opaque-by-visibility"
  | .extern _ => "extern"
  | .absent => "absent"

instance : ToString Availability := ⟨Availability.toString⟩

/-- Whether a translator can read a body here. -/
def hasCode : Availability → Bool
  | .code => true
  | _ => false

end Availability

/-- The availability of `n`'s mono body in `env`, and the decl when there is one. Pure: it
reads `monoExt` through `getDeclCore?`, exactly as `Translate.wrapperKeep?` does. -/
def monoAvailability (env : Environment) (n : Name) : Availability × Option (Decl .pure) :=
  match getDeclCore? env monoExt n with
  | none => (.absent, none)
  | some d =>
    match d.value with
    | .code _ => (.code, some d)
    | .extern data =>
      if data.entries == [ExternEntry.opaque] then (.opaqueByVisibility, some d)
      else (.extern data.entries.length, some d)

/-! ## 3. The compiler's own checker -/

/-- Run `Lean.Compiler.LCNF.Decl.check` on a decl read out of `monoExt`. The decl must be
internalized first — `Check.Pure.checkParam` compares each parameter with the one in the
local context, and a decl straight out of the extension has none — which is what `ppDecl'`
does too (`PrettyPrinter.lean:218-220`). Neither the environment nor the fresh-name counter
is modified.

`checkTypes` turns on the compiler's type-compatibility pass as well as the structural one.
It is off by default and its own docstring says it "fails in code that makes heavy use of
dependent types" (`ConfigOptions.lean:68-71`), so a caller that turns it on must read a
failure as a *report about the checker*, not only about the code. -/
def checkDecl (d : Decl .pure) (checkTypes : Bool := false) : CoreM (Except String Unit) := do
  let act : CoreM (Except String Unit) :=
    runCompilerWithoutModifyingState .mono do
      try
        let d ← d.internalize
        d.check
        return .ok ()
      catch e =>
        return .error (← e.toMessageData.toString)
  if checkTypes then
    withOptions (fun o => o.setBool `compiler.checkTypes true) act
  else
    act

/-! ## 4. The closure walk -/

/-- What a walk treats as an endpoint. Everything here is data supplied by the caller: the
generic code never knows a family name. -/
structure Walk.Config where
  /-- Constants the caller implements itself (a builtin table, an extern ledger): the walk
  records them and does not descend. -/
  primitive : Name → Bool := fun _ => false
  /-- The largest number of declarations to translate; beyond it, a name is `frontier`. -/
  cap : Nat := 4096
  /-- Follow `f` when a walk meets `f._redArg`, and vice versa, as `Translate` does. -/
  foldRedArg : Bool := true

/-- The `reduceArity` twin's suffix. -/
def redArgSuffix : Name := `_redArg

/-- `f` for `f._redArg`, `n` otherwise. -/
def stripRedArg (n : Name) : Name :=
  match n with
  | .str p "_redArg" => p
  | _ => n

/-- The constant heads a `Code .pure` calls, in first-occurrence order. -/
partial def calledConstants (code : Code .pure) : Array Name :=
  go code #[]
where
  push (acc : Array Name) (n : Name) : Array Name := if acc.contains n then acc else acc.push n
  goLet (v : LetValue .pure) (acc : Array Name) : Array Name :=
    match v with
    | .const n _ _ => push acc n
    | _ => acc
  go (c : Code .pure) (acc : Array Name) : Array Name :=
    match c with
    | .let decl k => go k (goLet decl.value acc)
    | .fun decl k | .jp decl k => go k (go decl.value acc)
    | .jmp _ _ | .return _ | .unreach _ => acc
    | .cases cs => cs.alts.foldl (init := acc) fun acc alt =>
        match alt with
        | .default k => go k acc
        | .alt _ _ k => go k acc

/-- One declaration of a closure, as the manifest records it. -/
structure DeclFacts where
  name : Name
  /-- The name a caller asked for, when the walk followed a `_redArg` fold. -/
  requestedAs : Name
  availability : Availability
  /-- `Lean.Compiler.LCNF.DeclHash`'s hash of the whole `Decl`, as a hex string: the identity
  of the *code*, insensitive to nothing (binder names and fvar ids are part of it, and
  `saveMono` normalises fvar ids, so it is stable across runs of one build). -/
  declHash : String
  arity : Nat
  /-- Parameters whose LCNF type is erased (`◾`): the ones a target drops or fills with a
  unit. -/
  erasedParams : Nat
  size : Nat
  recursive : Bool
  safe : Bool
  inlineAttr : Bool
  /-- `.ok` when the compiler's own `Decl.check` accepted the body. -/
  valid : Except String Unit
  census : Census
  callees : Array Name
  /-- The module the constant came from, `none` when it is local to this environment. -/
  module : Option Name
  /-- Whether that module participates in the **module system** (`ModuleData.isModule`).
  This is the switch that decides whether `monoExt`'s export filter applies at all:
  `isDeclPublic`/`isDeclTransparent` return `true` unconditionally for a non-module file
  (`PublicDeclsExt.lean:35-36`, `PhaseExt.lean:42-43`), so a non-module module exports every
  mono body and a module module exports only the public transparent ones. -/
  moduleIsModule : Bool

instance : Inhabited DeclFacts :=
  ⟨{ name := .anonymous, requestedAs := .anonymous, availability := .absent, declHash := ""
   , arity := 0, erasedParams := 0, size := 0, recursive := false, safe := true
   , inlineAttr := false, valid := .ok (), census := {}, callees := #[], module := none
   , moduleIsModule := false }⟩

/-- A callee whose mono body could not be read, with everything that says why. -/
structure MissingFacts where
  name : Name
  availability : Availability
  module : Option Name
  moduleIsModule : Bool
  /-- Whether the environment knows the constant at all, and as what. -/
  constKind : String
  deriving Inhabited

/-- What a walk produced. Absence (`missing`), refusal (`invalid`) and frontier
(`frontier`) are three separate fields. -/
structure Closure where
  decls : Array DeclFacts := #[]
  /-- Reached, declared primitive by the caller, never opened. -/
  primitives : Array Name := #[]
  /-- Reached and `getMonoDecl?` gave no code: with the availability that says why. -/
  missing : Array MissingFacts := #[]
  /-- Reached past the cap. -/
  frontier : Array Name := #[]
  /-- Constructor constants reached as call heads (a construction, not a call). -/
  ctors : Array Name := #[]
  deriving Inhabited

namespace Closure

def census (c : Closure) : Census :=
  c.decls.foldl (init := {}) fun acc d => acc.merge d.census

def invalid (c : Closure) : Array DeclFacts :=
  c.decls.filter fun d => d.valid matches .error _

end Closure

private def pushNew (a : Array Name) (n : Name) : Array Name :=
  if a.contains n then a else a.push n

/-- Walk the mono closure of `roots`. Generic: `cfg.primitive` is the caller's table.

The walk mirrors `OCaml5.Lcnf.translateClosure`'s traversal so that the manifest describes
*that* closure and not a different one: constructors are not opened, primitives are not
opened, `f._redArg` and `f` are one node, and the cap makes a frontier rather than an
error. -/
def walkClosure (roots : Array Name) (cfg : Walk.Config := {}) (checkTypes : Bool := false) :
    CoreM Closure := do
  let env ← getEnv
  let mut c : Closure := {}
  let mut done : NameSet := {}
  let mut queue : Array Name := roots
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    if done.contains n then continue
    if cfg.primitive n then
      c := { c with primitives := pushNew c.primitives n }
      done := done.insert n
      continue
    if env.find? n matches some (.ctorInfo _) then
      c := { c with ctors := pushNew c.ctors n }
      done := done.insert n
      continue
    if c.decls.size ≥ cfg.cap then
      c := { c with frontier := pushNew c.frontier n }
      continue
    done := done.insert n
    let (avail, d?) := monoAvailability env n
    -- the `reduceArity` fold: a wrapper's twin is the declaration that carries the code
    let mut requested := n
    let mut avail := avail
    let mut d? := d?
    if cfg.foldRedArg then
      if let some d := d? then
        if let some twin := redArgTarget? d then
          let (a2, d2) := monoAvailability env twin
          if a2.hasCode then
            done := done.insert twin
            requested := n
            avail := a2
            d? := d2
      let stripped := stripRedArg n
      if stripped != n then done := done.insert stripped
    let missingFacts : MissingFacts :=
      { name := n, availability := avail
        module := (env.getModuleIdxFor? n).bind fun idx => env.header.moduleNames[idx]?
        moduleIsModule :=
          match env.getModuleIdxFor? n with
          | none => env.header.isModule
          | some idx => env.header.moduleData[idx]?.any (·.isModule)
        constKind :=
          match env.find? n with
          | none => "unknown"
          | some (.defnInfo _) => "def"
          | some (.thmInfo _) => "theorem"
          | some (.axiomInfo _) => "axiom"
          | some (.opaqueInfo _) => "opaque"
          | some (.inductInfo _) => "inductive"
          | some (.ctorInfo _) => "constructor"
          | some (.recInfo _) => "recursor"
          | some (.quotInfo _) => "quot" }
    match d? with
    | none => c := { c with missing := c.missing.push missingFacts }
    | some d =>
      unless avail.hasCode do
        c := { c with missing := c.missing.push missingFacts }
        continue
      let code := match d.value with | .code k => some k | .extern _ => none
      let callees := match code with | some k => calledConstants k | none => #[]
      let valid ← checkDecl d checkTypes
      let facts : DeclFacts :=
        { name := d.name, requestedAs := requested, availability := avail
          declHash := (toString (hash d)),
          arity := d.params.size
          erasedParams := d.params.foldl (init := 0) fun k p => k + (if p.type.isErased then 1 else 0)
          size := d.size, recursive := d.recursive, safe := d.safe
          inlineAttr := d.inlineAttr
          valid := valid
          census := Census.ofDecl {} d
          callees := callees
          module := (env.getModuleIdxFor? d.name).bind fun idx => env.header.moduleNames[idx]?
          moduleIsModule :=
            match env.getModuleIdxFor? d.name with
            | none => env.header.isModule
            | some idx => env.header.moduleData[idx]?.any (·.isModule) }
      c := { c with decls := c.decls.push facts }
      for callee in callees do
        unless done.contains callee do queue := queue.push callee
  return c
where
  /-- The `reduceArity` wrapper shape: `let _x := f._redArg …; return _x`. The same test
  `OCaml5.Lcnf.redArgTarget?` makes; it is repeated here so this module imports nothing. -/
  redArgTarget? (d : Decl .pure) : Option Name :=
    match d.value with
    | .code (.let decl (.return r)) =>
      match decl.value with
      | .const callName _ _ =>
        if callName == d.name ++ redArgSuffix && r == decl.fvarId then some callName else none
      | _ => none
    | _ => none

/-! ## 5. The manifest -/

/-- Everything a generator run should be able to hand a reader: what it read, from where,
under which compiler, and what it could not read. -/
structure Manifest where
  leanVersion : String
  /-- `mono`, always, on this route; the field exists so a reader never has to assume. -/
  phase : String := "mono"
  roots : Array Name
  /-- Modules whose environment the roots were looked up in. -/
  imports : Array Name := #[]
  closure : Closure
  deriving Inhabited

namespace Manifest

private def availJson : Availability → Json
  | .extern k => Json.mkObj [("kind", "extern"), ("entries", Json.num k)]
  | a => Json.mkObj [("kind", Json.str (toString a))]

def declJson (d : DeclFacts) : Json :=
  Json.mkObj
    [ ("name", Json.str d.name.toString)
    , ("requestedAs", Json.str d.requestedAs.toString)
    , ("availability", availJson d.availability)
    , ("declHash", Json.str d.declHash)
    , ("arity", Json.num d.arity)
    , ("erasedParams", Json.num d.erasedParams)
    , ("size", Json.num d.size)
    , ("recursive", Json.bool d.recursive)
    , ("safe", Json.bool d.safe)
    , ("inline", Json.bool d.inlineAttr)
    , ("valid", match d.valid with | .ok _ => Json.bool true | .error _ => Json.bool false)
    , ("invalidReason", match d.valid with | .ok _ => Json.null | .error m => Json.str m)
    , ("module", match d.module with | none => Json.null | some m => Json.str m.toString)
    , ("moduleIsModule", Json.bool d.moduleIsModule)
    , ("constructs", d.census.toJson)
    , ("callees", Json.arr (d.callees.map fun n => Json.str n.toString)) ]

def toJson (m : Manifest) : Json :=
  let c := m.closure
  Json.mkObj
    [ ("format", "conform-lcnf-manifest-v1")
    , ("leanVersion", Json.str m.leanVersion)
    , ("phase", Json.str m.phase)
    , ("roots", Json.arr (m.roots.map fun n => Json.str n.toString))
    , ("imports", Json.arr (m.imports.map fun n => Json.str n.toString))
    , ("summary", Json.mkObj
        [ ("declarations", Json.num c.decls.size)
        , ("invalid", Json.num c.invalid.size)
        , ("primitives", Json.num c.primitives.size)
        , ("missing", Json.num c.missing.size)
        , ("frontier", Json.num c.frontier.size)
        , ("constructors", Json.num c.ctors.size) ])
    , ("constructs", c.census.toJson)
    , ("casesTypes", Json.mkObj (c.census.casesTypesList.map fun (n, k) => (n.toString, Json.num k)))
    , ("primitivesUsed", Json.arr (c.primitives.map fun n => Json.str n.toString))
    , ("missing", Json.arr (c.missing.map fun f =>
        Json.mkObj [ ("name", Json.str f.name.toString)
                   , ("availability", availJson f.availability)
                   , ("constKind", Json.str f.constKind)
                   , ("module", match f.module with | none => Json.null | some m => Json.str m.toString)
                   , ("moduleIsModule", Json.bool f.moduleIsModule) ]))
    , ("frontier", Json.arr (c.frontier.map fun n => Json.str n.toString))
    , ("declarations", Json.arr (c.decls.map declJson)) ]

/-- The manifest as a `Conform.Report`: one row per declaration for `lcnf.decl.valid`, one
row per unreadable callee for `lcnf.decl.available`, one row per unreached callee for
`lcnf.closure.frontier`. The evidence is `tested` throughout: `Decl.check` is a finite run of
the compiler's own checker on named inputs, not a theorem. -/
def toReport (m : Manifest) (tool : String := "conform-lcnf-validity") : Report :=
  let c := m.closure
  let declRows : Array Row := c.decls.map fun d =>
    let subj : Subject := { kind := "declaration", path := [d.name.toString] }
    match d.valid with
    | .ok _ =>
      Row.pass "lcnf.decl.valid" subj .tested
        s!"Decl.check accepted the mono body ({d.size} nodes, arity {d.arity})"
        (declJson d)
    | .error msg => Row.refused "lcnf.decl.valid" subj msg (declJson d)
  let missingRows : Array Row := c.missing.map fun f =>
    Row.unresolved "lcnf.decl.available" { kind := "declaration", path := [f.name.toString] }
      s!"no mono code: {f.availability} ({f.constKind}, module system: {f.moduleIsModule})"
      (availJson f.availability)
  let frontierRows : Array Row := c.frontier.map fun n =>
    Row.unresolved "lcnf.closure.frontier" { kind := "declaration", path := [n.toString] }
      "beyond the closure cap"
  { tool
    pins := [ { name := "lean", value := m.leanVersion }, { name := "phase", value := m.phase } ]
    expected := c.decls.size + c.missing.size + c.frontier.size
    rows := declRows ++ missingRows ++ frontierRows }

end Manifest

end Conform.Lcnf
