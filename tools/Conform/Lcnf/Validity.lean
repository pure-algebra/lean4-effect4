import Lean
import Conform.Lcnf.Index
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

/-- The census of one `Code .pure`.

The traversal is the compiler's own `Code.forM` (`LCNF/Basic.lean:861`), which visits every
node of the tree in pre-order — the continuation of a `let`, the *body* and the continuation
of a local function or join point, and the code of every alternative. This function therefore
says only what a single node contributes; the recursion, and its termination, are the
compiler's, and the seat's `partial` walker is gone.

`step` counts an alternative at the `cases` node that owns it rather than when the walk
reaches its code, which is the same count in a different order: `HashMap` totals do not
depend on the order the increments arrive in. -/
def ofCode (c : Census) (code : Code .pure) : Census :=
  ((code.forM visit).run c).2
where
  visit (k : Code .pure) : StateM Census Unit := modify (step · k)
  step (c : Census) : Code .pure → Census
    | .let decl _ => (c.bump "Code.let").ofLetValue decl.value
    | .fun decl _ => fnBinder (c.bump "Code.fun") decl
    | .jp decl _ => fnBinder (c.bump "Code.jp") decl
    | .jmp _ args => (c.bump "Code.jmp").ofArgs args
    | .return _ => c.bump "Code.return"
    | .unreach _ => c.bump "Code.unreach"
    | .cases cs =>
      let c := c.bump "Code.cases"
      let c := { c with casesTypes := bumpName c.casesTypes cs.typeName }
      cs.alts.foldl (init := c) altHead
  fnBinder (c : Census) (decl : FunDecl .pure) : Census :=
    { c with maxFunArity := max c.maxFunArity decl.params.size,
             nullaryFuns := c.nullaryFuns + (if decl.params.isEmpty then 1 else 0) }
  altHead (c : Census) : Alt .pure → Census
    | .default _ => c.bump "Alt.default"
    | .alt ctor _ _ =>
      let c := c.bump "Alt.alt"
      { c with altCtors := bumpName c.altCtors ctor }

/-- The census of one declaration, its body and its parameter list. `DeclValue.forCodeM` is
the compiler's door here, but it drops the `.extern` arm on the floor and this census has to
*count* it, so the two-arm match stays. -/
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
  /-- The persisted extension had no body, and the declaration was compiled **in this
  process** — `Lean.Compiler.LCNF.main` under `withoutModifyingEnv`, then `getMonoDecl?`.
  Only `Walk.Config.onDemand` produces this; with the flag off a walk reads exactly what an
  out-of-process generator would read. -/
  | onDemand
  deriving Inhabited, DecidableEq

namespace Availability

protected def toString : Availability → String
  | .code => "code"
  | .opaqueByVisibility => "opaque-by-visibility"
  | .extern _ => "extern"
  | .absent => "absent"
  | .onDemand => "on-demand"

instance : ToString Availability := ⟨Availability.toString⟩

/-- Whether a translator can read a body here. -/
def hasCode : Availability → Bool
  | .code | .onDemand => true
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

/-- Compile `n` through the compiler's whole pipeline **in this process** and read its mono
body back, leaving the environment as it was.

This is the answer to the availability catch (`seat-lcnf.md` §1.4): a declaration whose mono
body the `.olean` does not carry — because the module system's export filter dropped it, or
because the phase was never persisted — does not have to be a hole. `Lean.Compiler.LCNF.main`
is the same entry point `compileDecls` uses; `withoutModifyingEnv` discards the extension
state it writes.

**It is a fallback, not a reproduction, and the availability tag says so.** A body produced
here is what the compiler can make *from the imported environment*, which is not in general
the body it persisted when it compiled the defining module. Measured with `recompileAgrees?`
over the two audited closures: of the 20 declarations of the `Ty` closure, 3 recompile to an
`alphaEqv` body, 12 differ and 5 produce no fresh body at all; of the 605 of the `api`
closure, 68 agree, 155 differ, and 382 produce nothing. Two causes, both read off the printed
LCNF (`lcnf/idiom/probes/recompile-diff.txt`):

* **A matcher is no longer inlined.** `Ty.isNever` is persisted as a `cases` of 5 nodes; the
  fresh body is 3 nodes and still *calls* `Ty.isNever.match_1` with two lambda-lifted arms,
  because the matcher's own LCNF is not in the imported environment for the simplifier to
  inline. This is the same missing entry that makes `main` raise, below.
* **A mono type degrades to `lcAny`.** `Ty.join`'s two bodies print identically and are not
  `alphaEqv`: one `let`'s mono type is `List Effect4.Program.Ty` persisted and `List lcAny`
  fresh. `Code.alphaEqv` compares `LetDecl.type`, so a type-only difference is a difference.

The 382 that produce nothing are the compiler-generated twins — `_redArg`, `spec_N`, `_lam_N`
— which have no kernel definition, so `main` cannot be asked for them at all: they exist only
as a side effect of compiling their host.

So: use this to fill a hole, and read the `on-demand` availability as "a body, and not the
one the `.olean` would have carried". The gate on `opaque-by-visibility` (`seat-lcnf.md` §3
R7(ii)) stays the primary defence against a `module` migration; this is the second one.

A refusal (a `Prop`, a `noncomputable`, an `@[extern]` with no body, an elaboration error) is
`none`, never an exception: this is a *fallback*, and a caller that asked for it still gets a
`missing` row when it cannot be met.

**Why the failure of `main` is caught and the answer read anyway.** `main` runs the *whole*
pipeline, base → mono → impure, and the impure passes need more of the environment than an
`.olean` carries: recompiling a single declaration whose body used a `match` raises
`Failed to find LCNF signature for …match_1` inside `InferBorrow`
(`LCNF/InferBorrow.lean:333`), because the auxiliary matcher's *impure* signature was never
imported. That failure is **after** the mono phase's `saveMono`, so the body this function
wants is already in the (temporary) extension state when the exception is thrown; catching it
here and reading the extension afterwards is what makes the path work at all. Measured on six
`Effect4.Program.Ty` declarations: four raise in `InferBorrow`, and all six still yield a mono
body.

**The answer is read out of `monoExt`'s local state, not through `getMonoDecl?`.** This is
not a detail. `getMonoDecl?` goes through `findExtEntry?` (`LCNF/Basic.lean:1243-1251`), which
looks a name up by *module index first* and consults the local state only when the name has
none — so for an imported declaration it hands back the persisted entry and a fresh compile is
invisible through it. An entry is in the local state only if `saveMono` ran in this process,
so a `some` here is always the freshly compiled body. **Correction to `ir-reuse.md` §2, probe
D**: that probe read `getMonoDecl?` after recompiling an imported declaration and concluded
the pipeline was deterministic; it had compared the persisted declaration with itself. -/
structure Compilation where
  declaration : Option (Decl .pure)
  pipelineCompleted : Bool
  diagnostic : Option String
  options : String

/-- A mono body can survive a later pipeline failure. Keep that diagnostic and the selected
options so a caller cannot confuse available mono data with a successful full compilation. -/
def compileMono (n : Name) : CoreM Compilation := do
  withoutModifyingEnv do
    let options ← getOptions
    let mut diagnostic := none
    try
      Lean.Compiler.LCNF.main #[n] options
    catch error =>
      diagnostic := some (← error.toMessageData.toString)
    return {
      declaration := monoExt.getState (← getEnv) |>.find? n
      pipelineCompleted := diagnostic.isNone
      diagnostic
      options := toString options }

def compileMono? (n : Name) : CoreM (Option (Decl .pure)) := do
  return (← compileMono n).declaration

/-- Recompile `n` and compare with its persisted mono body: `Code.alphaEqv` (equal modulo
free-variable names) and `DeclHash` equality (`hash`, which is id-*sensitive*). `none` when
either side has no code — including when `compileMono?` could not produce one at all.

The ids are not normalised first, and do not need to be: `saveMono` runs `normalizeFVarIds`
on both sides (`LCNF/Passes.lean:66-73`), so where the two bodies agree the hashes agree too.
Both components are reported because they answer different questions — `alphaEqv` whether the
*code* is the same, `hash` whether the persisted bytes would be. -/
def recompileAgrees? (n : Name) : CoreM (Option (Bool × Bool)) := do
  let (_, persisted?) := monoAvailability (← getEnv) n
  let some persisted := persisted? | return none
  let some fresh ← compileMono? n | return none
  match persisted.value, fresh.value with
  | .code p, .code f => return some (Code.alphaEqv p f, hash p == hash f)
  | _, _ => return none

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
  /-- When the persisted extension has no body for a constant, compile it in this process
  (`compileMono?`) instead of recording it as `missing`. **Off by default**, and the default
  is the honest one: with it off the walk sees exactly what a generator running out of process
  sees, which is what the manifest is a manifest *of*. With it on, an `opaque-by-visibility`
  or `absent` callee that the compiler can still produce becomes an `on-demand` declaration
  and is checked and censused like any other. -/
  onDemand : Bool := false

/-- The `reduceArity` twin's suffix. -/
def redArgSuffix : Name := `_redArg

/-- `f` for `f._redArg`, `n` otherwise. -/
def stripRedArg (n : Name) : Name :=
  match n with
  | .str p "_redArg" => p
  | _ => n

/-- The constant heads a `Code .pure` calls, in first-occurrence order.

`Code.forM` is the traversal, so the seat's second `partial` walker is gone and the visiting
order is the compiler's — which is the same pre-order the hand walker had, so the
first-occurrence order of the result is unchanged. The seat contributes only the dedup, and
it now keeps a `NameSet` beside the array instead of rescanning the accumulator, so the cost
is linear rather than quadratic in the number of distinct callees. -/
def calledConstants (code : Code .pure) : Array Name :=
  (((code.forM visit).run (#[], ({} : NameSet))).2).1
where
  visit (c : Code .pure) : StateM (Array Name × NameSet) Unit :=
    match c with
    | .let decl _ =>
      match decl.value with
      | .const n _ _ => modify fun (acc, seen) =>
          if seen.contains n then (acc, seen) else (acc.push n, seen.insert n)
      | _ => pure ()
    | _ => pure ()

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
  compilation : Option Json := none

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
  let mono := persistedMonoIndex env
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
    let (avail, _) := monoAvailability env n
    let d? := mono.findIn? env n
    let mut compilation := none
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
    -- the availability catch's remedy: the extension had no body, so make one
    if cfg.onDemand && !avail.hasCode then
      let fresh ← compileMono n
      compilation := some (Json.mkObj [("pipelineCompleted", .bool fresh.pipelineCompleted),
        ("diagnostic", toJson fresh.diagnostic), ("options", .str fresh.options)])
      if let some d := fresh.declaration then
        -- `DeclValue.isCodeAndM` is the compiler's "and it is code" test; a fresh compile of
        -- a genuine `@[extern]` still yields an `.extern` value, which stays a `missing` row
        if ← d.value.isCodeAndM (fun _ => pure true) then
          avail := .onDemand
          d? := some d
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
          compilation
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
    , ("compilation", d.compilation.getD .null)
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
    required := (c.decls.map fun d => ⟨"lcnf.decl.valid", ⟨"declaration", [d.name.toString]⟩⟩) ++
      (c.missing.map fun f => ⟨"lcnf.decl.available", ⟨"declaration", [f.name.toString]⟩⟩) ++
      (c.frontier.map fun n => ⟨"lcnf.closure.frontier", ⟨"declaration", [n.toString]⟩⟩)
    rows := declRows ++ missingRows ++ frontierRows }

end Manifest

end Conform.Lcnf
