import Lean

/-!
# OCaml5.Lcnf.Census

**What it is.** A census of the constructs a mono-phase `Decl .pure` uses: one counter per
constructor of `Code`, `LetValue`, `LitValue`, `Arg`, `Alt` and `DeclValue` in the pure fragment,
so a translator's rule table can be compared with the surface it must cover. The route's closure
manifest reads it per declaration (`OCaml5.Lcnf.Gen`), and so does the validity walk of the
conformance tools (`Conform.Lcnf.Validity`).

**Properties.** `constructs` is the fixed 26-element list in a fixed order, so two runs over the
same closure produce the same bytes — *by construction*.
-/

namespace OCaml5.Lcnf
open Lean Compiler LCNF

/-! ## The construct census -/

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

end OCaml5.Lcnf
