import Conform.Lcnf.Validity
import OCaml5.Lcnf.Translate

/-!
# Conform.Effect4.Lcnf — Effect4 as the first configuration of the LCNF tooling

**What it is.** The `--run` driver that points `Conform.Lcnf.Validity` at this repository's
mono closure, and the *fidelity table*: one row per entry of `OCaml5.Lcnf.Translate.builtin?`
and `OCaml5.Lcnf.Types.builtinTy?` saying how faithfully the OCaml form reproduces the Lean
meaning. The generic half knows none of this — the roots, the primitive predicate and the
fidelity classes all live here, on the Effect4 side of the extensibility rule
(`docs/research/type-tooling/brief-common.md`).

    lake env lean -M4096 --run tools/Conform/Effect4/Lcnf.lean \
      --import Effect4.Api --out <dir> --cap 2000 Effect4.Api.run Effect4.Api.replay

**Depends on.** `Conform.Lcnf.Validity` (generic), `OCaml5.Lcnf.Translate` (the route under
audit). It is a tool: `IO`, `CoreM`, imported by nothing.
-/

open Lean Compiler LCNF
open Conform Conform.Lcnf

namespace Conform.Effect4.Lcnf

/-! ## 1. The fidelity table

How faithfully an OCaml builtin row reproduces the Lean constant it stands for. The classes
are the brief's: *exact*, *exact under a stated domain*, *approximate*, *unsound*. The class
is a claim about the **rule**, checked against the Lean definition and, where a probe settles
it, against `ocaml` — the receipts are in `docs/research/type-tooling/lcnf/`. -/

inductive Fidelity
  /-- The OCaml form denotes the same function on the whole Lean domain. -/
  | exact
  /-- The OCaml form denotes the same function on a stated sub-domain, and something else
  outside it. The domain is the row's `domain` field. -/
  | domain
  /-- The OCaml form denotes a different function that agrees on the values this tree
  produces, or differs in a way the row states. -/
  | approximate
  /-- The OCaml form denotes a different function and the difference can be reached. -/
  | unsound
  deriving DecidableEq, Repr, Inhabited

namespace Fidelity
protected def toString : Fidelity → String
  | .exact => "exact"
  | .domain => "exact-under-domain"
  | .approximate => "approximate"
  | .unsound => "unsound"
instance : ToString Fidelity := ⟨Fidelity.toString⟩
end Fidelity

/-- One row of the fidelity table. -/
structure FidRow where
  /-- The Lean constant the `builtin?` table matches on. -/
  lean : Name
  /-- The OCaml form, as the table writes it. -/
  ocaml : String
  fidelity : Fidelity
  /-- The domain on which the row is exact (`""` when the class is `exact`). -/
  domain : String := ""
  /-- Why: the difference, or the argument that there is none. -/
  note : String
  deriving Inhabited

/-- The whole `builtin?` table of `src/OCaml5/Lcnf/Translate.lean:144-244`, one row per
matched name, classified. Transcription is guarded: `fidelityTableCovers` below checks that
every `lean` name here really is a `builtin?` row, so a rename in `Translate` shows up as a
failure rather than as a silently stale table. -/
def fidelityTable : List FidRow :=
  [ -- Nat comparisons: `Nat` is `int`, and the comparison is exact wherever both operands are
    -- representable.
    ⟨`Nat.decEq, "=", .domain, "0 ≤ a, b < 2^62", "Lean `Nat` is unbounded; OCaml `int` is 63-bit. `=` on `int` is structural equality of the machine word, which agrees with `Nat` equality on the representable range."⟩
  , ⟨`Nat.beq, "=", .domain, "0 ≤ a, b < 2^62", "as `Nat.decEq`."⟩
  , ⟨`instDecidableEqNat, "=", .domain, "0 ≤ a, b < 2^62", "as `Nat.decEq`; `Decidable` is `Bool` at mono."⟩
  , ⟨`Nat.decLt, "<", .domain, "0 ≤ a, b < 2^62", "OCaml's `<` on `int` is signed; a saturated or wrapped operand can compare wrongly, which is why literals and `pow` saturate rather than wrap."⟩
  , ⟨`Nat.blt, "<", .domain, "0 ≤ a, b < 2^62", "as `Nat.decLt`."⟩
  , ⟨`Nat.decLe, "<=", .domain, "0 ≤ a, b < 2^62", "as `Nat.decLt`."⟩
  , ⟨`Nat.ble, "<=", .domain, "0 ≤ a, b < 2^62", "as `Nat.decLt`."⟩
  , ⟨`Nat.add, "+", .domain, "a + b < 2^62", "OCaml `+` wraps at 2^62 without a trap; Lean's `Nat.add` does not."⟩
  , ⟨`Nat.mul, "*", .domain, "a * b < 2^62", "as `Nat.add`."⟩
  , ⟨`Nat.div, "/", .approximate, "b ≠ 0", "`Nat.div a 0 = 0` in Lean; OCaml raises `Division_by_zero`. An absence in Lean becomes an exception in OCaml — the one row where a Lean total function becomes an OCaml partial one."⟩
  , ⟨`Nat.mod, "mod", .approximate, "b ≠ 0", "`Nat.mod a 0 = a` in Lean; OCaml raises `Division_by_zero`."⟩
  , ⟨`Nat.sub, "max 0 (a - b)", .domain, "0 ≤ a, b < 2^62", "truncated subtraction, spelled out; exact on the representable range."⟩
  , ⟨`Nat.succ, "a + 1", .domain, "a + 1 < 2^62", "as `Nat.add`."⟩
  , ⟨`Nat.pred, "max 0 (a - 1)", .domain, "a < 2^62", "truncated predecessor."⟩
  , ⟨`Nat.pow, "_pow_clamped a b", .approximate, "a ^ b < max_int", "saturating: `2 ^ 64` reads as `max_int` rather than wrapping to 0. The host profile of `ocaml/gen/NOTES.md` §5. Note the helper's own multiplications are checked against `max_int / a`, so the saturation is monotone."⟩
  , ⟨`Nat.shiftLeft, "a * _pow_clamped 2 b", .approximate, "a * 2^b < max_int", "the same clamp."⟩
  , ⟨`Nat.shiftRight, "if b >= 63 then 0 else a lsr b", .domain, "a < 2^62", "OCaml's `lsr` is undefined at shift ≥ 63, so the row guards it; `lsr` on a non-negative `int` is Lean's `shiftRight` below 2^62."⟩
  , ⟨`Nat.land, "land", .domain, "a, b < 2^62", "bitwise and on the 63-bit word."⟩
  , ⟨`Nat.lor, "lor", .domain, "a, b < 2^62", "bitwise or on the 63-bit word."⟩
  , ⟨`Nat.xor, "lxor", .domain, "a, b < 2^62", "bitwise xor on the 63-bit word."⟩
    -- UInt8: `int` with an explicit truncation on the way in.
  , ⟨`UInt8.decEq, "=", .exact, "", "`UInt8` is `int`; both sides are already reduced mod 256 by `ofNat`."⟩
  , ⟨`instDecidableEqUInt8, "=", .exact, "", "as `UInt8.decEq`."⟩
  , ⟨`UInt8.beq, "=", .exact, "", "as `UInt8.decEq`."⟩
  , ⟨`UInt8.ofNat, "a land 255", .exact, "", "`UInt8.ofNat` is `n % 256`, and `land 255` is `% 256` on a non-negative `int`."⟩
  , ⟨`UInt8.ofNatLT, "a land 255", .exact, "", "the argument is already < 256; the mask is a no-op."⟩
  , ⟨`UInt8.ofNatTruncate, "a land 255", .approximate, "", "`ofNatTruncate` **clamps** at 255 in Lean (`min n 255`), the row **wraps** (`n land 255`). They differ for every `n ≥ 256`: `ofNatTruncate 256 = 255`, the row gives `0`. Not reached by the audited closure, but the row is wrong as written."⟩
  , ⟨`UInt8.toNat, "a", .exact, "", "identity on the representation."⟩
  , ⟨`UInt8.toUInt64, "a", .exact, "", "identity on the representation; `UInt64` is `int` too."⟩
  , ⟨`UInt8.toUInt32, "a", .exact, "", "identity on the representation."⟩
    -- Bool
  , ⟨`Bool.decEq, "=", .exact, "", "OCaml `bool` is Lean `Bool`."⟩
  , ⟨`instDecidableEqBool, "=", .exact, "", "as `Bool.decEq`."⟩
  , ⟨`Bool.not, "not", .exact, "", ""⟩
  , ⟨`not, "not", .exact, "", ""⟩
  , ⟨`Bool.and, "&&", .approximate, "", "OCaml's `&&` is short-circuiting and Lean's `Bool.and` is a strict function of two already-evaluated arguments. At mono LCNF both arguments are already `let`-bound values, so the difference is unobservable *here* — but the row is not exact as a function-level claim, and an emitter that inlined the arguments would change evaluation order."⟩
  , ⟨`and, "&&", .approximate, "", "as `Bool.and`."⟩
  , ⟨`Bool.or, "||", .approximate, "", "as `Bool.and`."⟩
  , ⟨`or, "||", .approximate, "", "as `Bool.and`."⟩
    -- String: the interesting one.
  , ⟨`String.decEq, "=", .exact, "", "OCaml's structural `=` on `string` is byte equality; two Lean strings are equal iff their UTF-8 encodings are equal, and the route's strings *are* their UTF-8 bytes."⟩
  , ⟨`instDecidableEqString, "=", .exact, "", "as `String.decEq`."⟩
  , ⟨`String.append, "^", .exact, "", "concatenation of UTF-8 byte sequences is the encoding of the concatenation."⟩
  , ⟨`String.length, "String.length", .unsound, "the string is ASCII", "Lean's `String.length` counts **Unicode scalar values**; OCaml's counts **bytes**. They differ on the first non-ASCII character. `Effect4.Program.Ty.render` and the wire's tag strings are ASCII today, so the difference is not reached — but nothing in the route enforces that, and a service target string carrying a non-ASCII identifier would silently disagree."⟩
    -- List
  , ⟨`List.appendTR, "@", .exact, "", "`appendTR` is `append` (the tail-recursive spelling the mono phase leaves behind)."⟩
  , ⟨`List.append, "@", .exact, "", ""⟩
  , ⟨`List.reverse, "List.rev", .exact, "", ""⟩
  , ⟨`List.reverseAux, "List.rev_append", .exact, "", "`List.reverseAux as bs = List.rev_append as bs`."⟩
  , ⟨`List.length, "List.length", .domain, "length < 2^62", "the result is a `Nat` spelled as `int`."⟩
  , ⟨`List.lengthTR, "List.length", .domain, "length < 2^62", "as `List.length`."⟩
  , ⟨`List.instDecidableEqNil, "l = []", .exact, "", "the structural comparison of a list against the empty list is `isEmpty`."⟩
  , ⟨`List.isEmpty, "l = []", .exact, "", ""⟩
  , ⟨`List.elem, "List.exists (inst a) l", .exact, "", "`[BEq α]` is a one-field structure at mono, so the instance is a relevant argument. Lean's `List.elem a (b :: l)` tests `a == b`, i.e. `inst a b`; `List.exists (inst a) l` tests the same, in the same order."⟩
  , ⟨`List.contains, "List.exists (inst a) l", .approximate, "BEq is symmetric", "Lean's `List.contains l a` is `l.any (· == a)`, i.e. `inst b a` for each element `b`; the row builds `inst a b`. The two agree only for a symmetric `BEq`. Every `BEq` this closure passes is a derived `DecidableEq`, which is symmetric, so the difference is not reached — but the row is argument-order-wrong as written."⟩
  , ⟨`List.map, "List.map", .exact, "", ""⟩
  , ⟨`List.mapTR, "List.map", .exact, "", ""⟩
  , ⟨`List.filter, "List.filter", .exact, "", ""⟩
  , ⟨`List.filterTR, "List.filter", .exact, "", ""⟩
  , ⟨`List.foldl, "List.fold_left", .exact, "", "same argument order (`f`, `init`, `l`) and same associativity."⟩
  , ⟨`List.all, "List.for_all p l", .exact, "", "Lean takes the list first, OCaml the predicate first; the row swaps."⟩
  , ⟨`List.any, "List.exists p l", .exact, "", "as `List.all`."⟩
  , ⟨`List.find?, "List.find_opt", .exact, "", ""⟩
  , ⟨`List.flatten, "List.concat", .exact, "", "OCaml's `List.concat` is `flatten`."⟩
  , ⟨`List.flattenTR, "List.concat", .exact, "", ""⟩
  , ⟨`List.filterMap, "List.filter_map", .exact, "", ""⟩
  , ⟨`List.filterMapTR, "List.filter_map", .exact, "", ""⟩
    -- Array as list: the shim.
  , ⟨`Array.mkEmpty, "[]", .exact, "", "`Array` is `list`; the capacity hint is dropped."⟩
  , ⟨`Array.emptyWithCapacity, "[]", .exact, "", ""⟩
  , ⟨`Array.toList, "a", .exact, "", "identity under the shim."⟩
  , ⟨`List.toArray, "a", .exact, "", "identity under the shim."⟩
  , ⟨`Array.push, "a @ [x]", .approximate, "", "denotationally exact; **O(n) per push** where Lean's `Array.push` is amortised O(1). A `push` in a loop is quadratic. This is the one row whose defect is complexity rather than meaning."⟩
  , ⟨`Array.size, "List.length", .approximate, "", "denotationally exact, O(n) where Lean's is O(1)."⟩
  , ⟨`Array.appendList, "@", .exact, "", ""⟩
  , ⟨`List.foldl._at_.Array.appendList.spec_0, "@", .exact, "", "the specialisation of the fold that `Array.appendList` compiles to."⟩
  , ⟨`USize.ofNat, "a", .domain, "a < 2^62", "`USize` is the shim's index type and is `int`."⟩
  , ⟨`USize.toNat, "a", .exact, "", ""⟩
  , ⟨`USize.ofNatLT, "a", .exact, "", ""⟩
  , ⟨`USize.decEq, "=", .domain, "a, b < 2^62", ""⟩
  , ⟨`USize.beq, "=", .domain, "a, b < 2^62", ""⟩
  , ⟨`USize.sub, "max 0 (a - b)", .unsound, "a ≥ b", "`USize.sub` in Lean **wraps** (it is `Fin (2^64)` subtraction: `0 - 1 = 2^64 - 1`); the row **truncates** to 0. Every use in this closure is a bounded index decrement where `a ≥ b`, so the difference is not reached, but the row is not the Lean function."⟩
  , ⟨`USize.add, "+", .unsound, "a + b < 2^62", "`USize.add` wraps at 2^64 in Lean; OCaml's `+` wraps at 2^62. Two different wrapping points."⟩
  , ⟨`Array.uget, "List.nth", .unsound, "i < length", "Lean's `Array.uget a i h` is total (`h` proves `i` in range) and the row is `List.nth`, which **raises** `Failure \"nth\"` out of range and `Invalid_argument` on a negative index. Under the shim it is also O(i) rather than O(1)."⟩
  , ⟨`Array.get!, "List.nth", .unsound, "i < length", "Lean's `Array.get!` out of range **panics and returns `default`** (execution continues); `List.nth` raises. An absence in Lean becomes an exception in OCaml."⟩
  , ⟨`Array.fget, "List.nth", .unsound, "i < length", "as `Array.get!`."⟩
    -- Option, Prod, panic
  , ⟨`Option.isSome, "Option.is_some", .exact, "", ""⟩
  , ⟨`Option.isNone, "Option.is_none", .exact, "", ""⟩
  , ⟨`Option.getD, "Option.value ~default", .exact, "", ""⟩
  , ⟨`Option.map, "Option.map", .exact, "", ""⟩
  , ⟨`Option.bind, "Option.bind", .exact, "", ""⟩
  , ⟨`Prod.fst, "fst", .exact, "", ""⟩
  , ⟨`Prod.snd, "snd", .exact, "", ""⟩
  , ⟨`panic, "failwith", .approximate, "", "Lean's `panic` logs and **returns `default`**: the caller continues with a junk value. OCaml's `failwith` raises `Failure`. The OCaml behaviour is arguably the better one, but it is not the Lean one, and a Lean theorem about a program that panics says nothing about an OCaml run that aborts."⟩
  , ⟨`panicCore, "failwith", .approximate, "", "as `panic`."⟩ ]

/-- Every row of `fidelityTable` names a constant `OCaml5.Lcnf.builtin?` really matches.
A row whose name `builtin?` does not know is a stale transcription. -/
def fidelityTableCovers : List Name :=
  fidelityTable.filterMap fun r =>
    if (OCaml5.Lcnf.builtin? r.lean).isSome then none else some r.lean

/-- The `builtinTy?` table, classified the same way (`src/OCaml5/Lcnf/Types.lean:48-62`). -/
def typeFidelityTable : List FidRow :=
  [ ⟨``Nat, "int", .domain, "n < 2^62", "OCaml `int` is 63-bit, Lean `Nat` unbounded."⟩
  , ⟨``Int, "int", .domain, "-2^62 ≤ n < 2^62", "and `Int` and `Nat` share one OCaml type, so an emitter cannot tell them apart in an annotation."⟩
  , ⟨``UInt8, "int", .exact, "", "the range 0..255 is inside `int`."⟩
  , ⟨``UInt16, "int", .exact, "", ""⟩
  , ⟨``UInt32, "int", .exact, "", ""⟩
  , ⟨``UInt64, "int", .unsound, "n < 2^62", "**the hole.** `UInt64` values reach 2^64 - 1; OCaml's `int` holds 2^62 - 1. The wire's big-endian 64-bit fields and `Effect4.Store.Val.wf`'s `… < 2 ^ 64` live in this type. Nothing in the route detects the overflow: it wraps."⟩
  , ⟨``USize, "int", .unsound, "n < 2^62", "as `UInt64` — and `USize` is the shim's index type, so it is also the type every `Array` index is spelled in."⟩
  , ⟨``Bool, "bool", .exact, "", ""⟩
  , ⟨``String, "string", .approximate, "the string is ASCII", "Lean's `String` is a sequence of Unicode scalar values; OCaml's is a byte sequence. Equality and concatenation agree; `length`, indexing and any `Char` operation do not."⟩
  , ⟨``Unit, "unit", .exact, "", ""⟩
  , ⟨``PUnit, "unit", .exact, "", ""⟩
  , ⟨``Char, "char", .unsound, "the character is ASCII", "Lean's `Char` is a Unicode scalar value (21 bits); OCaml's `char` is one byte. There is no rule for `Char` operations in `builtin?` at all, so a `Char` in code is a hole — but a `Char` in a *type* is silently `char`."⟩
  , ⟨``Float, "float", .exact, "", "both are IEEE 754 binary64. No `Float` operation has a `builtin?` row, so any arithmetic is a hole."⟩
  , ⟨``List, "list", .exact, "", ""⟩
  , ⟨``Array, "list", .approximate, "", "the shim: denotationally a sequence, operationally a different cost model (see `Array.push`, `Array.uget`)."⟩
  , ⟨``Option, "option", .exact, "", ""⟩
  , ⟨``Prod, "*", .exact, "", ""⟩
  , ⟨``Except, "result", .exact, "", "`Except ε α` is `(α, ε) result`, arguments swapped."⟩ ]

/-! ## 2. The primitive predicate

What the OCaml route does *not* descend into: a `builtin?` row and (when a table is given)
an `Extract Constant` row. This is the argument the generic walker takes. -/

def ocamlPrimitive (ex : OCaml5.Lcnf.Externs) : Name → Bool := fun n =>
  (OCaml5.Lcnf.builtin? n).isSome || ex.hasFn n

/-! ## 3. The driver -/

structure Args where
  imports : Array Name := #[`Effect4.Api]
  roots : Array Name := #[]
  cap : Nat := 4096
  out : Option String := none
  checkTypes : Bool := false
  /-- Do not treat the OCaml builtin table as primitive: walk into the stdlib too, so the
  measurement says how much of the closure the table hides. -/
  noBuiltins : Bool := false
  /-- Compile a callee whose mono body the extension does not carry, instead of recording it
  as `missing` (`Conform.Lcnf.Walk.Config.onDemand`). An **addition**: off by default, so a
  default run reads exactly what an out-of-process generator reads. -/
  onDemand : Bool := false

def parseArgs : List String → Args → Args
  | "--import" :: m :: rest, a =>
    parseArgs rest { a with imports := ((m.splitOn ",").map String.toName).toArray }
  | "--cap" :: n :: rest, a => parseArgs rest { a with cap := n.toNat! }
  | "--out" :: p :: rest, a => parseArgs rest { a with out := some p }
  | "--check-types" :: rest, a => parseArgs rest { a with checkTypes := true }
  | "--no-builtins" :: rest, a => parseArgs rest { a with noBuiltins := true }
  | "--on-demand" :: rest, a => parseArgs rest { a with onDemand := true }
  | r :: rest, a => parseArgs rest { a with roots := a.roots.push r.toName }
  | [], a => a

def main (argv : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let args := parseArgs argv {}
  if args.roots.isEmpty then
    IO.eprintln "usage: … Lcnf.lean [--import M,N] [--cap n] [--out dir] [--check-types] [--no-builtins] [--on-demand] root…"
    return 2
  let env ← importModules (args.imports.map fun m => { module := m }) {} 0
  let ctx : Core.Context := { fileName := "<conform-lcnf>", fileMap := default }
  let act : CoreM UInt32 := do
    -- the transcription guard first: a stale fidelity row is a stale audit
    unless fidelityTableCovers.isEmpty do
      IO.eprintln s!"fidelity table names constants `builtin?` does not match: {fidelityTableCovers}"
      return 3
    let cfg : Walk.Config :=
      { primitive := if args.noBuiltins then (fun _ => false) else ocamlPrimitive {}
        cap := args.cap
        onDemand := args.onDemand }
    let closure ← walkClosure args.roots cfg args.checkTypes
    let manifest : Manifest :=
      { leanVersion := Lean.versionString, roots := args.roots, imports := args.imports
        closure := closure }
    let census := closure.census
    -- the human summary
    IO.println s!"roots: {args.roots}"
    IO.println s!"declarations: {closure.decls.size}  invalid: {closure.invalid.size}  \
      primitives: {closure.primitives.size}  missing: {closure.missing.size}  \
      frontier: {closure.frontier.size}  constructors: {closure.ctors.size}"
    IO.println "construct census (mono/pure fragment, 26 constructors):"
    for k in constructs do
      IO.println s!"  {k}: {census.get k}"
    IO.println s!"max local-function arity: {census.maxFunArity}, nullary local functions: {census.nullaryFuns}"
    IO.println s!"largest Nat literal: {census.maxNatLit}  (≥ 2^62: {census.bigNatLits})  \
      non-ASCII string literals: {census.nonAsciiStrLits}"
    IO.println s!"cases scrutinee types ({census.casesTypesList.length}):"
    for (n, k) in census.casesTypesList do IO.println s!"  {n}: {k}"
    IO.println s!"proj types ({census.projTypesList.length}):"
    for (n, k) in census.projTypesList do IO.println s!"  {n}: {k}"
    IO.println s!"missing ({closure.missing.size}):"
    for f in closure.missing do
      IO.println s!"  {f.name}: {f.availability} ({f.constKind}) module={f.module} moduleSystem={f.moduleIsModule}"
    IO.println s!"frontier ({closure.frontier.size}): {closure.frontier}"
    IO.println s!"invalid ({closure.invalid.size}):"
    for d in closure.invalid do
      match d.valid with
      | .error m => IO.println s!"  {d.name}: {m}"
      | .ok _ => pure ()
    IO.println s!"primitives hit ({closure.primitives.size}):"
    for n in closure.primitives do IO.println s!"  {n}"
    -- the availability catch's remedy, and its self-check. Both are silent unless asked for,
    -- so a default run's bytes are the bytes it had before the flag existed.
    if args.onDemand then
      let onDemand := closure.decls.filter (·.availability == .onDemand)
      IO.println s!"on-demand compiled ({onDemand.size}), still missing ({closure.missing.size}):"
      for d in onDemand do IO.println s!"  {d.name} ({d.size} nodes)"
      -- the mechanism's own self-check, and it is not a formality: recompile every
      -- declaration that *does* have a persisted body and say how often the in-process
      -- compile reproduces it. See the note's §2 — it usually does not.
      let mut same := 0
      let mut differ := 0
      let mut noCode := 0
      let mut noCodeInternal := 0
      let mut examples : Array String := #[]
      for d in closure.decls do
        match ← recompileAgrees? d.name with
        | none =>
          noCode := noCode + 1
          -- `Name.isInternal` is the compiler's own "the frontend could not have written
          -- this" test: `_redArg`, `_lam_N` and the `._at_.….spec_N` chains all match it,
          -- and those are exactly the names that have no kernel definition to compile.
          if d.name.isInternal then noCodeInternal := noCodeInternal + 1
        | some (alpha, sameHash) =>
          if alpha then same := same + 1
          else
            differ := differ + 1
            if examples.size < 8 then
              examples := examples.push s!"{d.name} (same DeclHash: {sameHash})"
      IO.println s!"recompiled {closure.decls.size}: alphaEqv {same}, differ {differ}, \
        no fresh body {noCode} (of which internal names: {noCodeInternal})"
      for e in examples do IO.println s!"  differs: {e}"
    -- cross-check against the real translator: the same roots through
    -- `OCaml5.Lcnf.translateClosure`, so the walker's numbers and the route's numbers are
    -- compared rather than assumed equal, and the OCaml **name collisions** are measured.
    let tc ← OCaml5.Lcnf.translateClosure args.roots args.cap {} {}
    let mut byName : Std.HashMap String (Array Name) := {}
    for t in tc.decls do
      byName := byName.insert t.ocamlName ((byName.getD t.ocamlName #[]).push t.leanName)
    let collisions := byName.toList.filter fun (_, ns) => ns.size > 1
    IO.println s!"translator: {tc.decls.size} declarations, {tc.todos.size} todos, \
      {tc.missing.size} missing, {tc.frontier.size} frontier, \
      {tc.wrapperRefs.size} wrapper refs, {tc.realTypes.size} real types"
    IO.println s!"OCaml global-name collisions ({collisions.length}):"
    for (nm, ns) in collisions do IO.println s!"  {nm} <- {ns}"
    IO.println s!"translator todos ({tc.todos.size}):"
    for t in tc.todos do IO.println s!"  {t}"
    match args.out with
    | none => pure ()
    | some dir =>
      IO.FS.createDirAll dir
      IO.FS.writeFile (dir ++ "/manifest.json") (manifest.toJson.pretty ++ "\n")
      let report := manifest.toReport
      IO.FS.writeFile (dir ++ "/report.json") (report.sorted.toJson.pretty ++ "\n")
      -- the fidelity table, as data, with the rows this closure actually hit marked
      -- a primitive is hit under its `_redArg` twin's name as often as under its own;
      -- `builtin?` itself matches on `stripRedArg n`, so the ledger must too
      let hit : Std.HashSet Name :=
        closure.primitives.foldl (fun s n => s.insert (Conform.Lcnf.stripRedArg n)) {}
      let fidJson := Json.arr (fidelityTable.toArray.map fun r =>
        Json.mkObj
          [ ("lean", Json.str r.lean.toString), ("ocaml", Json.str r.ocaml)
          , ("fidelity", Json.str (toString r.fidelity)), ("domain", Json.str r.domain)
          , ("note", Json.str r.note), ("hit", Json.bool (hit.contains r.lean)) ])
      let tyFidJson := Json.arr (typeFidelityTable.toArray.map fun r =>
        Json.mkObj
          [ ("lean", Json.str r.lean.toString), ("ocaml", Json.str r.ocaml)
          , ("fidelity", Json.str (toString r.fidelity)), ("domain", Json.str r.domain)
          , ("note", Json.str r.note) ])
      IO.FS.writeFile (dir ++ "/fidelity.json")
        ((Json.mkObj [("values", fidJson), ("types", tyFidJson)]).pretty ++ "\n")
      IO.println s!"wrote {dir}/manifest.json, {dir}/report.json, {dir}/fidelity.json"
      IO.eprintln report.render
    return (if closure.invalid.isEmpty then 0 else 1)
  let (code, _) ← (act.toIO ctx { env := env })
  return code

end Conform.Effect4.Lcnf

def main (argv : List String) : IO UInt32 := Conform.Effect4.Lcnf.main argv
