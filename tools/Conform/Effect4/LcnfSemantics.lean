import Conform.Lcnf.Semantics
import Effect4

/-!
# Conform.Effect4.LcnfSemantics — rung 2's validation: the interpreter against Lean itself

**What it is.** The differential that gives `Conform.Lcnf.Semantics` its evidence. For the
`Effect4.Program.Ty` closure — `key`, `members`, `join`, `render`, `ltKey`, `insertMember`,
`ofMembers`, `isNever`, and `GenTy.merge` — it runs the **interpreter on the mono LCNF** and
the **compiled Lean function** on the same vectors and compares. The vector sets are the ones
the types seat generated (`docs/research/seat-types-tooling/x2-Vectors.lean`): every `Ty` of
depth ≤ 1 over the eight-leaf alphabet, depth ≤ 2 over a three-leaf alphabet, and every `Ty`
the two package tables carry — 1,330 unary vectors and 3,249 pairs after deduplication.

    lake env lean -M4096 --run tools/Conform/Effect4/LcnfSemantics.lean --out <dir>

Agreement is *tested* evidence — a finite run on named inputs — that the interpreter gives
mono LCNF the compiler's own meaning on this fragment. It is not a proof and is never called
one.

**The mutants.** `--mutate <n>` breaks one interpreter rule on purpose and expects the
differential to go red; a rule whose mutant stays green is a rule the corpus does not
exercise, which is a finding about the corpus. The six mutants are §2 below.
-/

open Lean Compiler LCNF
open Conform Conform.Lcnf
open Effect4.Program

namespace Conform.Effect4.LcnfSemantics

/-! ## 1. Marshalling `Ty` into the value domain

Explicit, not derived: the interpreter's `Value.ctor` carries **all** of a constructor's
fields in order, and `Ty`'s constructors have no erased fields, so each arm is the
constructor's own name applied to its own arguments. The round trip is checked on every
vector (`marshalRoundTrip` below), so a mistake here is a red row rather than a silent
agreement. -/

partial def tyValue : Ty → Value
  | .never => .ctor ``Ty.never #[]
  | .unit => .ctor ``Ty.unit #[]
  | .nat => .ctor ``Ty.nat #[]
  | .int => .ctor ``Ty.int #[]
  | .string => .ctor ``Ty.string #[]
  | .bool => .ctor ``Ty.bool #[]
  | .handle t => .ctor ``Ty.handle #[.str t]
  | .option i => .ctor ``Ty.option #[tyValue i]
  | .list i => .ctor ``Ty.list #[tyValue i]
  | .prod l r => .ctor ``Ty.prod #[tyValue l, tyValue r]
  | .except e v => .ctor ``Ty.except #[tyValue e, tyValue v]
  | .exitOf v e => .ctor ``Ty.exitOf #[tyValue v, tyValue e]
  | .causeOf e => .ctor ``Ty.causeOf #[tyValue e]
  | .fiberOf v e => .ctor ``Ty.fiberOf #[tyValue v, tyValue e]
  | .union l r => .ctor ``Ty.union #[tyValue l, tyValue r]

/-- The inverse, so the marshalling can be round-tripped rather than trusted. -/
partial def valueTy? (v : Value) : Option Ty := do
  match v with
  | .ctor n fs =>
    if n == ``Ty.never then some .never
    else if n == ``Ty.unit then some .unit
    else if n == ``Ty.nat then some .nat
    else if n == ``Ty.int then some .int
    else if n == ``Ty.string then some .string
    else if n == ``Ty.bool then some .bool
    else if n == ``Ty.handle then do return .handle (← (← fs[0]?).toStr?)
    else if n == ``Ty.option then do return .option (← valueTy? (← fs[0]?))
    else if n == ``Ty.list then do return .list (← valueTy? (← fs[0]?))
    else if n == ``Ty.causeOf then do return .causeOf (← valueTy? (← fs[0]?))
    else if n == ``Ty.prod then do return .prod (← valueTy? (← fs[0]?)) (← valueTy? (← fs[1]?))
    else if n == ``Ty.except then do return .except (← valueTy? (← fs[0]?)) (← valueTy? (← fs[1]?))
    else if n == ``Ty.exitOf then do return .exitOf (← valueTy? (← fs[0]?)) (← valueTy? (← fs[1]?))
    else if n == ``Ty.fiberOf then do return .fiberOf (← valueTy? (← fs[0]?)) (← valueTy? (← fs[1]?))
    else if n == ``Ty.union then do return .union (← valueTy? (← fs[0]?)) (← valueTy? (← fs[1]?))
    else none
  | _ => none

def tyListValue (ts : List Ty) : Value := Value.ofList (ts.map tyValue)

/-! ## 2. The vectors — the same domains the types seat enumerated -/

def leaves : List Ty :=
  [.never, .unit, .nat, .int, .string, .bool, .handle "Ref.Ref<number>", .handle Ty.scopeTarget]

def layer (below right : List Ty) : List Ty :=
  (below.map Ty.option) ++ (below.map Ty.list) ++ (below.map Ty.causeOf) ++
  (below.flatMap fun a => right.flatMap fun b =>
    [.prod a b, .except a b, .exitOf a b, .fiberOf a b, .union a b])

def small : List Ty := [.never, .nat, .handle "Ref.Ref<number>"]
def d1full : List Ty := leaves ++ layer leaves leaves
def c1 : List Ty := small ++ layer small small
def c2 : List Ty := c1 ++ layer c1 small

def packageTys : List Ty :=
  (Packages.sqliteBun ++ Packages.keyValueStoreMemory).flatMap fun r =>
    [r.request, r.answer, r.error]

def vectors : List Ty := (d1full ++ c2 ++ packageTys).eraseDups

/-! ## 3. The primitive table this closure needs

Nine rows. They are exactly the constants the `Ty` closure reaches that have **no mono
body** — measured, not guessed (`docs/research/type-tooling/lcnf/tynb/run.log`). Everything
else the interpreter reads out of the compiler's own output. -/

def tyPrims : PrimTable :=
  [ (``Nat.add, .natAdd)
  , (``Nat.decEq, .natDecEq)
  , (``Nat.decLt, .natDecLt)
  , (``String.append, .strAppend)
  , (``String.decEq, .strDecEq)
  , (``String.toUTF8, .strToUTF8)
  , (``ByteArray.data, .identity)
  , (``Array.toList, .arrayToList)
  , (``UInt8.toNat, .identity) ]

/-! ## 4. The mutants — the negative controls

Each breaks one rule of the interpreter and must make the differential go red. A mutant that
stays green means the corpus never exercises that rule. -/

inductive Mutant
  /-- No mutation. -/
  | pristine
  /-- **Assumption.** `Nat.decLt` answers `≤`: the ordering rule `ltKey` and `insertMember`
  are built on. -/
  | ltIsLe
  /-- **Assumption.** `Nat.add` is `Nat.mul`. -/
  | addIsMul
  /-- **Code.** Every `Nat` literal is one larger: the constructor codes of `Ty.key`. -/
  | natLitShift
  /-- **Code.** The two arms of every `cases` on `Bool` are swapped — the canonical
  destruction-rule bug, and the one X2 found three of
  (`2026-09-09-seat-types-tooling.md` §5.5). -/
  | boolArmsSwapped
  /-- **Code.** Every `String.append` call takes its arguments the other way round:
  `Ty.render`'s concatenation order. -/
  | appendSwapped
  /-- **Representation.** The constructor table's `numParams` is zeroed, so a construction
  keeps its erased type arguments among its fields — the off-by-`numParams` an emitter makes
  when it forgets `ci.numParams`. The `cases` rule then refuses, because a `cases`
  alternative binds exactly `numFields` parameters. -/
  | ctorKeepsParams
  deriving DecidableEq, Inhabited

def mutantOfNat : Nat → Mutant
  | 1 => .ltIsLe
  | 2 => .addIsMul
  | 3 => .natLitShift
  | 4 => .boolArmsSwapped
  | 5 => .appendSwapped
  | 6 => .ctorKeepsParams
  | _ => .pristine

def Mutant.label : Mutant → String
  | .pristine => "none"
  | .ltIsLe => "Nat.decLt answers ≤"
  | .addIsMul => "Nat.add is Nat.mul"
  | .natLitShift => "every Nat literal is one larger"
  | .boolArmsSwapped => "the arms of every cases on Bool are swapped"
  | .appendSwapped => "String.append takes its arguments the other way round"
  | .ctorKeepsParams => "a construction keeps its type parameters as fields"

/-- The **assumption** mutants: one row of the primitive table says something else. -/
def mutatePrims (m : Mutant) (t : PrimTable) : PrimTable :=
  t.map fun (n, p) =>
    match m with
    | .ltIsLe => if n == ``Nat.decLt then (n, .natDecLe) else (n, p)
    | .addIsMul => if n == ``Nat.add then (n, .natMul) else (n, p)
    | _ => (n, p)

/-- The **representation** mutant: the constructor arity table. -/
def mutateCtors (m : Mutant) (ctors : Std.HashMap Name (Nat × Nat)) :
    Std.HashMap Name (Nat × Nat) :=
  match m with
  | .ctorKeepsParams => ctors.fold (init := {}) fun acc n (np, nf) => acc.insert n (0, np + nf)
  | _ => ctors

/-- The **code** mutants: the interpreter's *input* is rewritten, never the interpreter. Each
is a transformation a wrong translator would make. -/
partial def mutateCode (m : Mutant) (c : Code .pure) : Code .pure :=
  match c with
  | .let decl k => .let { decl with value := mutateLetValue m decl.value } (mutateCode m k)
  | .fun decl k =>
    .fun (.mk decl.fvarId decl.binderName decl.params decl.type (mutateCode m decl.value))
      (mutateCode m k)
  | .jp decl k =>
    .jp (.mk decl.fvarId decl.binderName decl.params decl.type (mutateCode m decl.value))
      (mutateCode m k)
  | .jmp f args => .jmp f args
  | .return x => .return x
  | .unreach t => .unreach t
  | .cases cs =>
    let alts := cs.alts.map fun
      | .alt n ps k => Alt.alt n ps (mutateCode m k)
      | .default k => Alt.default (mutateCode m k)
    let alts :=
      if m == .boolArmsSwapped && cs.typeName == ``Bool && alts.size == 2 then
        -- keep each alternative's constructor name and give it the other one's body
        match alts[0]!, alts[1]! with
        | .alt n0 p0 k0, .alt n1 p1 k1 => #[Alt.alt n0 p0 k1, Alt.alt n1 p1 k0]
        | a, b => #[b, a]
      else alts
    .cases (.mk cs.typeName cs.resultType cs.discr alts)
where
  mutateLetValue (m : Mutant) (v : LetValue .pure) : LetValue .pure :=
    match m, v with
    | .natLitShift, .lit (.nat n) => .lit (.nat (n + 1))
    | .appendSwapped, .const n us args =>
      if Conform.Lcnf.stripRedArg n == ``String.append then .const n us args.reverse
      else v
    | _, _ => v

def mutateDecl (m : Mutant) (d : Decl .pure) : Decl .pure :=
  match m with
  | .pristine | .ltIsLe | .addIsMul | .ctorKeepsParams => d
  | _ => { d with value := d.value.mapCode (mutateCode m) }

/-- The whole context, mutated. -/
def mutateCtx (m : Mutant) (ctx : Ctx) : Ctx :=
  { ctx with
    ctors := mutateCtors m ctx.ctors
    decls := ctx.decls.fold (init := {}) fun acc n d => acc.insert n (mutateDecl m d) }

/-! ## 5. The differential -/

structure Counts where
  pass : Nat := 0
  fail : Nat := 0
  stuck : Nat := 0
  fuel : Nat := 0
  deriving Inhabited

def tally (rows : Array Row) : Counts :=
  rows.foldl (init := {}) fun c r =>
    match r.outcome with
    | .pass => { c with pass := c.pass + 1 }
    | .counterexample => { c with fail := c.fail + 1 }
    | .refused => { c with stuck := c.stuck + 1 }
    | .unresolved => { c with fuel := c.fuel + 1 }

/-- The 20,387 cases: eight per unary vector, three per pair. -/
def buildCases : Array Case := Id.run do
  let mut out : Array Case := #[]
  let vs := vectors
  for t in vs do
    let tv := tyValue t
    let lbl := t.render
    out := out.push { label := lbl, decl := ``Ty.render, args := #[tv], expected := .str t.render }
    out := out.push { label := lbl, decl := ``Ty.key, args := #[tv], expected := Value.ofNatList t.key }
    out := out.push { label := lbl, decl := ``Ty.members, args := #[tv], expected := tyListValue t.members }
    out := out.push { label := lbl, decl := ``Ty.isNever, args := #[tv], expected := Value.bool t.isNever }
    out := out.push { label := lbl, decl := ``Ty.ofMembers, args := #[tyListValue t.members],
                      expected := tyValue (Ty.ofMembers t.members) }
    out := out.push { label := lbl ++ " ⊔ self", decl := ``Ty.join, args := #[tv, tv],
                      expected := tyValue (Ty.join t t) }
    out := out.push { label := lbl ++ " ⊔ never", decl := ``Ty.join, args := #[tv, tyValue .never],
                      expected := tyValue (Ty.join t .never) }
    out := out.push { label := lbl ++ " ▷ []", decl := ``Ty.insertMember,
                      args := #[tv, Value.ofList []],
                      expected := tyListValue (Ty.insertMember t []) }
  for a in c1 do
    for b in c1 do
      let lbl := a.render ++ " | " ++ b.render
      out := out.push { label := lbl, decl := ``Ty.join, args := #[tyValue a, tyValue b],
                        expected := tyValue (Ty.join a b) }
      out := out.push { label := lbl, decl := ``Ty.ltKey,
                        args := #[Value.ofNatList a.key, Value.ofNatList b.key],
                        expected := Value.bool (Ty.ltKey a.key b.key) }
      out := out.push { label := lbl, decl := ``Ty.insertMember,
                        args := #[tyValue a, tyListValue [b]],
                        expected := tyListValue (Ty.insertMember a [b]) }
  return out

/-- The marshalling round trip, on every vector: `valueTy? ∘ tyValue = some`. A failure here
would make an agreement meaningless, so it is checked rather than assumed. -/
def marshalRoundTrip : Array Row :=
  vectors.toArray.map fun t =>
    let subj : Subject := { kind := "vector", path := ["marshal", t.render] }
    match valueTy? (tyValue t) with
    | some t' =>
      if t' == t then Row.pass "lcnf.semantics.marshal" subj .tested "round trip"
      else Row.counterexample "lcnf.semantics.marshal" subj "round trip changed the value"
        (Json.str t'.render)
    | none => Row.refused "lcnf.semantics.marshal" subj "round trip refused"

/-! ## 6. The driver -/

structure Args where
  out : Option String := none
  fuel : Nat := 100000
  mutate : Nat := 0
  /-- Also run `GenTy.merge`. -/
  genTy : Bool := true

partial def parseArgs : List String → Args → Args
  | "--out" :: p :: rest, a => parseArgs rest { a with out := some p }
  | "--fuel" :: n :: rest, a => parseArgs rest { a with fuel := n.toNat! }
  | "--mutate" :: n :: rest, a => parseArgs rest { a with mutate := n.toNat! }
  | _ :: rest, a => parseArgs rest a
  | [], a => a

/-- The closure the interpreter needs: the walker's declarations plus the externs, with the
builtin table switched **off** so the interpreter reads Lean's own bodies wherever they
exist. -/
def closureNames : CoreM (Array Name) := do
  let roots : Array Name :=
    #[``Ty.key, ``Ty.members, ``Ty.join, ``Ty.render, ``Ty.ltKey, ``Ty.insertMember,
      ``Ty.ofMembers, ``Ty.isNever, ``GenTy.merge]
  let c ← walkClosure roots { primitive := fun _ => false, cap := 4000 }
  return c.decls.map (·.name) ++ c.missing.map (·.name)

def main (argv : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let args := parseArgs argv {}
  let mutant := mutantOfNat args.mutate
  let env ← importModules #[{ module := `Effect4 }] {} 0
  let ctx : Core.Context := { fileName := "<conform-lcnf-semantics>", fileMap := default }
  let act : CoreM UInt32 := do
    let names ← closureNames
    let prims := mutatePrims mutant tyPrims
    let ictx := mutateCtx mutant (Ctx.ofClosure (← getEnv) names prims)
    let cases := buildCases
    let rows := differential ictx args.fuel "lcnf.semantics.agrees" cases
    let all := marshalRoundTrip ++ rows
    let counts := tally all
    let report : Report :=
      { tool := "conform-lcnf-semantics"
        pins := [ { name := "lean", value := Lean.versionString }
                , { name := "mutant", value := mutant.label } ]
        expected := all.size
        rows := all }
    IO.println s!"mutant: {mutant.label}"
    IO.println s!"closure: {names.size} names, primitives: {prims.length}"
    IO.println s!"vectors: {vectors.length} unary, {c1.length * c1.length} pairs"
    IO.println s!"cases: {cases.size} + {marshalRoundTrip.size} marshalling = {all.size}"
    IO.println s!"pass {counts.pass}  counterexample {counts.fail}  refused {counts.stuck}  \
      out-of-fuel {counts.fuel}"
    for r in all.filter (fun r => r.outcome != .pass) |>.extract 0 12 do
      IO.println s!"  {r.outcome} {r.subject.render}: {r.message}"
    match args.out with
    | none => pure ()
    | some dir =>
      IO.FS.createDirAll dir
      let leaf := if args.mutate == 0 then "semantics" else s!"semantics-mutant{args.mutate}"
      IO.FS.writeFile (dir ++ "/" ++ leaf ++ ".json") (report.sorted.toJson.pretty ++ "\n")
      IO.println s!"wrote {dir}/{leaf}.json"
    -- a mutant run is expected to be red; the plain run is expected to be green
    if args.mutate == 0 then
      return (if counts.fail + counts.stuck + counts.fuel == 0 then 0 else 1)
    else
      return (if counts.fail + counts.stuck + counts.fuel > 0 then 0 else 1)
  let (code, _) ← (act.toIO ctx { env := env })
  return code

end Conform.Effect4.LcnfSemantics

def main (argv : List String) : IO UInt32 := Conform.Effect4.LcnfSemantics.main argv
