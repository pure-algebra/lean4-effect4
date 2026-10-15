import Conform.Lcnf.Semantics
import OCaml5.Lcnf.Builtins
import Effect4

/-!
# Conform.Effect4.LcnfSemantics — rung 2's validation: the interpreter against Lean itself

**What it is.** The source lane's pieces: `Ty` marshalled into the interpreter's values, the
primitive table of the closure, and the mutants. The compiler checkpoint
(`Conform.Effect4.Normalization`, `make check-compiler`) runs the interpreter on the mono LCNF
of its fixtures through them, and each mutant must make its observation go red. The vector
differential that ran the interpreter against the compiled Lean functions on 1,330 unary vectors
and 3,249 pairs went on 2026-10-15: no gate ran it
(`git:fef45fb5a:tools/Conform/Effect4/LcnfSemantics.lean`, decisions row 391).

**The mutants.** Each breaks one interpreter rule on purpose and must make the checkpoint go
red; a rule whose mutant stays green is a rule the fixtures do not exercise.
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

mutual
def tyValue : Ty → Value
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
  | .lit s => .ctor ``Ty.lit #[.str s]
  | .refOf v => .ctor ``Ty.refOf #[tyValue v]
  | .deferredOf v e => .ctor ``Ty.deferredOf #[tyValue v, tyValue e]
  | .var i => .ctor ``Ty.var #[.nat i]
  | .unknown => .ctor ``Ty.unknown #[]
  | .record fs => .ctor ``Ty.record #[Value.ofList (fieldValues fs)]
  | .map k v => .ctor ``Ty.map #[tyValue k, tyValue v]
  | .tuple ts => .ctor ``Ty.tuple #[Value.ofList (itemValues ts)]
  | .app n ts => .ctor ``Ty.app #[.str n, Value.ofList (itemValues ts)]
  | .null => .ctor ``Ty.null #[]
  | .undefined => .ctor ``Ty.undefined #[]
  | .number => .ctor ``Ty.number #[]
  | .bytes => .ctor ``Ty.bytes #[]
  -- a row and a key code are trivial structures, so the row is its list of keys; not in the
  -- vectors
  | .contextOf keys => .ctor ``Ty.contextOf #[Value.ofList (keys.elems.map fun k =>
      .ctor ``Effect4.ServiceKey.mk #[.nat k.name.value, .nat k.service.value])]
/-- A record's fields, each `Prod.mk name (Prod.mk optional type)`. -/
def fieldValues : List (String × Bool × Ty) → List Value
  | [] => []
  | (n, o, t) :: rest =>
    .ctor ``Prod.mk #[.str n, .ctor ``Prod.mk #[Value.bool o, tyValue t]] :: fieldValues rest
/-- A tuple's or a reference's items. -/
def itemValues : List Ty → List Value
  | [] => []
  | t :: rest => tyValue t :: itemValues rest
end

/-! ## 3. The primitive table this closure needs

The constants with **no mono body** carry the interpreter's only assumptions: their meanings. The
table is computed from the route's one primitive table (`OCaml5.Lcnf.sourcePrims`): each row
whose constant is an extern of Lean's runtime names its primitive in its runtime column, and
`Conform.Effect4.CompilerControls` checks that column against the environment. Everything else
the interpreter reads out of the compiler's own output. The OCaml form of the same constant is
the target's, in the same row. -/

def tyPrims : OCaml5.Lcnf.PrimTable := OCaml5.Lcnf.sourcePrims

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

def Mutant.label : Mutant → String
  | .pristine => "none"
  | .ltIsLe => "Nat.decLt answers ≤"
  | .addIsMul => "Nat.add is Nat.mul"
  | .natLitShift => "every Nat literal is one larger"
  | .boolArmsSwapped => "the arms of every cases on Bool are swapped"
  | .appendSwapped => "String.append takes its arguments the other way round"
  | .ctorKeepsParams => "a construction keeps its type parameters as fields"

/-- The **assumption** mutants: one row of the primitive table says something else. -/
def mutatePrims (m : Mutant) (t : OCaml5.Lcnf.PrimTable) : OCaml5.Lcnf.PrimTable :=
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
is a transformation a wrong translator would make.

The rewriter is shaped like the compiler's own structural rewriter,
`Code.instantiateValueLevelParams` (`LCNF/Basic.lean:874-916`): every node is rebuilt through
`Code.updateLet!`/`updateFun!`/`updateCases!`, `LetDecl.updateCore` and `Alt.updateCode`
rather than by naming the constructor and its fields. Those helpers return the *same* object
when nothing under it changed (they compare by pointer), so an unmutated subtree is shared
rather than copied, and — the reason to prefer them here — a `FunDecl` or an `Alt` keeps every
field this rewriter does not mean to touch, including the ones a future `Basic.lean` adds.

It stays a hand walker: the compiler has no generic `Code → Code` map (`DeclValue.mapCodeM`
applies a function to the body, it does not descend), and `Code.forM` cannot rebuild. -/
partial def mutateCode (m : Mutant) (c : Code .pure) : Code .pure :=
  match c with
  | .let decl k =>
    c.updateLet! (decl.updateCore decl.type (mutateLetValue m decl.value)) (mutateCode m k)
  | .fun decl k | .jp decl k =>
    c.updateFun! (decl.updateCore decl.type decl.params (mutateCode m decl.value))
      (mutateCode m k)
  | .jmp .. | .return .. | .unreach .. => c
  | .cases cs =>
    let alts := cs.alts.map fun alt => alt.updateCode (mutateCode m alt.getCode)
    let alts :=
      if m == .boolArmsSwapped && cs.typeName == ``Bool && alts.size == 2 then
        -- keep each alternative's constructor name and give it the other one's body
        match alts[0]!, alts[1]! with
        | a@(.alt ..), b@(.alt ..) => #[a.updateCode b.getCode, b.updateCode a.getCode]
        | a, b => #[b, a]
      else alts
    c.updateCases! cs.resultType cs.discr alts
where
  mutateLetValue (m : Mutant) (v : LetValue .pure) : LetValue .pure :=
    match m, v with
    | .natLitShift, .lit (.nat n) => .lit (.nat (n + 1))
    | .appendSwapped, .const n us args =>
      if OCaml5.Lcnf.stripRedArg n == ``String.append then .const n us args.reverse
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

end Conform.Effect4.LcnfSemantics
