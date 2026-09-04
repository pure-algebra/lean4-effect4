import Lean

/-!
# OCaml5.Lcnf.Dump

**What it is.** The one door to Lean's own compiler IR. `monoDecl?` fetches the mono-phase
LCNF `Decl` of a constant out of the imported environment, and `sketch` prints the shape of
its `Code` — one line per node, naming every `Code`, `LetValue`, `Arg` and `Alt` constructor
it meets — so a translator's coverage can be read off a dump before a rule is written.

**Depends on.** `Lean` only: `Lean.Compiler.LCNF.PhaseExt.getMonoDecl?` (the `monoExt`
persistent extension, `PhaseExt.lean:112,162`) and `PrettyPrinter.ppDecl'` (`:218`).

**Properties.**
* `monoDecl?` reads, never compiles: what comes back is what `saveMono`
  (`Passes.lean:66-74`) wrote when the module was built, after `normalizeFVarIds`, so a dump
  is deterministic across runs and machines — *by construction*.
* `sketch` is total on pure-phase `Code` and names every constructor of `Code .pure`,
  `LetValue .pure`, `Arg .pure` and `Alt .pure` — *tested* (`tools/LcnfDump.lean` on the
  `Dispatcher` and `RunMachine` functions of `Effect4.Machine.Fibers`).
* Neither entry point mutates the environment: both are read-only `CoreM` — *by
  construction* (`ppMono` runs the printer under `runCompilerWithoutModifyingState`).

**Why mono, not base or impure.** Base still carries type arguments and `Decidable`;
impure has already introduced reference counting, boxing and `reset`/`reuse`. Mono is the
phase where polymorphism is erased (type arguments are `◾`), `Decidable` is `Bool`,
structure projections are `cases` (`StructProjCases.lean`), local functions are lifted
(`LambdaLifting.lean`), and the code is still a pure tree of `let`/`jp`/`cases`/`return` —
exactly the fragment OCaml spells directly.
-/

namespace OCaml5.Lcnf

open Lean Compiler LCNF

/-- The mono-phase LCNF of `declName`, as stored in the imported environment (`monoExt`);
`none` when the constant has no code (an inductive, a constructor, an `extern`, a
`noncomputable`), or when its module was built by a compiler that did not persist the mono
phase. -/
def monoDecl? (declName : Name) : CoreM (Option (Decl .pure)) :=
  getMonoDecl? declName

/-- The base-phase LCNF, for comparison: type arguments still present, `Decidable` not yet
`Bool`. -/
def baseDecl? (declName : Name) : CoreM (Option (Decl .pure)) :=
  getBaseDecl? declName

/-- The compiler's own pretty printer on a mono decl, the same text
`set_option trace.Compiler.saveMono true` prints. Internalises a copy; the environment and
the fresh-name counter are restored afterwards. -/
def ppMono (decl : Decl .pure) : CoreM Format :=
  ppDecl' decl .mono

/-! ## The shape printer

A pure walk. Free variables are referred to by `FVarId` in `return`, `jmp`, `cases`, `fvar`
and `proj`; their binder names live on the declaring node, so the walk carries a map from
`FVarId` to binder name, extended at every `let`, `fun`, `jp`, parameter and alternative.
Names are not unique in LCNF (shadowing is by `FVarId`), which is why the map is keyed on
the id and not the name. -/

/-- The names in scope, by free-variable id. -/
abbrev Names := Std.HashMap FVarId String

/-- The binder name of an id, or the raw id when the walk has not bound it (a dangling
reference, which valid LCNF never has). -/
def Names.get (ns : Names) (id : FVarId) : String :=
  ns.getD id s!"?{id.name}"

/-- Bind a parameter or a let. -/
def Names.bind (ns : Names) (id : FVarId) (n : Name) : Names :=
  ns.insert id n.toString

def Names.bindParams (ns : Names) (ps : Array (Param .pure)) : Names :=
  ps.foldl (fun ns p => ns.bind p.fvarId p.binderName) ns

/-- One argument: `◾` for erased, the name for a variable, `_type` for a type argument. -/
def sketchArg (ns : Names) : Arg .pure → String
  | .erased => "◾"
  | .fvar id => ns.get id
  | .type _ => "_type"

def sketchArgs (ns : Names) (args : Array (Arg .pure)) : String :=
  String.intercalate " " (args.toList.map (sketchArg ns))

/-- One `LetValue`: its constructor and its payload. -/
def sketchLetValue (ns : Names) : LetValue .pure → String
  | .lit (.nat n) => s!"lit.nat {n}"
  | .lit (.str s) => s!"lit.str {repr s}"
  | .lit (.uint8 n) => s!"lit.uint8 {n}"
  | .lit (.uint16 n) => s!"lit.uint16 {n}"
  | .lit (.uint32 n) => s!"lit.uint32 {n}"
  | .lit (.uint64 n) => s!"lit.uint64 {n}"
  | .lit (.usize n) => s!"lit.usize {n}"
  | .erased => "erased"
  | .proj typeName i s => s!"proj {typeName} #{i} {ns.get s}"
  | .const n _ args => s!"const {n} {sketchArgs ns args}"
  | .fvar f args => s!"fvar {ns.get f} {sketchArgs ns args}"

/-- The mono type of a binder, printed as the delaborator would print the `Expr`: mono types
are closed terms over constants, `→`, `lcAny` and `lcErased`, so no local context is needed. -/
def sketchType (e : Expr) : String :=
  toString e

private def indent (n : Nat) : String := "".pushn ' ' (2 * n)

mutual

/-- The lines of a `Code`, at indentation `d`. -/
partial def sketchCode (ns : Names) (d : Nat) : Code .pure → List String
  | .let decl k =>
      (indent d ++ s!"let {decl.binderName} : {sketchType decl.type} := {sketchLetValue ns decl.value}")
        :: sketchCode (ns.bind decl.fvarId decl.binderName) d k
  | .fun decl k =>
      let ns' := ns.bind decl.fvarId decl.binderName
      (indent d ++ s!"fun {decl.binderName}" ++ sketchParams decl.params)
        :: sketchCode (ns'.bindParams decl.params) (d + 1) decl.value
        ++ sketchCode ns' d k
  | .jp decl k =>
      let ns' := ns.bind decl.fvarId decl.binderName
      (indent d ++ s!"jp {decl.binderName}" ++ sketchParams decl.params)
        :: sketchCode (ns'.bindParams decl.params) (d + 1) decl.value
        ++ sketchCode ns' d k
  | .jmp f args => [indent d ++ s!"jmp {ns.get f} {sketchArgs ns args}"]
  | .cases c =>
      (indent d ++ s!"cases {c.typeName} {ns.get c.discr} : {sketchType c.resultType}")
        :: (c.alts.toList.flatMap (sketchAlt ns (d + 1)))
  | .return x => [indent d ++ s!"return {ns.get x}"]
  | .unreach _ => [indent d ++ "unreach"]

/-- One alternative. -/
partial def sketchAlt (ns : Names) (d : Nat) : Alt .pure → List String
  | .default k => (indent d ++ "| _ =>") :: sketchCode ns (d + 1) k
  | .alt ctorName ps k =>
      (indent d ++ s!"| {ctorName}" ++ sketchParams ps ++ " =>")
        :: sketchCode (ns.bindParams ps) (d + 1) k

/-- ` (x : T) (y : U)`. -/
partial def sketchParams (ps : Array (Param .pure)) : String :=
  String.join (ps.toList.map fun p => s!" ({p.binderName} : {sketchType p.type})")

end

/-- The whole declaration: signature line, then the body. -/
def sketch (decl : Decl .pure) : String :=
  let header := s!"decl {decl.name}{sketchParams decl.params} : {sketchType decl.type}"
    ++ (if decl.recursive then " [recursive]" else "")
  let body := match decl.value with
    | .code c => sketchCode (({} : Names).bindParams decl.params) 1 c
    | .extern _ => ["  extern"]
  String.intercalate "\n" (header :: body)

end OCaml5.Lcnf
