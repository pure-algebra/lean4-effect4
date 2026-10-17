import Lean
import OCaml5.Lcnf.Dump

/-!
# OCaml5.Lcnf.Gallina — Lean's compiler IR printed as Rocq, for proofs about Lean's own code

**What it is.** The second printer of the LCNF route. The first writes OCaml from the mono phase
(`OCaml5.Lcnf.Translate`); this one writes Gallina from the base phase, so that a Rocq development
proves facts of Lean's definitions and not of a hand copy. It prints a *skeleton*: the
declarations a spec names print as `Fixpoint`s and `Definition`s, the types it names as
`Inductive`s, and every other constant the skeleton calls prints as a Section `Variable` typed from
its Lean signature. The program types come from the generated `Eff_types.v` (rocq-of-ocaml over
`ocaml/eff/eff_types.ml`), so a constructor of `Effect4.Program.Eff` is `Eff_succeed` here as it
is there.

**Why the base phase.** The mono phase lowers a match on `Nat` to `Nat.decEq` and `Nat.sub`, and
lifts local functions to top-level ones that call their parent; Rocq's guard checker refuses both.
The base phase keeps `cases n | Nat.zero | Nat.succ n'` and local `fun`s, so a recursive call
stays on a variable its match binds, which is what the guard checker reads.

**Naturals.** A natural the code cases on as `zero`/`succ`, a successor field, and every argument or
parameter position a counter flows to or from, print as Rocq `nat`: budget counters, which recurse
structurally. Every other natural prints as `int` (Z), as the generated program types spell
Lean's `Nat`.

**Depends on.** `Lean` and `OCaml5.Lcnf.Dump` (`baseDecl?`, the persisted base phase).

**Properties.**
* Every printed declaration is the base-phase code of its Lean declaration, node for node: a `let`
  as `let`, a `fun` and a join point as a local `fun`, a `jmp` as an application, `cases` as
  `match`, `return` as the variable — *by construction*.
* A constant outside the spec is never inlined or copied: it is one Section `Variable` —
  *by construction*.
* Names are per declaration: LCNF numbers its variables per declaration, so the printer's map from
  variables to names is rebuilt for each — *by construction*.
* A recursive declaration names its structural argument, the parameter its first `cases` reads;
  Rocq's guard checker decides the rest — *tested* (the generated `Skeleton.v` of
  `Effect4.Run.Tree` compiles under Rocq 9.0.1; `docs/research/2026-10-16-native-kit/README.md`).
-/

namespace OCaml5.Lcnf.Gallina

open Lean Compiler LCNF

/-- What to print: the skeleton's declarations in dependency order, its own types, the Rocq names
of the other types it mentions, the types left abstract, and the file's header lines. -/
structure Spec where
  decls : List Name
  types : List Name
  knownTypes : List (Name × String)
  abstractTypes : List String
  requires : List String

/-- The constructor names the Rocq standard library and the generated types use. -/
def ctorRocq (env : Environment) (n : Name) : Option String :=
  match n with
  | ``Option.some => some "Some" | ``Option.none => some "None"
  | ``List.cons => some "cons" | ``List.nil => some "nil"
  | ``Bool.true => some "true" | ``Bool.false => some "false"
  | ``Prod.mk => some "pair" | ``PUnit.unit => some "tt" | ``Unit.unit => some "tt"
  | ``Nat.zero => some "O" | ``Nat.succ => some "S"
  | _ =>
    if env.isConstructor n then
      match n.getPrefix with
      | .str _ ty => some s!"{ty}_{n.getString!}"
      | _ => none
    else none

/-- A Rocq identifier for a Lean function: its last component, with a prefix for a helper
namespace (`Tree.Eval.push` is `eval_push`). -/
def fnRocq (n : Name) : String :=
  match n with
  | .str (.str _ ns) s =>
    let s := (s.replace "?" "_opt").replace "'" "_"
    if ns == "Eval" then "eval_" ++ s else s
  | _ => "f"

/-- A local name: `v_` and the binder's characters, each non-alphanumeric one as `_`. -/
def localName (n : Name) : String :=
  "v_" ++ String.ofList ((toString n).toList.map fun c => if c.isAlphanum then c else '_')

/-- A Lean type as a Rocq type; `counter` says a natural is a budget counter. -/
partial def rocqTy (spec : Spec) (counter : Bool) (e : Expr) : String :=
  let e := e.consumeMData
  match e with
  | .forallE _ d b _ => s!"({rocqTy spec false d} -> {rocqTy spec counter b})"
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn with
    | .const ``Nat _ => if counter then "nat" else "int"
    | .const n _ =>
      match spec.knownTypes.lookup n with
      | some r =>
        if args.isEmpty then r else s!"({r} {" ".intercalate (args.toList.map (rocqTy spec false))})"
      | none => s!"(* {n} *) unknown"
    | _ => s!"(* {e} *) unknown"

/-- The printer's state for one declaration: a name for each variable, and the counters. -/
structure Locals where
  names : Std.HashMap FVarId String := {}
  counters : Std.HashSet FVarId := {}

def Locals.name (l : Locals) (f : FVarId) : String := (l.names.get? f).getD "v_unbound"

def Locals.bind (l : Locals) (f : FVarId) (n : Name) : Locals :=
  { l with names := l.names.insert f (localName n) }

def Locals.bindParams (l : Locals) (ps : Array (Param .pure)) : Locals :=
  ps.foldl (fun l p => l.bind p.fvarId p.binderName) l

/-- Name every variable a code declares, and mark the counters it shows. -/
partial def scan (l : Locals) : Code .pure → Locals
  | .let d k => scan (l.bind d.fvarId d.binderName) k
  | .fun d k | .jp d k => scan (scan ((l.bind d.fvarId d.binderName).bindParams d.params) d.value) k
  | .cases c =>
    let l := if c.typeName == ``Nat then { l with counters := l.counters.insert c.discr } else l
    c.alts.foldl (fun l alt => match alt with
      | .alt n ps code =>
        let l := l.bindParams ps
        let l := if n == ``Nat.succ then
          ps.foldl (fun l p => { l with counters := l.counters.insert p.fvarId }) l else l
        scan l code
      | .default code => scan l code
      | _ => l) l
  | _ => l

/-- The global constants a code calls, with each call's variable arguments by position. -/
partial def calls : Code .pure → List (Name × Array (Option FVarId))
  | .let d k =>
    (match d.value with
      | .const n _ args => [(n, args.map fun | .fvar f => some f | _ => none)]
      | _ => []) ++ calls k
  | .fun d k | .jp d k => calls d.value ++ calls k
  | .cases c => c.alts.toList.flatMap fun
      | .alt _ _ code => calls code
      | .default code => calls code
      | _ => []
  | _ => []

def argName (l : Locals) : Arg .pure → Option String
  | .fvar f => some (l.name f)
  | _ => none

def app (fn : String) (args : List String) : String :=
  if args.isEmpty then fn else s!"({fn} {" ".intercalate args})"

/-- A structure's projection by index, when the spec generates the structure. -/
def projName (env : Environment) (typeName : Name) (idx : Nat) : String :=
  match getStructureInfo? env typeName with
  | some info =>
    match info.fieldNames[idx]? with
    | some f => s!"{(fnRocq typeName).toLower}_{f}"
    | none => s!"proj_{idx}"
  | none => if typeName == ``Prod then (if idx == 0 then "fst" else "snd") else s!"proj_{idx}"

def valueText (env : Environment) (l : Locals) (d : LetDecl .pure) : String :=
  match d.value with
  | .lit (.nat n) => if l.counters.contains d.fvarId then toString n else s!"{n}%Z"
  | .lit (.str s) => s!"\"{s}\"%string"
  | .lit _ | .erased => "tt"
  | .proj tn idx s => s!"({projName env tn idx} {l.name s})"
  | .const n _ args =>
    let as := args.toList.filterMap (argName l)
    app ((ctorRocq env n).getD (fnRocq n)) as
  | .fvar f args => app (l.name f) (args.toList.filterMap (argName l))
  | _ => "tt"

def paramText (spec : Spec) (l : Locals) (p : Param .pure) : String :=
  s!"({l.name p.fvarId} : {rocqTy spec (l.counters.contains p.fvarId) p.type})"

/-- A code as a Gallina expression, indented by `ind` after each line break. -/
partial def codeText (env : Environment) (spec : Spec) (l : Locals) (ind : String) :
    Code .pure → String
  | .let d k => s!"let {l.name d.fvarId} := {valueText env l d} in\n{ind}{codeText env spec l ind k}"
  | .fun d k =>
    let ps := " ".intercalate (d.params.toList.map (paramText spec l))
    s!"let {l.name d.fvarId} := (fun {ps} =>\n{ind}    {codeText env spec l (ind ++ "    ") d.value}) in\n{ind}{codeText env spec l ind k}"
  | .jp d k =>
    let ps := if d.params.isEmpty then "(_ : unit)"
      else " ".intercalate (d.params.toList.map (paramText spec l))
    s!"let {l.name d.fvarId} := (fun {ps} =>\n{ind}    {codeText env spec l (ind ++ "    ") d.value}) in\n{ind}{codeText env spec l ind k}"
  | .jmp f args =>
    let as := args.toList.filterMap (argName l)
    app (l.name f) (if as.isEmpty then ["tt"] else as)
  | .return f => l.name f
  | .unreach _ => "ltac:(exact (False_rect _ _))"
  | .cases c =>
    let arms := c.alts.toList.map fun
      | .alt n ps code =>
        let pat := match ctorRocq env n with
          | some ctor =>
            if ps.isEmpty then ctor
            else s!"{ctor} {" ".intercalate (ps.toList.map fun (p : Param .pure) => l.name p.fvarId)}"
          | none => "_"
        s!"{ind}| {pat} =>\n{ind}    {codeText env spec l (ind ++ "    ") code}"
      | .default code => s!"{ind}| _ =>\n{ind}    {codeText env spec l (ind ++ "    ") code}"
      | _ => ""
    s!"match {l.name c.discr} with\n{"\n".intercalate arms}\n{ind}end"

/-- The parameter a declaration recurses on: the scrutinee of its first `cases` on a parameter. -/
partial def structArg (ps : Array (Param .pure)) : Code .pure → Option FVarId
  | .let _ k | .fun _ k | .jp _ k => structArg ps k
  | .cases c => if ps.any (·.fvarId == c.discr) then some c.discr else none
  | _ => none

/-- A type the spec generates, as an `Inductive`, with a projection per field of a structure. -/
def typeText (env : Environment) (spec : Spec) (n : Name) : Except String String := do
  let some (.inductInfo ti) := env.find? n | .error s!"{n} is no inductive"
  let short := (spec.knownTypes.lookup n).getD (fnRocq n)
  let mut out := s!"Inductive {short} : Set :=\n"
  for c in ti.ctors do
    let some (.ctorInfo ci) := env.find? c | .error s!"{c} is no constructor"
    let rec fields : Expr → List String
      | .forallE _ d b _ => rocqTy spec false d :: fields b
      | _ => []
    out := out ++ s!"| {(ctorRocq env c).getD "C"} : {" -> ".intercalate (fields ci.type ++ [short])}\n"
  out := out ++ ".\n"
  if let some info := getStructureInfo? env n then
    let some ctor := ti.ctors.head? | .error s!"{n} has no constructor"
    for i in [:info.fieldNames.size] do
      let vars := (List.range info.fieldNames.size).map fun j => if j == i then "x" else "_"
      out := out ++ s!"Definition {projName env n i} (s : {short}) := match s with {(ctorRocq env ctor).getD "C"} {" ".intercalate vars} => x end.\n"
  return out

/-- **The skeleton as one Rocq file.** -/
def render (spec : Spec) (header : String) : CoreM String := do
  let env ← getEnv
  let mut decls : Array (Decl .pure) := #[]
  for n in spec.decls do
    match ← OCaml5.Lcnf.baseDecl? n with
    | some d => decls := decls.push d
    | none => throwError s!"Gallina: {n} has no base-phase code"
  -- the counters, per declaration and by parameter position, to a fixed point across calls
  let localsOf (d : Decl .pure) (cps : Std.HashSet Nat) : Locals := Id.run do
    let mut l := (({} : Locals).bindParams d.params)
    if let .code c := d.value then l := scan l c
    for i in [:d.params.size] do
      if cps.contains i then l := { l with counters := l.counters.insert d.params[i]!.fvarId }
    return l
  let mut cps : Std.HashMap Name (Std.HashSet Nat) := {}
  for _ in [:decls.size + 2] do
    for d in decls do
      let mut l := localsOf d ((cps.get? d.name).getD {})
      if let .code c := d.value then
        for (callee, args) in calls c do
          if let some cd := decls.find? (·.name == callee) then
            for i in [:min args.size cd.params.size] do
              if let some a := args[i]! then
                let set := (cps.get? callee).getD {}
                if l.counters.contains a then cps := cps.insert callee (set.insert i)
                if set.contains i then l := { l with counters := l.counters.insert a }
      for i in [:d.params.size] do
        if l.counters.contains d.params[i]!.fvarId then
          cps := cps.insert d.name (((cps.get? d.name).getD {}).insert i)
  -- the variables: every constant the skeleton calls that it neither defines nor constructs
  let defined : NameSet := spec.decls.foldl (·.insert ·) {}
  let mut vars : Array Name := #[]
  for d in decls do
    if let .code c := d.value then
      for (n, _) in calls c do
        if !defined.contains n && (ctorRocq env n).isNone && !vars.contains n then
          vars := vars.push n
  -- the mutual groups: declarations that reach one another through calls
  let callees (d : Decl .pure) : List Name := match d.value with
    | .code c => (calls c).map (·.1) |>.filter defined.contains
    | _ => []
  let reaches (a b : Name) : Bool := Id.run do
    let mut seen : NameSet := {}
    let mut todo := [a]
    let mut found := false
    for _ in [:decls.size * decls.size + 1] do
      match todo with
      | [] => break
      | x :: rest =>
        todo := rest
        if !seen.contains x then
          seen := seen.insert x
          let next := (decls.find? (·.name == x)).map callees |>.getD []
          if next.contains b then found := true
          todo := next ++ todo
    return found
  let mut out := header ++ "\n\n" ++ "\n".intercalate spec.requires ++ "\n\nSection Skeleton.\n\n"
  out := out ++ s!"Variables {" ".intercalate spec.abstractTypes} : Set.\n\n"
  for t in spec.types do
    match typeText env spec t with
    | .ok text => out := out ++ text ++ "\n"
    | .error e => throwError e
  for v in vars do
    let some info := env.find? v | throwError s!"Gallina: no constant {v}"
    out := out ++ s!"Variable {fnRocq v} : {rocqTy spec false info.type}.\n"
  out := out ++ "\n"
  let mut printed : NameSet := {}
  for d in decls do
    if printed.contains d.name then continue
    let group := decls.filter fun e => e.name == d.name || (reaches d.name e.name && reaches e.name d.name)
    let mut first := true
    for g in group do
      printed := printed.insert g.name
      let l := localsOf g ((cps.get? g.name).getD {})
      let .code c := g.value | throwError s!"Gallina: {g.name} is extern"
      let recursive := (callees g).any fun n => group.any (·.name == n)
      let sa := if recursive then (structArg g.params c).map fun f => s!" \{struct {l.name f}}" else none
      let kw := if !first then "with" else if recursive then "Fixpoint" else "Definition"
      let mut t := g.type
      for _ in g.params do
        if let .forallE _ _ b _ := t then t := b
      out := out ++ s!"{kw} {fnRocq g.name} {" ".intercalate (g.params.toList.map (paramText spec l))}{sa.getD ""} : {rocqTy spec false t} :=\n  {codeText env spec l "  " c}\n"
      first := false
    out := out ++ ".\n\n"
  return out ++ "End Skeleton.\n"

/-- **The call tree's control skeleton** (`Effect4.Run.Tree`): the spec of the generated
`Skeleton.v`. The evaluator (`Tree.Eval`) is variables; the program types are `Eff_types.v`'s. -/
def treeSpec : Spec where
  decls := [`Effect4.Run.Tree.bind, `Effect4.Run.Tree.andThen, `Effect4.Run.Tree.loop,
    `Effect4.Run.Tree.whileRounds, `Effect4.Run.Tree.bodiesOf, `Effect4.Run.Tree.level,
    `Effect4.Run.Tree.statements, `Effect4.Run.Tree.unfolded, `Effect4.Run.Tree.ofProgram]
  types := [`Effect4.Run.Tree, `Effect4.Run.Tree.Frame]
  knownTypes := [
    (`Effect4.Run.Tree, "tree"), (`Effect4.Run.Tree.Frame, "frame"),
    (`Effect4.Store.Val, "val_"), (`Effect4.Machine.Val, "val_"), (`Effect4.Program.Term, "term"),
    (`Effect4.Program.Eff, "eff"), (`Effect4.Program.Stmts, "stmts"), (`Effect4.Program.Effs, "effs"),
    (`Effect4.Program.NativeOp, "native_op"), (`Effect4.Exit, "exit_"), (`Effect4.Cause, "cause"),
    (`Effect4.Machine.Err, "err"), (`Effect4.Machine.Defect, "defect"), (`Effect4.FiberId, "int"),
    (`Effect4.Program.Row, "row"), (`Effect4.Program.Decision, "decision"),
    (`Effect4.Program.CauseTerm, "cause_term"), (`Effect4.Program.Ty, "ty"),
    (`Effect4.Machine.SyncOp, "sync_op"), (`Effect4.Machine.Ctx, "ctx"),
    (`Effect4.Machine.ExitV, "(exit_ val_ err defect int unit)"),
    (`Effect4.Machine.CauseV, "(cause err defect int unit)"),
    (`Effect4.Program.NativeEff, "(eff native_op)"), (`Effect4.Program.RowTable, "(list row)"),
    (`Effect4.Run.Tree.Unfold, "(eff native_op -> list val_ -> list frame -> ctx -> tree)"),
    (``List, "list"), (``Option, "option"), (``Prod, "prod"), (``Bool, "bool"),
    (``Unit, "unit"), (``PUnit, "unit")]
  abstractTypes := ["sync_op", "ctx"]
  requires := ["From Stdlib Require Import List ZArith String.", "Import ListNotations.",
    "Require Import RocqOfOCaml.RocqOfOCaml.", "Require Import E4.Eff_types."]

end OCaml5.Lcnf.Gallina
