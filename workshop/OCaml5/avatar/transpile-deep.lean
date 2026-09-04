/-
Seat F3 (2026-09-04): the derived-avatar probe — a *syntax-level* transpiler from the
`Prim`-free function group of `Effect4/Deep/Fibers.lean` to `OCaml5.Ml.Syntax`, rendered by
`OCaml5.Ml.render`. Packet 2 of `docs/research/2026-09-04-seat-f3-ocaml-platform-critique.md` §6.

What it does: parses `Effect4/Deep/Fibers.lean` with Lean's own parser (no elaboration, no
lake), selects the `def`s named on the command line (a `where`-local is addressed as
`outer.local`), translates each `def`'s *surface syntax* to an `Ml.Decl`, applies the
pure-update→mutation pass (`Ml.Passes.mutate`) to the names declared linear, and prints the
OCaml text. Every syntax form it does not know becomes `Expr.hole "<kind>"` so the residue is
visible in the output and countable (`--residue`).

What it deliberately is not: an elaborator. Types are dropped (OCaml infers them against the
generated carriers), instance and implicit binders are skipped, and the decisions a human made
for the hand port are *tables* here, not inference: the constructor table (Lean constructor →
avatar constructor, from the descriptions' prefixes), the method table (`List.*`/`Option.*`
dot-calls → `Stdlib`), the renames (`fiber?` → `fiber_opt`), the anonymous-constructor hints
(which record `⟨a, b⟩` builds, per def), and the linear names per def (the mutate pass's
precondition, `Ml/Passes.lean:20-33`). DIVERGENCE 3 is one rewrite: `m.update x` and
`m.modify …` read as their receiver, because the avatar's records are mutated in place.

Not a lake module: `workshop/OCaml5/avatar` is no `srcDir` (`lakefile.toml`), so this runs
only through `transpile-deep.sh` (`lean --run`, the same olean fallback as `render-deep.sh`).
-/
import Lean
import OCaml5.Render

open Lean Parser
open OCaml5.Ml
abbrev MExpr := OCaml5.Ml.Expr
abbrev MPat := OCaml5.Ml.Pat
instance : Inhabited OCaml5.Ml.Arm := ⟨.mk .wild none .unit⟩
instance : Inhabited OCaml5.Ml.Bind := ⟨{ name := "", body := .unit }⟩

namespace F3

/-! ## The tables: the hand port's decisions, as data -/

/-- Lean constructor (qualified, as written in `Fibers.lean`) → avatar constructor. -/
def ctorTable : List (String × String) :=
  [ ("Task.start", "Tstart"), ("Task.resume", "Tresume"),
    ("Cmd.evaluate", "Cevaluate"), ("Cmd.resume", "Cresume"), ("Cmd.launch", "Claunch"),
    ("Cmd.link", "Clink"), ("Cmd.drainDue", "CdrainDue"),
    ("RunDecision.fire", "Dfire"), ("RunDecision.flush", "Dflush"),
    ("RunDecision.evaluate", "Devaluate"), ("RunDecision.yieldVerdict", "DyieldVerdict"),
    ("RunDecision.answerAsync", "DanswerAsync"), ("RunDecision.interruptFrom", "DinterruptFrom"),
    ("RunDecision.installMiddleware", "DinstallMiddleware"),
    ("Parked.notParked", "NotParked"), ("Parked.withGuard", "WithGuard"),
    ("Observer.resumeAwait", "ResumeAwait"), ("Observer.untrackChild", "UntrackChild"),
    ("Observer.dropScopeFinalizer", "DropScopeFinalizer"), ("Observer.countdown", "Countdown"),
    ("Observer.raceCallback", "RaceCallback"), ("Observer.callback", "Callback"),
    ("Stuck.unknownFiber", "UnknownFiber"), ("Stuck.unknownScope", "UnknownScope"),
    ("Resume.exitsValue", "RexitsValue"), ("Resume.void", "Rvoid"),
    ("Resume.continueWith", "RcontinueWith"),
    ("RunEvent.forked", "Forked"), ("RunEvent.started", "Started"),
    ("RunEvent.scheduledTask", "ScheduledTask"), ("RunEvent.ranTask", "RanTask"),
    ("RunEvent.yieldInjected", "YieldInjected"), ("RunEvent.parkedOn", "ParkedOn"),
    ("RunEvent.resumedWith", "ResumedWith"), ("RunEvent.interruptRecorded", "InterruptRecorded"),
    ("RunEvent.interruptDeferred", "InterruptDeferred"),
    ("RunEvent.childrenInterrupted", "ChildrenInterrupted"),
    ("RunEvent.observerFired", "ObserverFired"), ("RunEvent.scopeLinked", "ScopeLinked"),
    ("RunEvent.scopeClosedOnLink", "ScopeClosedOnLink"), ("RunEvent.raceStarted", "RaceStarted"),
    ("RunEvent.raceLaunched", "RaceLaunched"), ("RunEvent.raceSettled", "RaceSettled"),
    ("RunEvent.exited", "Exited"), ("RunEvent.callback", "CallbackEv"),
    ("Exit.success", "Esuccess"), ("Exit.failure", "Efailure"),
    ("Supervision.MaskMode.interruptible", "Minterruptible"),
    ("Supervision.MaskMode.uninterruptible", "Muninterruptible"),
    ("Supervision.MaskMode.inherit", "Minherit"),
    ("Supervision.ScopeMode.forkIn", "0"), ("Supervision.ScopeMode.fiberRunIn", "1"),
    ("some", "Some"), ("none", "None"), ("Option.some", "Some"), ("Option.none", "None") ]

/-- Lean value names the avatar spells differently. -/
def renameTable : List (String × String) :=
  [ ("fiber?", "fiber_opt"), ("race?", "race_opt"), ("RunFiber.park", "run_fiber_park"),
    ("RunFiber.make", "run_fiber_make"), ("Cause.annotate", "cause_annotate"),
    ("Cause.combine", "cause_combine"), ("Supervision.interruptCause", "cause_interrupt"),
    ("Dispatcher.empty", "Dispatcher.empty ()"), ("Dispatcher.insert", "Dispatcher.insert"),
    ("Dispatcher.enqueue", "Dispatcher.enqueue"), ("Dispatcher.drain", "Dispatcher.drain"),
    ("stepDecision.fire", "fire"), ("stepDecision.flushAll", "flush_all"),
    ("stepDecision.flushRoot", "flush_root"), ("countdownPark.resumePrim", "resume_prim") ]

/-- Which record an anonymous constructor `⟨…⟩` builds, per def: the field names in order. -/
def anonHints : List (String × List String) :=
  [ ("insert", ["priority", "tasks"]), ("empty", ["buckets", "armed"]),
    ("enqueue", ["buckets", "armed"]), ("drain", ["buckets", "armed"]),
    ("launchEntrant", ["start_immediately", "daemon", "mask_mode"]),
    ("countdownPark", ["token", "waiting_on", "remaining", "collected", "resume_with", "fail_fast"]),
    ("injectYield", ["token", "waiting_on", "remaining", "collected", "resume_with", "fail_fast"]) ]

/-- The names the hand port updates in place (the `mutate` precondition), per def. -/
def linearTable : List (String × List String) :=
  [ ("enqueue", ["d"]), ("drain", ["d"]), ("arm", ["m"]), ("disarm", ["m"]),
    ("runloopTop", ["f"]), ("countOp", ["f"]), ("interruptRecord", ["f"]),
    ("fire", ["m", "o"]), ("interruptEach", ["m", "g"]) ]

/-- `List.*`/`Option.*` dot-calls on a local, as the hand port spells them. -/
def methodCall (name : String) (recv : MExpr) (args : List MExpr) : Option MExpr :=
  match name, args with
  | "contains", [a] => some (Expr.call "List.mem" [a, recv])
  | "filter", [f] => some (Expr.call "List.filter" [f, recv])
  | "map", [f] => some (Expr.call "List.map" [f, recv])
  | "find?", [f] => some (Expr.call "List.find_opt" [f, recv])
  | "all", [f] => some (Expr.call "List.for_all" [f, recv])
  | "any", [f] => some (Expr.call "List.exists" [f, recv])
  | "foldl", [f, init] => some (Expr.call "List.fold_left" [f, init, recv])
  | "flatten", [] => some (Expr.call "List.concat" [recv])
  | "length", [] => some (Expr.call "List.length" [recv])
  | "isEmpty", [] => some (.binop "=" recv (.ctor "[]" []))
  | "isSome", [] => some (.binop "<>" recv (.ctor "None" []))
  | "isNone", [] => some (.binop "=" recv (.ctor "None" []))
  | "getD", [d] => some (.matchE recv [.mk (.ctor "Some" [.var "x"]) none (.var "x"),
                                       .mk (.ctor "None" []) none d])
  | "bind", [f] => some (Expr.call "Option.bind" [recv, f])
  | "drain", [] => some (Expr.call "Dispatcher.drain" [recv])
  | "enqueue", [p, t] => some (Expr.call "Dispatcher.enqueue" [recv, p, t])
  -- DIVERGENCE 3: the avatar's records are mutated in place; `update`/`modify` are the receiver
  | "update", [_] => some recv
  | "modify", [id, .fn [x] body] =>
    some (.seq (.matchE (Expr.call "fiber_opt" [recv, id])
                 [.mk (.ctor "Some" [.var x]) none (.seq (Expr.call "ignore" [body]) .unit),
                  .mk (.ctor "None" []) none .unit]) recv)
  | "emit", [es] => some (Expr.call "emit" [recv, es])
  | _, _ => none

/-! ## The translation state -/

structure St where
  defName : String := ""
  locals : List String := []
  residue : List String := []

abbrev M := StateM St

def hole (kind : String) (fill : MExpr := .unit) : M MExpr := do
  modify fun s => { s with residue := s.residue ++ [kind] }
  pure (.hole kind fill)

def isLocal (n : String) : M Bool := do pure ((← get).locals.contains n)

def withLocals (ns : List String) (k : M α) : M α := do
  let saved := (← get).locals
  modify fun s => { s with locals := s.locals ++ ns }
  let r ← k
  modify fun s => { s with locals := saved }
  pure r

def lookupCtor (n : String) : Option String := (ctorTable.find? (·.1 == n)).map (·.2)

/-- A short constructor name (`.fire`, or a bare `some`): the last component of a table key. -/
def lookupCtorShort (n : String) : Option String :=
  lookupCtor n <|> (ctorTable.find? fun p => (p.1.splitOn ".").getLast! == n).map (·.2)

def globalName (n : String) : String :=
  match renameTable.find? (·.1 == n) with
  | some (_, r) => r
  | none => valueName ((n.splitOn ".").getLast!)

/-- A dotted identifier read as a local's field chain, when its head is a local. -/
def fieldChain (parts : List String) : MExpr :=
  match parts with
  | [] => .unit
  | h :: rest => rest.foldl (fun e f =>
      if f == "current" || f == "stack" then .hole ("frame:" ++ f) (.field e (mangleField f))
      else .field e (mangleField f)) (.var (mangleField h))

/-- Count the frame holes a field chain introduced (`fieldChain` is pure, so the residue is
read off the expression afterwards). -/
partial def holesOf : MExpr → List String
  | .hole n e => n :: holesOf e
  | .field e _ => holesOf e
  | .setField e _ v => holesOf e ++ holesOf v
  | .app f as => holesOf f ++ as.foldl (fun a e => a ++ holesOf e) []
  | .binop _ l r => holesOf l ++ holesOf r
  | .ifThen c a b => holesOf c ++ holesOf a ++ holesOf b
  | .letIn _ v b => holesOf v ++ holesOf b
  | .letPat _ v b => holesOf v ++ holesOf b
  | .seq a b => holesOf a ++ holesOf b
  | .matchE s arms => holesOf s ++ arms.foldl (fun a (.mk _ g b) => a ++ (g.map holesOf).getD [] ++ holesOf b) []
  | .functionE arms => arms.foldl (fun a (.mk _ g b) => a ++ (g.map holesOf).getD [] ++ holesOf b) []
  | .fn _ b => holesOf b
  | .record fs => fs.foldl (fun a (_, e) => a ++ holesOf e) []
  | .recordWith b fs => holesOf b ++ fs.foldl (fun a (_, e) => a ++ holesOf e) []
  | .tuple es => es.foldl (fun a e => a ++ holesOf e) []
  | .listLit es => es.foldl (fun a e => a ++ holesOf e) []
  | _ => []

/-- The leftmost identifier under a node (a binder's name). -/
partial def firstIdent (stx : Syntax) : Option String :=
  match stx with
  | .ident _ _ n _ => if n.isAnonymous || n.hasMacroScopes then none else some (toString n)
  | .node _ _ args => args.foldl (fun acc c => acc <|> firstIdent c) none
  | _ => none

/-- The elements of a `(a, b, c)` node: the non-atom leaves of its comma-separated spine. -/
partial def tupleItems (stx : Syntax) : List Syntax :=
  match stx with
  | .node _ k args =>
    if k == nullKind then args.toList.foldl (fun acc c => acc ++ tupleItems c) []
    else [stx]
  | .atom _ _ => []
  | _ => [stx]

/-- The first descendant of a kind. -/
partial def findKind (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.isOfKind k then some stx
  else match stx with
    | .node _ _ args => args.foldl (fun acc c => acc <|> findKind c k) none
    | _ => none

/-- Every descendant of a kind, in order. -/
partial def findAll (stx : Syntax) (k : SyntaxNodeKind) : List Syntax :=
  if stx.isOfKind k then [stx]
  else match stx with
    | .node _ _ args => args.toList.foldl (fun acc c => acc ++ findAll c k) []
    | _ => []

/-! ## Terms -/

mutual

partial def trExpr (stx : Syntax) : M MExpr := do
  match stx with
  | .ident _ _ n _ =>
    let s := toString n
    let parts := s.splitOn "."
    if (← isLocal parts.head!) then
      -- `m.armed.isEmpty`: a method with no arguments on a field chain
      match parts.getLast? with
      | some last =>
        if parts.length > 1 then
          match methodCall last (fieldChain parts.dropLast) [] with
          | some e => pure e
          | none => pure (fieldChain parts)
        else pure (fieldChain parts)
      | none => pure (fieldChain parts)
    else
      match lookupCtor s with
      | some c => pure (.ctor c [])
      | none =>
        match s with
        | "true" => pure (.bool true)
        | "false" => pure (.bool false)
        | _ => pure (.var (globalName s))
  | .node _ k args =>
    if k == ``Term.app then trApp args[0]! (args[1]!.getArgs.toList)
    else if k == ``Term.paren then trExpr args[1]!
    else if k == numLitKind then
      match stx.isNatLit? with
      | some v => pure (.int v)
      | none => hole "num"
    else if k == ``Term.tuple then
      let es ← (tupleItems args[1]!).mapM trExpr
      pure (.tuple es)
    else if k == ``«term[_]» then
      let items := args[1]!.getSepArgs.toList
      pure (.listLit (← items.mapM trExpr))
    else if k == ``Term.anonymousCtor then
      let items := args[1]!.getSepArgs.toList
      let es ← items.mapM trExpr
      match anonHints.find? (·.1 == (← get).defName) with
      | some (_, fields) => pure (.record (fields.zip es))
      | none => pure (.tuple es)
    else if k == ``Term.structInst then trStructInst stx
    else if k == ``termIfThenElse then
      pure (.ifThen (← trExpr args[1]!) (← trExpr args[3]!) (← trExpr args[5]!))
    else if k == ``Term.let then trLet args
    else if k == ``Term.match then trMatch args
    else if k == ``Term.fun then trFun args
    else if k == ``Term.typeAscription then trExpr args[1]!
    else if k == ``Term.proj then
      let recv ← trExpr args[0]!
      if args[2]!.getKind == fieldIdxKind then
        pure (Expr.call (if args[2]![0]!.getAtomVal == "1" then "fst" else "snd") [recv])
      else
        let name := toString args[2]!.getId
        match methodCall name recv [] with
        | some e => pure e
        | none => pure (.field recv (mangleField name))
    else if k == ``Term.dotIdent then
      let n := toString args[1]!.getId
      match lookupCtorShort n with
      | some c => pure (.ctor c [])
      | none => pure (.ctor (ctorName "" n) [])
    else if k == ``«term_++_» then pure (.binop "@" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_::_» then pure (.binop "::" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_=_» then pure (.binop "=" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_≠_» then pure (.binop "<>" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_<_» then pure (.binop "<" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_>_» then pure (.binop ">" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_≤_» then pure (.binop "<=" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_≥_» then pure (.binop ">=" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_+_» then pure (.binop "+" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_-_» then pure (.binop "-" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_&&_» then pure (.binop "&&" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term_||_» then pure (.binop "||" (← trExpr args[0]!) (← trExpr args[2]!))
    else if k == ``«term!_» then pure (Expr.call "not" [← trExpr args[1]!])
    else hole (toString k)
  | _ => hole "atom"

partial def trApp (fn : Syntax) (argStx : List Syntax) : M MExpr := do
  let args ← argStx.mapM trExpr
  match fn with
  | .ident _ _ n _ =>
    let s := toString n
    let parts := s.splitOn "."
    if s == "decide" then pure args.head!
    else if (← isLocal parts.head!) && parts.length > 1 then
      let recv := fieldChain parts.dropLast
      match methodCall parts.getLast! recv args with
      | some e => pure e
      | none => pure (Expr.call (globalName parts.getLast!) (recv :: args))
    else
      match lookupCtor s with
      | some c => pure (.ctor c args)
      | none =>
        if (← isLocal s) then pure (.app (.var (mangleField s)) args)
        else pure (Expr.call (globalName s) args)
  | .node _ k pargs =>
    if k == ``Term.proj then
      let recv ← trExpr pargs[0]!
      let name := toString pargs[2]!.getId
      match methodCall name recv args with
      | some e => pure e
      | none => pure (Expr.call (globalName name) (recv :: args))
    else pure (.app (← trExpr fn) args)
  | _ => pure (.app (← trExpr fn) args)

partial def trStructInst (stx : Syntax) : M MExpr := do
  -- `{ src with f := v, … }` or `{ f := v, … }`
  let args := stx.getArgs
  let srcOpt := args[1]!
  let fieldsNode := args[2]!
  let fields ← fieldsNode[0]!.getSepArgs.toList.mapM fun f => do
    let lval := f[0]!
    let name := toString lval[0]!.getId
    let rhs := findKind f ``Term.structInstFieldDef
    let v ← match rhs with
      | some r => trExpr r.getArgs.back!
      | none => hole "structInstField"
    pure (mangleField name, v)
  if srcOpt.getNumArgs > 0 then
    let src ← trExpr srcOpt[0]![0]!
    pure (.recordWith src fields)
  else pure (.record fields)

partial def trLet (args : Array Syntax) : M MExpr := do
  -- `let` letConfig letDecl `;`? body
  let decl := args[2]![0]!
  let body := args[4]!
  if decl.isOfKind ``Term.letIdDecl then
    let name := (firstIdent decl[0]!).getD "_"
    let binders := decl[1]!.getArgs.toList.filterMap fun b =>
      if b.getKind == identKind then some (toString b.getId) else none
    let value ← withLocals binders (trExpr decl[4]!)
    let value := if binders.isEmpty then value else .fn (binders.map mangleField) value
    let b ← withLocals [name] (trExpr body)
    pure (.letIn (mangleField name) value b)
  else if decl.isOfKind ``Term.letPatDecl then
    let pat ← trPat decl[0]!
    let value ← trExpr decl[4]!
    let names := patVarsOf pat
    let b ← withLocals names (trExpr body)
    pure (.letPat pat value b)
  else hole (toString decl.getKind)

partial def patVarsOf : MPat → List String
  | .var n => [n]
  | .ctor _ ps => ps.foldl (fun a p => a ++ patVarsOf p) []
  | .tuple ps => ps.foldl (fun a p => a ++ patVarsOf p) []
  | .cons h t => patVarsOf h ++ patVarsOf t
  | .record fs => fs.foldl (fun a p => a ++ patVarsOf p.2) []
  | _ => []

/-- A pattern, plus the `n + 1` rewrites it needs (`(var, guard, let)` triples). -/
partial def trPat (stx : Syntax) : M MPat := do
  match stx with
  | .ident _ _ n _ =>
    let s := toString n
    if s == "_" then pure .wild
    else match lookupCtor s with
      | some c => pure (.ctor c [])
      | none => pure (.var (mangleField s))
  | .node _ k args =>
    if k == ``Term.hole then pure .wild
    else if k == ``Term.app then
      let fnName := toString args[0]!.getId
      let ps ← args[1]!.getArgs.toList.mapM trPat
      match lookupCtor fnName with
      | some c => pure (.ctor c ps)
      | none => pure (.ctor (ctorName "" ((fnName.splitOn ".").getLast!)) ps)
    else if k == ``Term.paren then trPat args[1]!
    else if k == ``Term.tuple then
      pure (.tuple (← (tupleItems args[1]!).mapM trPat))
    else if k == ``«term[_]» then
      let items := args[1]!.getSepArgs.toList
      if items.isEmpty then pure (.ctor "[]" []) else pure (.listPat (← items.mapM trPat))
    else if k == ``«term_::_» then pure (.cons (← trPat args[0]!) (← trPat args[2]!))
    else if k == numLitKind then pure (.int (stx.isNatLit?.getD 0))
    else if k == ``Term.anonymousCtor then
      let items ← args[1]!.getSepArgs.toList.mapM trPat
      match anonHints.find? (·.1 == (← get).defName) with
      | some (_, fields) => pure (.record (fields.zip items))
      | none => pure (.tuple items)
    else if k == ``«term_+_» then
      -- `n + 1` as a pattern: bound below by `succPat`
      let v := toString args[0]!.getId
      pure (.var ("succ:" ++ mangleField v))
    else
      modify fun s => { s with residue := s.residue ++ ["pat:" ++ toString k] }
      pure .wild
  | _ => pure .wild

/-- Turn `succ:n` variables into `n when n > 0` with `let n = n - 1` around the body. -/
partial def succPat (p : MPat) (guard : Option MExpr) (body : MExpr) : MPat × Option MExpr × MExpr :=
  match p with
  | .var n =>
    if n.startsWith "succ:" then
      let v := (n.drop 5).toString
      let g := Expr.binop ">" (.var v) (.int 0)
      let guard' := match guard with | some g0 => some (.binop "&&" g0 g) | none => some g
      (.var v, guard', .letIn v (.binop "-" (.var v) (.int 1)) body)
    else (p, guard, body)
  | .tuple ps =>
    let (ps', g, b) := ps.foldr (fun q (acc : List MPat × Option MExpr × MExpr) =>
      let (q', g', b') := succPat q acc.2.1 acc.2.2
      (q' :: acc.1, g', b')) ([], guard, body)
    (.tuple ps', g, b)
  | _ => (p, guard, body)

partial def trAlt (alt : Syntax) : M Arm := do
  -- matchAlt: `|` pats `=>` rhs ; pats is a sepBy of terms
  let pats := alt[1]![0]!.getSepArgs.toList
  let ps ← pats.mapM trPat
  let pat := match ps with | [p] => p | _ => .tuple ps
  let names := patVarsOf pat |>.map fun n => if n.startsWith "succ:" then (n.drop 5).toString else n
  let body ← withLocals names (trExpr alt[3]!)
  let (pat, guard, body) := succPat pat none body
  pure (.mk pat guard body)

partial def trMatch (args : Array Syntax) : M MExpr := do
  -- `match` discrs `with` alts
  let discrs := args[3]!.getSepArgs.toList.map fun d => d[1]!
  let scrut ← match discrs with
    | [d] => trExpr d
    | ds => do pure (.tuple (← ds.mapM trExpr))
  let alts := args[5]![0]!.getArgs.toList
  pure (.matchE scrut (← alts.mapM trAlt))

partial def trFun (args : Array Syntax) : M MExpr := do
  let body := args[1]!
  if body.isOfKind ``Term.basicFun then
    let binders := body[0]!.getArgs.toList
    let names := binders.foldl (fun acc b =>
      match firstIdent b with
      | some n => acc ++ [n]
      | none => acc) []
    let e ← withLocals names (trExpr body[3]!)
    pure (.fn (names.map mangleField) e)
  else if body.isOfKind ``Term.matchAlts then
    let alts := body[0]!.getArgs.toList
    pure (.functionE (← alts.mapM trAlt))
  else hole ("fun:" ++ toString body.getKind)

end

/-- The tail form of the mutate pass, which `Ml.Passes.mutate` does not have: a function whose
tail *returns* the updated linear record (`arm`, `disarm`, `countOp`, `runloopTop`) becomes a
procedure — `{ f with x := v }` at a tail position is `f.x <- v` and a bare `f` is `()`. A
second-half of packet 2: this belongs in `Ml/Passes.lean` beside `mutate`. -/
partial def tailUpdate (linear : List String) : MExpr → MExpr
  | .recordWith (.var f) fs =>
    if linear.contains f then
      fs.foldr (fun (n, v) acc =>
        let v' : MExpr := match v with
          | .recordWith (.var g) inner =>
            if g == f then OCaml5.Ml.Expr.recordWith (.field (.var f) n) inner else v
          | _ => v
        match v' with
        | .recordWith (.field (.var g) n') inner =>
          if g == f then
            inner.foldr (fun (k, w) acc2 => .seq (.setField (.field (.var f) n') k w) acc2) acc
          else .seq (.setField (.var f) n v') acc
        | _ => .seq (.setField (.var f) n v') acc) (.var f)
    else .recordWith (.var f) fs
  | .ifThen c a b => .ifThen c (tailUpdate linear a) (tailUpdate linear b)
  | .matchE s arms => .matchE s (arms.map fun | .mk p g b => .mk p g (tailUpdate linear b))
  | .letIn n v b => .letIn n v (tailUpdate linear b)
  | .letPat p v b => .letPat p v (tailUpdate linear b)
  | e => e

/-! ## Declarations -/

/-- The explicit binder names of a `def` (instance and implicit binders skipped). -/
def binderNames (sig : Syntax) : List String :=
  sig[0]!.getArgs.toList.foldl (fun acc b =>
    if b.isOfKind ``Term.explicitBinder then
      acc ++ (b[1]!.getArgs.toList.filter (·.getKind == identKind)).map (toString ·.getId)
    else acc) []

/-- One `def` (or `where`-local) as a `Bind`. `declValEqns` become extra positional parameters
matched as a tuple; `declValSimple` is the body. -/
def trDef (name : String) (sig : Syntax) (val : Syntax) : M (Bind × List Bind) := do
  modify fun s => { s with defName := name, locals := [] }
  let params := binderNames sig
  let (body, extra, wheres) ← withLocals params do
    if val.isOfKind ``Command.declValSimple then
      let e ← trExpr val[1]!
      pure (e, ([] : List String), val)
    else if val.isOfKind ``Command.declValEqns then
      let alts := val[0]![0]![0]!.getArgs.toList
      let arity := (alts.head?.map fun a => a[1]![0]!.getSepArgs.size).getD 1
      let extra := (List.range arity).map fun i => "x" ++ toString i
      let arms ← withLocals extra (alts.mapM trAlt)
      let scrut := match extra with | [x] => OCaml5.Ml.Expr.var x | xs => .tuple (xs.map OCaml5.Ml.Expr.var)
      pure (.matchE scrut arms, extra, val)
    else pure (.hole ("declVal:" ++ toString val.getKind) .unit, [], .missing)
  let linear := (linearTable.find? (·.1 == name)).map (·.2) |>.getD []
  let body := tailUpdate linear (mutate linear body)
  let allParams := (params ++ extra).map fun p => (mangleField p, (none : Option Ty))
  modify fun s => { s with residue := s.residue ++ holesOf body }
  let main : Bind := { name := globalName name, params := allParams, body := body }
  -- `where` locals: `whereDecls` → `letRecDecl`s
  let mut locals : List Bind := []
  let whereDecls := findKind wheres ``Term.whereDecls
  if let some wd := whereDecls then
    for ld in (findAll wd ``Term.letIdDecl ++ findAll wd ``Term.letEqnsDecl) do
      if ld.isOfKind ``Term.letIdDecl then
        let lname := (firstIdent ld[0]!).getD "_"
        let lparams := ld[1]!.getArgs.toList.foldl (fun acc b =>
          if b.isOfKind ``Term.explicitBinder then
            acc ++ (b[1]!.getArgs.toList.filter (·.getKind == identKind)).map (toString ·.getId)
          else acc) []
        modify fun s => { s with defName := lname, locals := [] }
        let lbody ← withLocals lparams (trExpr ld[4]!)
        let llinear := (linearTable.find? (·.1 == lname)).map (·.2) |>.getD []
        locals := locals ++ [{ name := globalName (name ++ "." ++ lname),
                               params := lparams.map fun p => (mangleField p, none),
                               body := mutate llinear lbody }]
      else if ld.isOfKind ``Term.letEqnsDecl then
        let lname := (firstIdent ld[0]!).getD "_"
        let lparams := ld[1]!.getArgs.toList.foldl (fun acc b =>
          if b.isOfKind ``Term.explicitBinder then
            acc ++ (b[1]!.getArgs.toList.filter (·.getKind == identKind)).map (toString ·.getId)
          else acc) []
        modify fun s => { s with defName := lname, locals := [] }
        let alts := ld[3]![0]!.getArgs.toList
        let arity := (alts.head?.map fun a => a[1]![0]!.getSepArgs.size).getD 1
        let extra := (List.range arity).map fun i => "x" ++ toString i
        let arms ← withLocals (lparams ++ extra) (alts.mapM trAlt)
        let scrut := match extra with | [x] => OCaml5.Ml.Expr.var x | xs => .tuple (xs.map OCaml5.Ml.Expr.var)
        let llinear := (linearTable.find? (·.1 == lname)).map (·.2) |>.getD []
        locals := locals ++ [{ name := globalName (name ++ "." ++ lname),
                               params := (lparams ++ extra).map fun p => (mangleField p, none),
                               body := mutate llinear (.matchE scrut arms) }]
  pure (main, locals)

/-! ## The driver -/

structure Found where
  name : String
  sig : Syntax
  val : Syntax

/-- Every `def` of the file, by name, with its signature and value syntax. -/
unsafe def collect (path : String) : IO (List Found) := do
  let input ← IO.FS.readFile path
  let env ← importModules #[{ module := `Init }] {} 0 (loadExts := true)
  let ictx := mkInputContext input path
  let (_, parserState, messages) ← parseHeader ictx
  let mut pstate := parserState
  let mut out : List Found := []
  let mut done := false
  while !done do
    let (cmd, ps, _) := parseCommand ictx { env := env, options := {} } pstate messages
    pstate := ps
    if cmd.isOfKind ``Command.eoi then done := true
    else
      match cmd with
      | Syntax.node _ ``Command.declaration #[_mods, decl] =>
        if decl.isOfKind ``Command.definition then
          out := out ++ [⟨toString decl[1]![0]!.getId, decl[2]!, decl[3]!⟩]
      | _ => pure ()
  pure out

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  let path := "Effect4/Deep/Fibers.lean"
  let wantResidue := args.contains "--residue"
  let names := args.filter (· != "--residue")
  let found ← collect path
  let mut residues : List (String × List String) := []
  let mut decls : List Decl := []
  for n in names do
    -- `outer.local` addresses a `where`-local of `outer`; `outer` alone renders it with its locals
    let (outer, only) := match n.splitOn "." with
      | [o] => (o, none)
      | [o, l] => (o, some l)
      | _ => (n, none)
    match found.find? (·.name == outer) with
    | none => IO.eprintln s!"transpile-deep: no def named {outer} in {path}"
    | some f =>
      let ((main, locals), st) := (trDef f.name f.sig f.val).run {}
      let binds := match only with
        | none => main :: locals
        | some l => locals.filter (·.name == globalName (outer ++ "." ++ l))
      let isRec := true
      decls := decls ++ [.letD isRec binds]
      residues := residues ++ [(n, st.residue)]
  if wantResidue then
    for (n, r) in residues do
      IO.println s!"{n}\t{r.length}\t{", ".intercalate r}"
  else
    IO.println (moduleText decls)

end F3

unsafe def main (args : List String) : IO Unit := F3.main args
