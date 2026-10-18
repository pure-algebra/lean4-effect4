module

public meta import Lean

/-!
# Tool.RequestSyntax — the tool's requests and their method keys, from one declaration

A tool method is one case of `Action` or `Query` (`Tool/Protocol.lean`). `tool_requests` declares
the two sums from their cases, the request over them, and beside them the method keys read off
the same cases:

- `MethodKey`, one constructor for each case, in order, the actions first;
- `MethodKey.all`, every key in that order;
- `MethodKey.kind`, an action or a query, by the sum that holds the case;
- `MethodKey.caseName`, the case's constructor name: the `_tag` its codec writes;
- `MethodKey.name`, the method's wire name: the case's name, or the `wire` name written at the
  case where its name cannot be it (`open` is a keyword of Lean, so `Action.open_` is written
  `wire "open"`);
- `MethodKey.name_nodup`, that no two methods share a wire name, decided where the keys are made;
- `Request.methodKey`, the key of a request.

So one declaration owns the cases and their wire names. A new case is a new key, and every
function that is exhaustive over the keys (a method's description and its hints,
`Tool/Methods.lean`) refuses to elaborate until it names the new key. A wire name written twice
refuses the whole declaration before anything is declared (`repeatedWire`), so no method shadows
another. Two cases with one name are refused by Lean, as two constructors of `MethodKey`.

The expansion is ordinary syntax: no file is written, and Lake rebuilds the declarations with their
input. The declarations land in the namespace where the command is written (`Effect4.Tool`, in
`Tool/Protocol.lean`), and the macro's own helpers stay in `Effect4.Tool.RequestSyntax`. The macro
reads syntax only. It never renders a name with `Name.toString`, and it stays inside the axiom
ceiling `[propext, Quot.sound]`.
-/

public meta section

namespace Effect4.Tool.RequestSyntax

open Lean

/-- One case of a request sum: its docstring, its name, its fields, and its wire name where its
name cannot be it. -/
syntax toolCase := (docComment)? "| " ident (ppSpace bracketedBinder)* (&" wire " str)?

/-- `tool_requests actions [ … ] queries [ … ]`: the request sums `Action` and `Query`, the
request `Request` over them, and the method keys read off their cases. -/
syntax (name := toolRequests) "tool_requests " &"actions" " [" toolCase+ "]"
  &"queries" " [" toolCase+ "]" : command

/-- A constructor's own name, without `Name.toString`'s escaping. -/
def ctorString : Name → String
  | .str _ s => s
  | _ => ""

/-- One case, as the macro reads it. -/
structure ToolCase where
  doc : Option (TSyntax ``Lean.Parser.Command.docComment)
  id : Ident
  binders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder
  wire : TSyntax `str
  sum : Name
  request : Name
  kind : Name

/-- A string literal as written, its quotes included: two wire names written alike are one. -/
def litText (s : TSyntax `str) : String :=
  match s.raw with
  | .atom _ text => text
  | .node _ _ args =>
    match args.toList with
    | [.atom _ text] => text
    | _ => ""
  | _ => ""

/-- The first case whose wire name a later case writes again: that later case. -/
def repeatedWire : List ToolCase → Option ToolCase
  | [] => none
  | c :: rest =>
    match rest.find? fun d => litText d.wire == litText c.wire with
    | some d => some d
    | none => repeatedWire rest

/-- Read one case of the sum `sum`, held by the request's constructor `request`, of kind `kind`. -/
def readToolCase (sum request kind : Name) (stx : Syntax) : MacroM ToolCase := do
  match stx with
  | `(toolCase| $[$doc?]? | $id:ident $bs:bracketedBinder* $[wire $w?]?) =>
    return { doc := doc?, id, binders := bs, sum, request, kind,
             wire := w?.getD (Syntax.mkStrLit (ctorString id.getId)) }
  | _ => Macro.throwUnsupported

set_option hygiene false in
macro_rules
  | `(tool_requests actions [ $as:toolCase* ] queries [ $qs:toolCase* ]) => do
    let actions ← as.mapM (readToolCase `Action `Request.act `MethodKind.action)
    let queries ← qs.mapM (readToolCase `Query `Request.ask `MethodKind.query)
    let ctorOf (c : ToolCase) : MacroM (TSyntax ``Lean.Parser.Command.ctor) :=
      match c.doc with
      | some d => `(Lean.Parser.Command.ctor| $d:docComment | $(c.id):ident $(c.binders)*)
      | none => `(Lean.Parser.Command.ctor| | $(c.id):ident $(c.binders)*)
    let actionCtors ← actions.mapM ctorOf
    let queryCtors ← queries.mapM ctorOf
    let cases := actions ++ queries
    if let some c := repeatedWire cases.toList then
      Macro.throwErrorAt c.id "this case's wire name is another method's: two methods would share it"
    let keyIdent (c : ToolCase) : Ident := mkIdent (`MethodKey ++ c.id.getId)
    let keyCtors ← cases.mapM fun c => `(Lean.Parser.Command.ctor| | $(c.id):ident)
    let all : Array Term := cases.map fun c => (keyIdent c : Term)
    let nameAlts ← cases.mapM fun c =>
      `(Lean.Parser.Term.matchAltExpr| | $(keyIdent c):ident => $(c.wire):str)
    let caseAlts ← cases.mapM fun c =>
      `(Lean.Parser.Term.matchAltExpr| | $(keyIdent c):ident =>
          $(Syntax.mkStrLit (ctorString c.id.getId)):str)
    let kindAlts ← cases.mapM fun c =>
      `(Lean.Parser.Term.matchAltExpr| | $(keyIdent c):ident => $(mkIdent c.kind):ident)
    let requestAlts ← cases.mapM fun c =>
      `(Lean.Parser.Term.matchAltExpr|
        | $(mkIdent c.request):ident ($(mkIdent (c.sum ++ c.id.getId)):ident ..) =>
          $(keyIdent c):ident)
    `(inductive Action where $actionCtors:ctor*
      inductive Query where $queryCtors:ctor*
      inductive Request where
        | act (a : Action)
        | ask (q : Query)
      /-- **A method's key**: one for each case of `Action` and of `Query`, in order. -/
      inductive MethodKey where $keyCtors:ctor* deriving DecidableEq
      /-- Every method's key, the actions first. -/
      def MethodKey.all : List MethodKey := [$all,*]
      /-- A method's wire name: its case's name, or the `wire` name written at the case. -/
      def MethodKey.name (k : MethodKey) : String := match k with $nameAlts:matchAlt*
      /-- A method's case name: the `_tag` its codec writes. -/
      def MethodKey.caseName (k : MethodKey) : String := match k with $caseAlts:matchAlt*
      /-- A method's kind, by the sum that holds its case. -/
      def MethodKey.kind (k : MethodKey) : MethodKind := match k with $kindAlts:matchAlt*
      /-- No two methods share a wire name: decided where the keys are made. -/
      theorem MethodKey.name_nodup : (MethodKey.all.map MethodKey.name).Nodup := by decide
      /-- A request's method key. -/
      def Request.methodKey (r : Request) : MethodKey := match r with $requestAlts:matchAlt*)

end Effect4.Tool.RequestSyntax
