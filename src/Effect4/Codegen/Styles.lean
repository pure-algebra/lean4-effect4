import Effect4.Codegen.Forms

/-!
# Codegen.Styles

Foreign target syntax constructed from the printer's syntax and the forms table.
This is printer output, never a second program IR. Rendering lives in Tools.Corpus;
no raw source string is stored as a target expression. Each document is paired with
its original Eff oracle by that driver. The recognizer's gate checks the inverse.
-/

namespace Effect4.Codegen.Styles

open Effect4.Program Effect4.Codegen.Forms

inductive PipeStyle
  | direct | method | function | curried | eta
  deriving DecidableEq, BEq
inductive DurationStyle
  | number | text | millis | seconds | minutes | hours | days | weeks
  deriving DecidableEq, BEq

structure Style where
  pipe : PipeStyle := .direct
  duration : DurationStyle := .number
  lambdas : Bool := false
  omitOptions : Bool := false
  releaseOne : Bool := false
  omitElse : Bool := false
  reverseFields : Bool := false
  /-- Exact head-to-binding map, supplied as data by the driver from the profile. -/
  aliases : List (String × String) := []

mutual
  inductive Expr
    | leaf (value : TypeScript.Expr)
    | call (fn : Expr) (args : List Expr)
    | method (target : Expr) (name : String) (args : List Expr)
    | member (target : Expr) (name : String)
    | generic (fn : Expr) (types : List String)
    | object (fields : List (String × Expr))
    | arr (items : List Expr)
    | lambda (params : List String) (body : Expr)
    | generator (body : List Stmt)
    | arrowBlock (params : List String) (body : List Stmt)
    | cond (test thenB elseB : Expr)
    | atomLambda (shape : LambdaShape)
  inductive Stmt
    | constYield (name : String) (value : Expr)
    | yieldDiscard (value : Expr)
    | ret (value : Expr)
    | ifElse (test : Expr) (thenB elseB : List Stmt) (omitElse : Bool)
    | whileTrue (label : Option String) (body : List Stmt)
    | letInit (name : String) (value : Expr)
    | assign (name : String) (value : Expr)
    | expr (value : Expr)
    | leaf (value : TypeScript.Stmt)
end

def ident (s : String) : Expr := .leaf (.ident s)
def number (n : Nat) : Expr := .leaf (.int n)
def rename (style : Style) (name : String) : String :=
  ((style.aliases.find? (fun pair => pair.1 == name)).map (·.2)).getD name

def head (style : Style) (name : String) : Expr := ident (rename style name)

def duration (style : Style) (n : Nat) : Expr :=
  let builder (unit : String) (divisor : Nat) :=
    if n % divisor == 0 then .call (head style ("Duration." ++ unit)) [number (n / divisor)]
    else .call (head style "Duration.millis") [number n]
  match style.duration with
  | .number => number n
  | .text => .leaf (.str (if n % 1000 == 500 then toString (n / 1000) ++ ".5 seconds" else toString n ++ " millis"))
  | .millis => builder "millis" 1
  | .seconds => builder "seconds" 1000
  | .minutes => builder "minutes" 60000
  | .hours => builder "hours" 3600000
  | .days => builder "days" 86400000
  | .weeks => builder "weeks" 604800000

/-- Only heads whose actual call has the fixed dual arity are restyled here.
Other direct and predicate-dual shapes are retained for the shape fixtures. -/
def applyHead (style : Style) (name : String) (args : List Expr) : Expr :=
  let direct := Expr.call (head style name) args
  let dual := duals.any fun (h, rule) => h == name && match rule with
    | .fixed n => args.length == n
    | _ => false
  match dual, args with
  | true, self :: rest =>
    match style.pipe with
    | .direct => direct
    | .method => .method self "pipe" [.call (head style name) rest]
    | .function => .call (head style "pipe") [self, .call (head style name) rest]
    | .curried => .call (.call (head style name) rest) [self]
    | .eta => .method self "pipe" [.lambda ["_self"] (.call (head style name) (ident "_self" :: rest))]
  | _, _ => direct

mutual
  def mentions (name : String) : TypeScript.Expr → Bool
    | .ident s => s == name
    | .call f xs => mentions name f || mentionsList name xs
    | .method x _ xs => mentions name x || mentionsList name xs
    | .member x _ | .generic x _ | .arrow _ x | .lambda _ x => mentions name x
    | .object fs | .objectML fs | .objectQuoted fs | .objectQuotedML fs | .objectFromEntries fs => mentionsFields name fs
    | .arr xs => mentionsList name xs
    | .generator ss | .arrowBlock _ ss => mentionsStmts name ss
    | .cond a b c => mentions name a || mentions name b || mentions name c
    | _ => false
  def mentionsList (name : String) : List TypeScript.Expr → Bool
    | [] => false | x :: xs => mentions name x || mentionsList name xs
  def mentionsFields (name : String) : List (String × TypeScript.Expr) → Bool
    | [] => false | (_, x) :: xs => mentions name x || mentionsFields name xs
  def mentionsStmts (name : String) : List TypeScript.Stmt → Bool
    | [] => false | x :: xs => mentionsStmt name x || mentionsStmts name xs
  def mentionsStmt (name : String) : TypeScript.Stmt → Bool
    | .constYield _ x | .ret x | .yieldDiscard x | .letInit _ x | .assign _ x | .exprStmt x => mentions name x
    | .ifElse t a b => mentions name t || mentionsStmts name a || mentionsStmts name b
    | .whileTrue _ ss | .labelled _ ss => mentionsStmts name ss
    | .scopedGen _ ss x | .scopedGenMasked _ ss x => mentionsStmts name ss || mentions name x
    | .switch x cases => mentions name x || mentionsCases name cases
    | _ => false
  def mentionsCases (name : String) : List (Nat × List TypeScript.Stmt) → Bool
    | [] => false | (_, ss) :: xs => mentionsStmts name ss || mentionsCases name xs
end

/-- The approved lambda replacement has no branch for takeAndBump. -/
def atom? : String → Option LambdaShape
  | "incr" => lambdaShape .incr
  | "double" => lambdaShape .double
  | "noChange" => lambdaShape .noChange
  | "zeroWhenPositive" => lambdaShape .zeroWhenPositive
  | "takeAndBump" => lambdaShape .takeAndBump
  | _ => none

mutual
  def expression (style : Style) : TypeScript.Expr → Expr
    | .ident s => if style.lambdas then
        match atom? s with | some shape => .atomLambda shape | none => head style s
      else head style s
    | .call (.ident "Effect.sleep") [.int (.ofNat n)] =>
        .call (head style "Effect.sleep") [duration style n]
    | .call (.ident "Effect.acquireRelease") [acquire, .lambda [resource, exit] body] =>
        .call (head style "Effect.acquireRelease") [expression style acquire,
          .lambda (if style.releaseOne && !mentions exit body then [resource] else [resource, exit]) (expression style body)]
    | .call (.ident name) args =>
        let changed := expressions style args
        let skipOptions :=  style.omitOptions &&
            ["Effect.forkChild", "Effect.forkDetach", "Effect.forkIn", "Effect.forkScoped"].contains name &&
            match args.getLast? with
            | some options => options == printForkOptions (defaults (name != "Effect.forkChild"))
            | none => false
        applyHead style name (if skipOptions then changed.dropLast else changed)
    | .call fn args => .call (expression style fn) (expressions style args)
    | .method x name args => .method (expression style x) name (expressions style args)
    | .member x name => .member (expression style x) name
    | .generic fn types => .generic (expression style fn) types
    | .object fs | .objectML fs | .objectQuoted fs | .objectQuotedML fs =>
        .object (if style.reverseFields then (fields style fs).reverse else fields style fs)
    | .arr xs => .arr (expressions style xs)
    | .arrow _ body => .lambda [] (expression style body)
    | .lambda params body => .lambda params (expression style body)
    | .generator body => .generator (statements style body)
    | .arrowBlock params body => .arrowBlock params (statements style body)
    | .cond t a b => .cond (expression style t) (expression style a) (expression style b)
    | x => .leaf x
  def expressions (style : Style) : List TypeScript.Expr → List Expr
    | [] => [] | x :: xs => expression style x :: expressions style xs
  def fields (style : Style) : List (String × TypeScript.Expr) → List (String × Expr)
    | [] => [] | (name, x) :: xs => (name, expression style x) :: fields style xs
  def statement (style : Style) : TypeScript.Stmt → Stmt
    | .constYield name x => .constYield name (expression style x)
    | .yieldDiscard x => .yieldDiscard (expression style x)
    | .ret x => .ret (expression style x)
    | .ifElse t a b => .ifElse (expression style t) (statements style a) (statements style b) (style.omitElse && b.isEmpty)
    | .whileTrue label body => .whileTrue label (statements style body)
    | .letInit name x => .letInit name (expression style x)
    | .assign name x => .assign name (expression style x)
    | .exprStmt x => .expr (expression style x)
    | x => .leaf x
  def statements (style : Style) : List TypeScript.Stmt → List Stmt
    | [] => [] | x :: xs => statement style x :: statements style xs
end

/-- Print one row's own foreign example at its declared surrounding depth. Arguments
are printed before the template inserts binders, so the later reader must weaken them. -/
def Form.foreign (f : Form) (style : Style) (n : Nat) : Option Expr := do
  let args := f.exampleArgs n
  let eff (i depth : Nat) : Option Expr := do
    let p ← args.effects[i]?
    let .ok e := print nativeSignature depth p | none
    some (expression style e)
  let term (i : Nat) : Option Expr := do
    let t ← args.terms[i]?
    some (expression style (printTerm t))
  let call (args : List Expr) := applyHead style f.head args
  let a := "a" ++ toString n
  let result ← match f.id with
    | "void" | "yieldNow" => some (head style f.head)
    | "die" => return call [← term 0]
    | "yieldKey" => do
        let _ ← args.keys[0]?
        -- The driver supplies the declaration for Key; this unit uses its yieldable face.
        some (.generator [.constYield a (ident "Key"), .ret (ident a)])
    | "andThenEffect" | "tapEffect" | "ensuring" => return call [← eff 0 n, ← eff 1 n]
    | "andThenContinuation" | "tapContinuation" => return call [← eff 0 n, .lambda [a] (← eff 1 (n + 1))]
    | "andThenThunk" => return call [← eff 0 n, .lambda [] (← eff 1 n)]
    | "as" => return call [← eff 0 n, ← term 0]
    | "asVoid" => return call [← eff 0 n]
    | "matchCause" => return call [← eff 0 n, .object [("onSuccess", .lambda [a] (← term 0)), ("onFailure", .lambda [a] (← term 1))]]
    | "matchCauseEffect" => return call [← eff 0 n, .object [("onSuccess", .lambda [a] (← eff 1 (n + 1))), ("onFailure", .lambda [a] (← eff 2 (n + 1)))]]
    | "forkChildDefault" | "forkDetachDefault" | "forkScopedDefault" => return call [← eff 0 n]
    | "forkInDefault" => return call [← eff 0 n, ← term 0]
    | "releaseOne" => return call [← eff 0 n, .lambda [a] (← eff 1 (n + 1))]
    | _ => none
  let rec wrap (i remaining : Nat) (body : Expr) : Expr :=
    match remaining with
    | 0 => body
    | m + 1 => applyHead style "Effect.flatMap" [.call (head style "Effect.succeed") [number 3],
        .lambda ["a" ++ toString i] (wrap (i + 1) m body)]
  return wrap 0 n result

#guard atom? "incr" == some .addOne
#guard atom? "takeAndBump" == none

end Effect4.Codegen.Styles
