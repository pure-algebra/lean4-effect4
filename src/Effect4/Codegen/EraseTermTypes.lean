import Effect4.Codegen.PrintLeaf
import Effect4.Codegen.TsFold

/-!
# Erase checked types only inside term and cause occurrences

The program eraser calls this module at slots selected by the existing template sorts.
The target syntax's generated fold reconstructs syntax, changing only the approved local call
forms (`mapCalls`).
The inferred fold has two checked callback annotations and a bare head.
The stored fold repeats its accumulator type, whose equality the inverse checks.
No operation row is routed through this local inverse at its program occurrence.
The successful-print syntax equation belongs to exact-codecs, R8.
Target compiler acceptance and host execution remain separate evidence.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open TypeScript

/-- Read every child at the same binder depth. -/
def atDepth {α : Type} (n : Nat) (children : List (Nat → α)) : List α :=
  children.map fun child => child n

/-- A statement spine threads the depth that each declaration returns. -/
def statementSpine : List (Nat → Stmt × Nat) → Nat → List Stmt × Nat
  | [], n => ([], n)
  | statement :: rest, n =>
    let (head, next) := statement n
    let (tail, finalDepth) := statementSpine rest next
    (head :: tail, finalDepth)

/-- The carrier of the call map: an expression or an object entry at a binder depth, and a
statement with the depth after it. -/
def CallCarrier : ExprFam → Type
  | .expr => Nat → Expr
  | .stmt => Nat → Stmt × Nat
  | .objectentry => Nat → ObjectEntry

/-- The constructor algebra of the target syntax's fold (`TsFold`), with a changed call field.
Its consumer is `eraseJoinArgs`. Every other form reconstructs itself from its folded children,
and a lambda or a block extends the binder depth by its parameters. -/
def callAlgebra (call : Nat → Expr → Expr) : ExprAlgebra CallCarrier where
  expr_ident name _ := .ident name
  expr_str value _ := .str value
  expr_int value _ := .int value
  expr_float64Bits bits _ := .float64Bits bits
  expr_bool value _ := .bool value
  expr_jsNull _ := .jsNull
  expr_call fn args n := call n (.call (fn n) (atDepth n args))
  expr_object fields n := .object (fields.map fun (name, value) => (name, value n))
  expr_objectML fields n := .objectML (fields.map fun (name, value) => (name, value n))
  expr_objectQuoted fields n := .objectQuoted (fields.map fun (name, value) => (name, value n))
  expr_objectQuotedML fields n := .objectQuotedML (fields.map fun (name, value) => (name, value n))
  expr_objectFromEntries fields n := .objectFromEntries (fields.map fun (name, value) => (name, value n))
  expr_arr items n := .arr (atDepth n items)
  expr_arrow ty body n := .arrow ty (body n)
  expr_generic fn types n := .generic (fn n) types
  expr_lambda params body ty n := .lambda params (body (n + params.length)) ty
  expr_method receiver name args n := .method (receiver n) name (atDepth n args)
  expr_member receiver name n := .member (receiver n) name
  expr_generator body n := .generator (statementSpine body n).1
  expr_cond test yes no n := .cond (test n) (yes n) (no n)
  expr_arrowBlock params body ty n := .arrowBlock params (statementSpine body (n + params.length)).1 ty
  expr_index target key n := .index (target n) (key n)
  expr_new callee args n := .new (callee n) (atDepth n args)
  expr_objectWith keys entries n := .objectWith keys (atDepth n entries)
  stmt_constYield name value ty n := (.constYield name (value n) ty, n + 1)
  stmt_ret value n := (.ret (value n), n)
  stmt_yieldDiscard value n := (.yieldDiscard (value n), n)
  stmt_letDefinite name ty n := (.letDefinite name ty, n + 1)
  stmt_letInit name value ty n := (.letInit name (value n) ty, n + 1)
  stmt_assign name value n := (.assign name (value n), n)
  stmt_whileTrue label body n := (.whileTrue label (statementSpine body n).1, n)
  stmt_switch scrutinee branches n :=
    (.switch (scrutinee n) (branches.map fun (tag, body) => (tag, (statementSpine body n).1)), n)
  stmt_ifElse test yes no n := (.ifElse (test n) (statementSpine yes n).1 (statementSpine no n).1, n)
  stmt_labelled label body n := (.labelled label (statementSpine body n).1, n)
  stmt_scopedGen name body onExit n := (.scopedGen name (statementSpine body n).1 (onExit n), n + 1)
  stmt_scopedGenMasked name body onExit n :=
    (.scopedGenMasked name (statementSpine body n).1 (onExit n), n + 1)
  stmt_breakTo label n := (.breakTo label, n)
  stmt_continueTo label n := (.continueTo label, n)
  stmt_exprStmt value n := (.exprStmt (value n), n)
  objectentry_property name value n := .property name (value n)
  objectentry_spread value n := .spread (value n)

/-- The target syntax's fold with the call transformation and the lexical binder depth. -/
def mapCalls (call : Nat → Expr → Expr) : Expr → Nat → Expr :=
  cata_expr (callAlgebra call)

end Effect4.Codegen

namespace Effect4.Codegen.EraseTermTypes

open TypeScript

/-- Exact local inverse for checked cause-query annotations, at a term occurrence only.
A program row may use the same head, so the caller must retain the term/program distinction. -/
def eraseCauseTermJoin (x : Expr) : Expr :=
  match x with
  | .call (.generic (.ident name) [.name ["unknown"] [], _]) [input] =>
    if ["causeIsFail", "causeIsDie", "causeIsInterrupt", "causeError"].contains name then
      .call (.ident name) [input]
    else x
  | x => x

/-- The two canonical fold forms carry different accumulator provenance.
The stored form verifies the repeated B; no arbitrary annotation is a marker. -/
def eraseFoldJoin (n : Nat) (x : Expr) : Expr :=
  match x with
  | .call (.ident name) args =>
    if name = "fold" then
      match args with
      | [list, init, step] =>
        match step with
        | .lambda [{ name := accName, type := some _ }, { name := itemName, type := some _ }] body none =>
          if decide (accName = Template.varName n) && decide (itemName = Template.varName (n + 1)) then
            ListFold.write n none list init body
          else x
        | _ => x
      | _ => x
    else x
  | .call (.generic (.ident name) types) args =>
    if name = "fold" then
      match types with
      | [acc, _] =>
        match args with
        | [list, init, step] =>
          match step with
          | .lambda [{ name := accName, type := some repeated }, { name := itemName, type := none }] body none =>
            if decide (accName = Template.varName n) && decide (itemName = Template.varName (n + 1)) &&
                TypeRef.beq repeated acc then ListFold.write n (some acc) list init body
            else x
          | _ => x
        | _ => x
      | _ => x
    else x
  | x => x

/-- Curried record inverses erase R and V, and retain the literal K marker.
The fold visits a receiver application before its containing replacement application. -/
def eraseRecordJoin (x : Expr) : Expr :=
  match x with
  | .call (.generic (.call (.generic (.ident name) [.literal key]) [.str actual]) [_]) [receiver] =>
    if ["recordRequired", "recordOptional", "recordSet"].contains name && decide (key = actual) then
      .call (.call (.generic (.ident name) [.literal key]) [.str actual]) [receiver]
    else x
  | .call (.generic (.call (.call (.generic (.ident "recordSet") [.literal key])
      [.str actual]) [receiver]) [_]) [value] =>
    if decide (key = actual) then Record.writeSet key receiver value
    else x
  | x => x

/-- Inferred two-slot product arguments occur only on these distinct target generic arities.
The pair argument retains the readonly slot tuple; neither inverse admits another runtime arity. -/
def eraseProductJoin (x : Expr) : Expr :=
  match x with
  | .call (.generic (.ident name) types) [first, second] =>
    if name = "tuple" then
      match types with
      | [_, _] => .call (.ident name) [first, second]
      | _ => x
    else if name = "pair" then
      match types with
      | [.tuple [_, _] true] => .call (.ident name) [first, second]
      | _ => x
    else x
  | _ => x

/-- The local inverse runs only inside a term or cause occurrence.
It preserves every stored type except the exact inferred arguments and callback encoding. -/
def callInverse (n : Nat) (x : Expr) : Expr :=
  eraseCauseTermJoin (eraseFoldJoin n (eraseRecordJoin (eraseProductJoin x)))

/-- Erase the selected term annotations through the target-syntax fold.
All children are term occurrences; lambdas extend the actual lexical binder depth. -/
def eraseTerm (n : Nat) (x : Expr) : Expr :=
  Effect4.Codegen.mapCalls callInverse x n

/-- Cause constructors keep their heads; the same fold reaches their term leaves. -/
def eraseCause (n : Nat) (x : Expr) : Expr := eraseTerm n x

/-- Only approved program heads have a node inverse, with exact target generic arities.
Their heads are reserved from operation rows under the existing LawfulSpelling premise. -/
def eraseNode (n : Nat) (x : Expr) : Expr :=
  match x with
  | .call (.ident "Effect.withFiber")
      [.arrowBlock [] [.exprStmt (.call (.generic (.ident "Fiber.runIn") [_, _])
        [receiver, scope]), .ret (.ident "Effect.void")] none] =>
    .call (.ident "Effect.withFiber")
      [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [receiver, scope]),
        .ret (.ident "Effect.void")] none]
  | .call (.generic (.ident "optionCase") [_, _, _, _, _, _, _])
      [input, .arrow none onNone, .lambda ps onSome none] =>
    if decide (ps = Template.params n [0]) then
      .call (.ident "optionCase") [input, .arrow none onNone, .lambda ps onSome none]
    else x
  | .call (.generic (.ident name) [_, .literal tag, _, _, _, _, _, _])
      [input, .str actual, .lambda ps left none, .lambda qs right none] =>
    if ["caseTag", "caseTagR"].contains name && decide (tag = actual) &&
        decide (ps = Template.params n [0]) && decide (qs = Template.params n [0]) then
      .call (.ident name) [input, .str actual, .lambda ps left none, .lambda qs right none]
    else x
  | .call (.generic (.ident name) [_, _]) [input] =>
    if ["Fiber.join", "Fiber.await", "Fiber.interrupt"].contains name then
      .call (.ident name) [input]
    else x
  | .call (.generic (.ident name) [_, _]) [first, second] =>
    if ["Fiber.runIn", "Scope.close"].contains name then
      .call (.ident name) [first, second]
    else x
  | .call (.generic (.ident "Effect.scoped") [_, _, _]) [input] =>
    .call (.ident "Effect.scoped") [input]
  | .call (.generic (.ident "Effect.acquireRelease") [_, _, _, _])
      [acquire, .lambda ps release none] =>
    if decide (ps = Template.params n [0, 1]) then
      .call (.ident "Effect.acquireRelease") [acquire, .lambda ps release none]
    else x
  | .call (.generic (.ident "Effect.forkIn") [_, _, _]) [child, scope, options] =>
    .call (.ident "Effect.forkIn") [child, scope, options]
  | .call (.generic (.ident name) [_]) [child, options] =>
    if ["Effect.forkChild", "Effect.forkDetach", "Effect.forkScoped", "Fiber.interruptAllAs"].contains name then
      .call (.ident name) [child, options]
    else x
  | .call (.generic (.ident name) [_]) [input] =>
    if ["Fiber.interruptAll", "Fiber.awaitAll"].contains name then
      .call (.ident name) [input]
    else x
  | x => x


end Effect4.Codegen.EraseTermTypes
