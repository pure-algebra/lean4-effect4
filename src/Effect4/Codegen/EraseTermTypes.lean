import Effect4.Codegen.PrintLeaf
import Effect4.Codegen.TargetFold

/-!
# Erase checked types only inside term and cause occurrences

The program eraser calls this module at slots selected by the existing template sorts.
The target fold reconstructs syntax, changing only the approved local call forms.
The inferred fold has two checked callback annotations and a bare head.
The stored fold repeats its accumulator type, whose equality the inverse checks.
No operation row is routed through this local inverse at its program occurrence.
The successful-print syntax equation belongs to exact-codecs, R8.
Target compiler acceptance and host execution remain separate evidence.
-/

set_option autoImplicit false

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

/-- The local inverse runs only inside a term or cause occurrence.
It preserves every stored type except the exact inferred arguments and callback encoding. -/
def callInverse (n : Nat) (x : Expr) : Expr :=
  eraseCauseTermJoin (eraseFoldJoin n (eraseRecordJoin x))

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
