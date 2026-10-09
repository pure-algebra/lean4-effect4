module

public meta import Effect4.Schema.FieldRef.Elab
public import Effect4.Step

/-!
# A record step by field name

`record_step% { id := request, hint := notification }` constructs a record step at the
expected record schema. The schema owns field order and field types. An author supplies each
required field once, in any order. The macro emits `StepFields` data in schema order.

Name lookup uses the same schema reader as `field_ref%`. Unknown, repeated, missing, optional,
and opaque fields refuse before child terms elaborate. Kernel checking validates every child
against its field type. This module stores no function in a step.
-/

public meta section

namespace Effect4.Modules.Step.Elab

open Lean Meta Elab Term
open Effect4.Schema.FieldRef.Elab (entries)

/-- A required record value, with fields supplied by name in any order. -/
syntax (name := recordStepStx) "record_step% " "{" (ident " := " term),* "}" : term

@[term_elab recordStepStx]
def elabRecordStep : TermElab := fun stx expected? => do
  match stx with
  | `(record_step% { $[$names:ident := $values:term],* }) =>
    tryPostponeIfNoneOrMVar expected?
    let Option.some expected := expected?
      | throwErrorAt stx "record_step%: the expected type must be a known record Step"
    let expected ← whnfR (← instantiateMVars expected)
    unless expected.isAppOfArity ``Effect4.Modules.Step 2 do
      throwErrorAt stx "record_step%: the expected type {expected} is not a Step"
    let schema ← whnf (← instantiateMVars (expected.getArg! 1))
    unless schema.isAppOfArity ``Effect4.Program.Ty.record 1 do
      if schema.hasExprMVar then tryPostpone
      throwErrorAt stx "record_step%: the expected step must return a known record"
    let fieldsExpr ← instantiateMVars (schema.getArg! 0)
    let Option.some fields ← entries 4096 fieldsExpr | do
      if fieldsExpr.hasExprMVar then tryPostpone
      throwErrorAt stx "record_step%: the schema does not reduce to a list of literal fields"
    for entry in fields do
      if (fields.filter (fun field => field.name == entry.name)).length > 1 then
        throwErrorAt stx "record_step%: two fields of the schema are named {entry.name}"
      if entry.optional then
        throwErrorAt stx "record_step%: the field {entry.name} is optional; construction requires required fields"
    let supplied := names.zip values
    let spelling (name : Ident) := name.getId.toString (escape := false)
    for (name, _) in supplied do
      let key := spelling name
      if (supplied.filter (fun entry => spelling entry.1 == key)).size > 1 then
        throwErrorAt name "record_step%: the field {key} is supplied twice"
      unless fields.any (fun field => field.name == key) do
        throwErrorAt name "record_step%: the schema has no field {key}"
    let mut ordered : Array (String × TSyntax `term) := #[]
    for field in fields do
      let Option.some (_, value) := supplied.find? (fun entry => spelling entry.1 == field.name)
        | throwErrorAt stx "record_step%: the required field {field.name} is missing"
      ordered := ordered.push (field.name, value)
    let mut result : TSyntax `term ← `($(mkCIdent `Effect4.Modules.StepFields.nil))
    for (name, value) in ordered.reverse do
      result ← `($(mkCIdent `Effect4.Modules.StepFields.cons) $(quote name) $value $result)
    elabTermEnsuringType (← `($(mkCIdent `Effect4.Modules.Step.record) $result)) expected
  | _ => throwUnsupportedSyntax

end Effect4.Modules.Step.Elab
