module

public import Effect4.Program.Typing.Focus

/-!
# Program.Typing.Table — the address table, the list of refusals, and the slot table

**The question.** `focusAt` answers at one address (`Program/Typing/Focus.lean`). A tool that
shows a whole program asks at every address at once: which environment each node reads, which
type the checker answers at each sub-program, and every place where the checker refuses. This
module answers with one list, the address table.

## The address table

`Node.addresses` lists the address of every node, in the order of the generated path fold: a
node, then its children from the left. `table` gives one entry for each address
(`Table.Entry`): the address, the environment there (`Node.envAt`), and at an address of a
program the checker's answer there (`Checker.check`). An entry of a program is in one of three
states:

| State | The entry | It means |
| --- | --- | --- |
| typed | an environment, and a type | the checker admits the sub-program there |
| refused | an environment, and a refusal | the checker refuses it; the refusal names its place |
| not reached | no environment, no answer | a step on the way reads a sibling that is refused |

An entry of a statement, a fiber action or a layer has its environment and no answer: the
checker answers at those sorts through the program above them.

## The list of refusals

`refusals` is the distinct refusals of the entries, in the table's order. A refused node
refuses each program around it with the same located refusal, so the list keeps one of each.
Its head is the located refusal of `explain`, and it is empty exactly when the checker admits
the program (`refusals_head`, `refusals_nil_iff`, `Laws/Program/Typing/Table.lean`).

## The slot table

A term has no address. Its type is `termTy` at the environment of its node, but for five term
slots, whose rule extends that environment first (`ExtSlot`). `Node.extSlotTerm` answers the
term in such a slot, and `Node.extSlotEnv` its environment. On a typed node the term has a type
there (`hasTy_extSlotEnv`). The consumer is the TypeScript printer at an eliminator inside
such a term.

## The cost

The table is a specification, and it is slow. Each entry asks `Node.envAt` from the root and
the checker at the address, so each entry costs up to one check of the program. A pass that
checks each node once is another slice, and this table is what it must answer.

## What this module is not

- It is not a second checker. It calls `Node.envAt` and `Checker.check`, and it changes neither.
- It does not mark past a refusal: an entry after a refused sibling is not reached.
- It does not order the refusals beyond the head. The rest follows the table's order, and no
  law relates that order to the checker's.
- It knows no gap and no hole. A hole is a host row, and the table reads it as the checker does.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- **Every address of a node**, in the order of the generated path fold: the node first, then
its children from the left. It lists exactly the addresses of the node's nodes
(`mem_addresses_iff`, `Laws/Program/Typing/Table.lean`). It is the path fold of the law graph
at the yield of one path (`addresses_eq_foldList` there), written here over the generated folds
because a core module does not import the law graph. -/
def Node.addresses (n : Node Op) : List (List Nat) :=
  let here {β : Type} (_ : β) (p : List Nat) : List (List Nat) := [p]
  match n with
  | .eff e => foldMapAt_eff [] (· ++ ·) [] e here here here here here here here
  | .stmt s => foldMapAt_stmt [] (· ++ ·) [] s here here here here here here here
  | .stmts s => foldMapAt_stmts [] (· ++ ·) [] s here here here here here here here
  | .action a => foldMapAt_action [] (· ++ ·) [] a here here here here here here here
  | .effs es => foldMapAt_effs [] (· ++ ·) [] es here here here here here here here
  | .layer l => foldMapAt_layer [] (· ++ ·) [] l here here here here here here here
  | .layers ls => foldMapAt_layers [] (· ++ ·) [] ls here here here here here here here

/-- **One entry of the address table.** -/
structure Table.Entry where
  /-- the address of the node -/
  path : List Nat
  /-- the environment at the address; `none` where a step on the way reads a refused sibling -/
  env : Option NodeEnv
  /-- at an address of a program with an environment: the checker's answer there -/
  result : Option (Except TypeRefusal EffTy)
  deriving DecidableEq

/-- **The address table of a program**: one entry for each address, in the order of
`Node.addresses`. The environment is `Node.envAt` from the root's environment `env0`. The answer
is `Checker.check` on the sub-program in that environment, located at the address. -/
def table (s : Signature Op) (env0 : TyEnv) (p : Eff Op) : List Table.Entry :=
  (Node.addresses (.eff p)).map fun a =>
    let env := (Node.eff p).envAt s (.env env0) a
    ⟨a, env, match (Node.eff p).at_ a, env with
      | some (.eff q), some (.env tys) => some (Checker.check s tys a q)
      | _, _ => none⟩

/-- **The refusals of a program**: the distinct refusals of the table's entries, in the table's
order. The head is the located refusal of `explain` (`refusals_head`), and the list is empty
exactly when the checker admits the program (`refusals_nil_iff`). -/
def refusals (s : Signature Op) (env0 : TyEnv) (p : Eff Op) : List TypeRefusal :=
  ((table s env0 p).filterMap fun e => e.result.bind Checker.refusal).eraseDups

/-! ## The slot table -/

/-- **A term slot whose rule extends its node's environment.** Every other term slot of a
program, of a statement and of a fiber action is typed at the node's own environment. -/
inductive ExtSlot where
  /-- the test of `catchIf`: it reads the body's error -/
  | catchIfTest
  /-- the test of `iterate`: it reads the cursor -/
  | iterateTest
  /-- the step of `iterate`: it reads the cursor and the body's answer -/
  | iterateStep
  /-- the result of `iterate`: it reads the cursor -/
  | iterateResult
  /-- an operation's own term (`Signature.termOf`): it reads its current value, at the instance
  of the row's parameter -/
  | opTerm
  deriving DecidableEq, Repr

/-- **The term in a slot of a node**; `none` where the node has no such slot. An operation's own
term stands in the operation, and the signature reads it. -/
def Node.extSlotTerm (s : Signature Op) : Node Op → ExtSlot → Option Term
  | .eff (.catchIf test _ _), .catchIfTest => some test
  | .eff (.iterate _ _ test _ _ _), .iterateTest => some test
  | .eff (.iterate _ _ _ step _ _), .iterateStep => some step
  | .eff (.iterate _ _ _ _ result _), .iterateResult => some result
  | .eff (.perform op _), .opTerm => (s.termOf op).map (·.term)
  | _, _ => none

/-- **The environment of a slot of a node**, from the node's environment `env`. Each case is
the environment of the term in the typing rule of its constructor (`HasTy.catchIf`,
`HasTy.iterate`, and `bindTerm` for an operation's term). The answer is `none` where the node
has no such slot, or where the checker refuses what the rule reads first: the body, the initial
term, or the request. On a typed node the slot's term has a type there (`hasTy_extSlotEnv`,
`Laws/Program/Typing/Table.lean`). -/
def Node.extSlotEnv (s : Signature Op) (env : TyEnv) (n : Node Op) : ExtSlot → Option TyEnv
  | .catchIfTest => match n with
    | .eff (.catchIf _ body _) =>
        (effTy s env body).map fun b => env ++ [b.error]
    | _ => none
  | .iterateTest => match n with
    | .eff (.iterate cursorTy initial _ _ _ _) =>
        (termTy s env initial).map fun c0 => env ++ [cursorTy.getD c0]
    | _ => none
  | .iterateResult => match n with
    | .eff (.iterate cursorTy initial _ _ _ _) =>
        (termTy s env initial).map fun c0 => env ++ [cursorTy.getD c0]
    | _ => none
  | .iterateStep => match n with
    | .eff (.iterate cursorTy initial _ _ _ body) =>
        match termTy s env initial with
        | some c0 =>
            let cursor := cursorTy.getD c0
            (effTy s (env ++ [cursor]) body).map fun b => env ++ [cursor, b.answer]
        | none => none
    | _ => none
  -- the instance of the parameter, as `bindTerm` computes it from the request's bindings
  | .opTerm => match n with
    | .eff (.perform op req) =>
        match s.termOf op with
        | some b =>
            match termTy s env req with
            | some reqTy =>
                let row := s.rowOf op
                match Ty.matchTemplate [] row.request.normalize reqTy.normalize with
                | some σ => some (env ++ [(b.param.normalize.instantiate σ).normalize])
                | none => none
            | none => none
        | none => none
    | _ => none

end Effect4.Program
