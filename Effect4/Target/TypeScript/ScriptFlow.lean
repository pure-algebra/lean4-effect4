import Effect4.Target.TypeScript.EffectV4
import Effect4.Semantics.Runs

/-!
# Target.TypeScript.ScriptFlow

Owner: the embedding of a straight-line `Script` into a Flow v2 graph, and
the closed alphabet it runs against. This is the internal oracle of the trace
lane: the same program traced through the algebra (`X.traced`) and run through
the Flow runner must agree under `m2` (`docs/TRACE-DAG.md`).

Operations of the embedded alphabet are positions in a table of `OpSpec`
rows: the family's operations first (traced), then the atoms and literals the
script needs (pure, excluded from the trace). Every block passes its whole
scope forward; a `perform` appends its answer as one more parameter. Types
are TypeScript spellings, as the rows carry them, so admission checks the
embedding for free.
-/

namespace Effect4.Target.EffectV4

open Effects Effect4.Flow
open Effects.Trace (Val)

/-- What an embedded operation is. -/
inductive OpKind where
  /-- An operation of the script's family: traced. -/
  | family
  /-- A pure atom: run, never traced. -/
  | atom
  /-- A literal: answers `value`, never traced. -/
  | lit (value : Val)
deriving DecidableEq, Repr, Inhabited

/-- One row of the embedded alphabet. -/
structure OpSpec where
  name : String
  kind : OpKind
  /-- TypeScript spelling of the request type; `void` for a nullary operation,
  and the right-nested tuple spelling for an operation of two or more
  parameters. -/
  requestTy : String
  /-- TypeScript spelling of the answer type. -/
  answerTy : String
  /-- TypeScript spelling of the declared error type (Flow v3): the type of the
  value a `performCatch`'s failure edge binds in its last slot. An operation
  that cannot fail declares `never`; the admission boundary never reads the
  spelling, it only compares. -/
  errorTy : String := "never"
  /-- The parameters of a family operation, binder and TypeScript spelling
  each. Empty on the hand-written rows of a table, which are unary. -/
  params : List (String × String) := []
deriving Repr, Inhabited

/-- How many arguments the host call of this operation takes. A request slot of
arity two or more holds the whole tuple and is destructured at the call
(`Lowering.tupleArgs`). -/
def OpSpec.arity (spec : OpSpec) : Nat := max 1 spec.params.length

/-- A row with no declared parameter list: an atom, a literal, or a family
operation whose request is one slot. Its arity is one and its failure edge is
`never`, and this says so rather than leaving a reader to check that two fields
were omitted on purpose (survey finding H16). -/
def OpSpec.unary (name : String) (kind : OpKind) (requestTy answerTy : String) : OpSpec :=
  { name := name, kind := kind, requestTy := requestTy, answerTy := answerTy,
    errorTy := "never", params := [] }

/-- A family operation of a declared parameter list that cannot fail. The
request spelling is the caller's: `requestSpelling params` for a table built
from a `ServiceRow`. -/
def OpSpec.infallible (name : String) (requestTy answerTy : String)
    (params : List (String × String)) : OpSpec :=
  { name := name, kind := .family, requestTy := requestTy, answerTy := answerTy,
    errorTy := "never", params := params }

/-- The row of a table position. -/
def OpSpec.at (table : List OpSpec) (op : Fin table.length) : OpSpec := table[op]

/-- The closed alphabet over a table: operations are table positions, so the
two lookup laws are positional. -/
abbrev tableAlphabet (id : AlphabetId) (table : List OpSpec) : FlowAlphabet String where
  id := id
  Op := Fin table.length
  operationId op := ⟨op.val⟩
  lookup id := if h : id.value < table.length then some ⟨id.value, h⟩ else none
  requestTy op := (OpSpec.at table op).requestTy
  answerTy op := (OpSpec.at table op).answerTy
  errorTy op := (OpSpec.at table op).errorTy
  boolTy := "boolean"
  lookup_operationId := by
    intro op
    simp [op.isLt]
  operationId_of_lookup := by
    intro id op found
    by_cases h : id.value < table.length
    · rw [dif_pos h] at found
      cases found
      cases id
      rfl
    · rw [dif_neg h] at found
      cases found

/-- A service over a table: literals answer themselves, atoms are evaluated
purely, and family operations are handled by name. -/
def tableService [Monad M] (id : AlphabetId) (table : List OpSpec)
    (family : String → Val → M Val) (atom : String → Val → Val) :
    FlowService (tableAlphabet id table) M where
  handle op request :=
    match (OpSpec.at table op).kind with
    | .lit value => pure value
    | .atom => pure (atom (OpSpec.at table op).name request)
    | .family => family (OpSpec.at table op).name request
  pure op :=
    match (OpSpec.at table op).kind with
    | .family => false
    | _ => true

/-- The traced name of a table operation. -/
def tableNameOf (id : AlphabetId) (table : List OpSpec) : (tableAlphabet id table).Op → String :=
  fun op => (OpSpec.at table op).name

/-! ## Building the graph -/

/-- The embedding state: the open block's scope is its parameter list. -/
structure Build where
  inputTy : String
  table : List OpSpec
  blocks : List (RawBlock String)
  /-- binder, TypeScript type, per parameter slot of the open block -/
  scope : List (String × String)
  /-- id of the open block -/
  next : Nat

namespace Build

def params (b : Build) : List String := b.scope.map (·.2)

def allVars (b : Build) : List Var := (List.range b.scope.length).map Var.mk

/-- The last parameter of the open block. -/
def last (b : Build) : Var := ⟨b.scope.length - 1⟩

def lookupVar (b : Build) (name : String) : Option (Var × String) :=
  match b.scope.findIdx? (fun entry => entry.1 == name) with
  | some index =>
      match b.scope[index]? with
      | some entry => some (⟨index⟩, entry.2)
      | none => none
  | none => none

def addOp (b : Build) (spec : OpSpec) : Build × Nat :=
  ({ b with table := b.table ++ [spec] }, b.table.length)

/-- Close the open block with a `perform` into a fresh block that receives the
whole scope plus the answer. -/
def performTo (b : Build) (op : Nat) (request : Var) (binder answerTy : String) : Build :=
  { b with
    blocks := b.blocks ++
      [{ id := ⟨b.next⟩, params := b.params,
         term := .perform ⟨op⟩ request ⟨b.next + 1⟩ b.allVars }]
    scope := b.scope ++ [(binder, answerTy)]
    next := b.next + 1 }

/-- A literal is a pure operation on the input parameter. -/
def literal (b : Build) (value : Val) (ty : String) : Build × Var × String :=
  let (b, op) := b.addOp (OpSpec.unary "lit" (.lit value) b.inputTy ty)
  let b := b.performTo op ⟨0⟩ "" ty
  (b, b.last, ty)

end Build

/-- Atoms the embedding may call: name, request type, answer type. -/
abbrev AtomTable := List (String × String × String)

/-- Materialize a pure term as a parameter of the open block. -/
def materialize (atoms : AtomTable) : Nat → Build → PureTerm → Option (Build × Var × String)
  | 0, _, _ => none
  | _, b, .var name => (b.lookupVar name).map fun (v, ty) => (b, v, ty)
  | _, b, .nat n => some (b.literal (.nat n) "number")
  | _, b, .str s => some (b.literal (.str s) "string")
  | fuel + 1, b, .app atom [arg] => do
      let (b, v, _) ← materialize atoms fuel b arg
      let (_, requestTy, answerTy) ← atoms.find? (·.1 == atom)
      let (b, op) := b.addOp (OpSpec.unary atom .atom requestTy answerTy)
      let b := b.performTo op v "" answerTy
      some (b, b.last, answerTy)
  | _, _, .app _ _ => none

/-- The request spelling of a parameter list: `void` for none, the parameter's
own spelling for one, and the right-nested product spelling for two or more.
This is exactly what `Effects.Trace.ToVal` builds from the parameter product on
the Lean face, and what `Spelling.prod` renders, so the two faces read one
request slot the same way. -/
def requestSpelling : List (String × String) → String
  | [] => "void"
  | [(_, ty)] => ty
  | (_, ty) :: rest => "readonly [" ++ ty ++ ", " ++ requestSpelling rest ++ "]"

/-- The family's operations, in row order, as the head of the table. Every row
has a request spelling, whatever its arity: an operation of two or more
parameters is performed with one request slot holding the tuple
(`E4-TARGET-CE-022`, repaired). -/
def familyTable (rows : ServiceRow) : List OpSpec :=
  rows.ops.map fun row =>
    { name := row.name
      kind := .family
      requestTy := requestSpelling row.tsParams
      answerTy := row.tsAnswer
      errorTy := match row.error with
        | some (_, ts) => ts
        | none => "never"
      params := row.tsParams }

def familyIndex (rows : ServiceRow) (op : String) : Option Nat :=
  rows.ops.findIdx? fun row => row.name == op

/-- One script step: a `perform` closes the open block, a `ret` ends the graph. -/
def embedStep (rows : ServiceRow) (atoms : AtomTable) (b : Build) : Step → Option Build
  | .perform bind op args => do
      let row ← rows.row? op
      let index ← familyIndex rows op
      let (b, request, _) ←
        match args with
        | [] => some (b.literal .unit "void")
        | [arg] => materialize atoms 16 b arg
        | _ => none
      some (b.performTo index request (bind.getD "") row.tsAnswer)
  | .ret value => do
      let (b, v, _) ← materialize atoms 16 b value
      some { b with
        blocks := b.blocks ++ [{ id := ⟨b.next⟩, params := b.params, term := .ret v }]
        next := b.next + 1 }

/-- Embed a straight-line script as a Flow v2 graph over a table alphabet.
Refuses operations with two or more parameters and atoms with an argument
list other than one; the graph is then admitted by `Effects.admit`. The
restriction is this embedding's, not the alphabet's: a hand-written region flow
performs a two-parameter operation from one tuple slot. -/
def Script.toFlow (rows : ServiceRow) (atoms : AtomTable) (script : Script) :
    Option (List OpSpec × RawFlow String) := do
  let start : Build :=
    { inputTy := script.param.2, table := familyTable rows, blocks := [],
      scope := [script.param], next := 0 }
  let b ← script.steps.foldlM (embedStep rows atoms) start
  some (b.table,
    { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := script.param.2,
      resultTy := script.result, blocks := b.blocks })

end Effect4.Target.EffectV4
