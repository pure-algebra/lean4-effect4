import Effect4.Modules.Queue.Cell
import Effect4.Program.Typing
import Effect4.Program.Native

/-!
# The Queue's cell and its steps: finite controls of the library module (decisions row 255)

The module is `src/Effect4/Modules/Queue/`: the cell's type and initial value (`Cell.lean`), and
the six step terms (`Steps.lean`). This battery holds the finite controls of the module alone:
the cell's type and value, and each step's type, size and reading domain. The comparison with
the abstract model is `Test/Program/QueueAgreement.lean`. The runs on the machine are
`Test/Program/QueueScenarios.lean`.

Placement. The typing controls are finite instances of the typing statements of
`src/Effect4/Laws/Modules/Queue/Steps.lean` (concept `store-typing`, requirement R4). Every
guard is a finite check at the listed message types. None proves a statement at every message
type, and none states agreement with the model.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Test.Program.QueueSteps

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-- A source term's tree at a scope of names. -/
def termAt (names : List String) (src : TermSrc) : Option Term :=
  (src { names := names } []).toOption

/-- The checker's type of a source term, at a scope of names and their types. -/
def typeAt (names : List String) (types : List Ty) (src : TermSrc) : Option Ty :=
  (termAt names src).bind (termTy nativeSignature types)

/-! ## 1. The cell -/

/-- Message types that are their own normal form. The cell is checked at each. -/
def messageTypes : List Ty :=
  [.nat, .string, .bool, .unit, .never, .unknown, .option .nat, .list .string,
   .union .nat .string, .prod .nat .string, .lit "x", .refOf .nat, .deferredOf .nat .never,
   .record [("a", false, .nat), ("b", true, .string)], .map .string .nat,
   .tuple [.nat, .string, .bool], .fiberOf .nat .never, .exitOf .nat .string, .causeOf .string,
   .int, .number, .null, .undefined, .bytes, Queue.cellTy .nat,
   .list (.union .nat (.lit "a")), .except .string .nat]

/-- Message types that are not their own normal form. -/
def unnormalTypes : List Ty :=
  [.union .nat .nat, .tuple [.nat, .string], .union .string (.lit "x"),
   .record [("b", false, .nat), ("a", false, .nat)], .prod (.union .nat .string) .bool]

/-- Message types that formation refuses: a repeated field, a map key that is no string, and a
`Deferred` whose error column the error alphabet does not admit. -/
def malformedTypes : List Ty :=
  [.record [("a", false, .nat), ("a", false, .string)], .map .nat .nat,
   .deferredOf .nat (.refOf .nat)]

#guard messageTypes.all fun A => decide (A.normalize = A)
#guard unnormalTypes.all fun A => decide (A.normalize ≠ A)

-- Each written declaration normalizes to its type: the fields in the canonical order.
#guard decide (Ty.normalize (.record Queue.takerFields) = Queue.takerTy)
#guard messageTypes.all fun A =>
  decide (Ty.normalize (.record (Queue.offerFields A)) = Queue.offerTy A) &&
    decide (Ty.normalize (.record (Queue.cellFields A)) = Queue.cellTy A)

-- The checker answers the cell's type for the initial value, at each message type and in any
-- scope.
#guard messageTypes.all fun A =>
  decide (typeAt [] [] (Queue.empty A 2) = some (Queue.cellTy A)) &&
    decide (typeAt ["x"] [.string] (Queue.empty A 0) = some (Queue.cellTy A))
-- Red control: at a message type that is not its own normal form, the checker answers the
-- cell's type at the normal form, and not at the written type.
#guard unnormalTypes.all fun A =>
  decide (typeAt [] [] (Queue.empty A 2) = some (Queue.cellTy A.normalize)) &&
    decide (typeAt [] [] (Queue.empty A 2) ≠ some (Queue.cellTy A))
-- Red control: at a message type that formation refuses, the initial value has no type.
#guard malformedTypes.all fun A => (typeAt [] [] (Queue.empty A 2)).isNone

-- The initial value: the record frame of the four fields in the canonical order, with the
-- capacity and three empty lists. The message type has no part in the value.
#guard messageTypes.all fun A =>
  decide (((termAt [] (Queue.empty A 2)).bind (evalTerm [])) = some
    (.ctor 0 [.list [.str "cap", .str "msgs", .str "offers", .str "takers"],
      .list [.nat 2, .list [], .list [], .list []]]))

end Test.Program.QueueSteps
