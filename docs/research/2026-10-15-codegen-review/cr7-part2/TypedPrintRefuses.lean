import Effect4.Laws.Api.ModuleReadable

/-!
# `E4-PRINT-CE-004` and `E4-PRINT-CE-005`: the typed print refuses where the print succeeds

Since the codegen refactor's CR-7, the module that ships prints its pieces by the typed print
alone (`shippedPieces`, `src/Effect4/Codegen/PrintTyped.lean`). The row-only printer, which a
piece fell back to where the site printer refused, is gone. Two statements held only through
that fallback. Each witness below refutes one of them as it stood, and its theorem now reads the
typed print's success.

`E4-PRINT-CE-004`. Emission's completeness (`emitModule_complete`,
`src/Effect4/Laws/Api/ModuleReadable.lean`) said that a checked program whose pieces are
readable, over a lawful table, emits. A site whose type has no printed form refuses the typed
print, so the module refuses the program. The theorem now takes the typed print's success at
the main piece (`typedMain`).

`E4-PRINT-CE-005`. The connector (`printTyped_eq_print`, `src/Effect4/Laws/Codegen/PrintTyped.lean`)
said that under `NoJoin` the typed print is the print. The site printer needs a checked context
at every address, and an address with no checked environment has none. The detector reads no
join there, so `NoJoin` can hold while the typed print refuses. The theorem now reads a
successful typed print.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Codegen.TypedPrintRefuses

open Effect4 Effect4.Program Effect4.Codegen

/-! ## `E4-PRINT-CE-004`: a checked, readable program whose typed print refuses -/

/-- A synchronous row whose answer is a legacy handle with no printed form. -/
def badRow : Row :=
  { name := "badRead", spelling := "Bad.read", kind := .sync, request := .unit,
    answer := .handle "not a type !", cite := "E4-PRINT-CE-004", registration := .external }

def badTable : RowTable := [badRow]

/-- A scope whose body answers the bad handle or a number: a proper union that the scope's site
must spell. The program discards it. -/
def joinedScope : NativeEff :=
  .bind
    (.scoped (.select (.lit (.bool true)) .bool
      (.perform (.external 0) (.lit .unit)) (.succeed (.lit (.nat 1)))))
    (.succeed (.lit (.nat 2)))

-- finite evaluation: the old statement's premises hold; the table is lawful, the program is
-- formed and checked, its one piece is readable, and its types and literals are in the profile
#guard LawfulTable badTable
#guard (Formation.checkInput joinedScope badTable).isNone
#guard (Api.typeOf joinedScope badTable).isSome
#guard match joinedScope.hoistAll with
  | .ok (main, _) => Readable [] (nativeSignature badTable) 0 main && main.block?.isNone
  | .error _ => false
#guard match Api.typeOf joinedScope badTable with
  | some t => declarationTypeRepresentable t
  | none => false
#guard (annotationRefusal joinedScope).isNone
#guard natLiteralsInProfile joinedScope

-- finite evaluation: the print prints it
#guard (Program.print (nativeSignature badTable) 0 joinedScope).isOk

-- the attack: the typed print refuses at the scope, whose answer has no printed form
#guard match Program.printTyped (nativeSignature badTable) [] joinedScope with
  | .error (.typeSpelling spelling) => spelling == "number | not a type !"
  | _ => false

-- so the module that ships refuses the program, by the same reason
#guard match Api.emitModule "main" joinedScope badTable with
  | .error (.print (.typeSpelling spelling)) => spelling == "number | not a type !"
  | _ => false

/-- The same program over a row whose answer prints. -/
def goodTable : RowTable := [{ badRow with answer := .string }]

-- control: where the site's type has a printed form, the typed print writes it and the module
-- emits
#guard (Program.printTyped (nativeSignature goodTable) [] joinedScope).isOk
#guard match Api.emitModule "main" joinedScope goodTable with
  | .ok _ => true
  | .error _ => false

/-! ## `E4-PRINT-CE-005`: an address with no checked environment -/

/-- A program whose first step reads a variable that its environment does not hold. The checker
types no answer for it, so the second step has no environment. -/
def unchecked : NativeEff := .bind (.succeed (.var 5)) (.succeed (.lit .unit))

-- finite evaluation: the second step has no checked environment, so no context
#guard ((annotate (nativeSignature []) [] unchecked).find? fun entry => entry.path == [1]).map
  (·.env.isNone) == some true
#guard (PrintEliminators.contextAtTable (annotate (nativeSignature []) [] unchecked) unchecked
  [1]).isNone

-- finite evaluation: at every address of the program no call needs a join and no site needs a
-- type; outside its addresses the program holds no node, so neither reads a join there
#guard (Node.addresses (.eff unchecked)).all fun path =>
  !PrintedJoin.at_ (nativeSignature []) [] unchecked path &&
    !PrintEliminators.joinsAt (nativeSignature []) [] unchecked path

-- finite evaluation: the print prints it
#guard (Program.print (nativeSignature []) 0 unchecked).isOk

-- the attack: the typed print refuses, for the missing context
#guard match Program.printTyped (nativeSignature []) [] unchecked with
  | .error (.internalAction why) => why == "typed:missing context"
  | _ => false

-- control: where the variable is in the environment, the typed print is the print
#guard match Program.printTyped (nativeSignature []) [] (.bind (.succeed (.lit .unit))
    (.succeed (.var 0))), Program.print (nativeSignature []) 0 (.bind (.succeed (.lit .unit))
    (.succeed (.var 0))) with
  | .ok typed, .ok plain => typed == plain
  | _, _ => false

end Test.Counterexamples.Codegen.TypedPrintRefuses
