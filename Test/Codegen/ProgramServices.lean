import Effect4.Program.Services
import Effect4.Codegen.Print
import Effect4.Codegen.Surface
import Effect4.Laws.Codegen.Services

/-!
# ProgramServices — controls for the domain and TypeScript profiles of service roles

The program domain accepts a reserved target name. Both profiles refuse a malformed method
request. The target also refuses collisions between generated key and layer names.
These finite controls concern role formation and target names, not service execution.
-/

set_option autoImplicit false

namespace Test.Codegen.ProgramServices

open Effect4.Program

/-- One service with a state of type `unit` and a method with no value argument. -/
def block (service method : String) : List DefDecl :=
  [ { name := service ++ "Init", request := .unit, answer := .unit,
      role := .serviceInit service }
  , { name := service ++ "Read", request := .unit, answer := .nat,
      role := .serviceMethod service method 0 } ]

-- finite evaluation: roles retain their declaration positions and argument counts
#guard (servicesOf (block "Counter" "read")).map (fun sv => (sv.name, sv.init, sv.methods)) =
  [("Counter", 0, [("read", 1, 0)])]

-- control: a target-reserved method name is formed in the program domain
#guard serviceFaultIn anyName (block "Counter" "delete") = none
#guard serviceFault (block "Counter" "delete") = some (.service "Counter")

/-- A request whose type differs from the state at arity zero. -/
def malformed : List DefDecl :=
  (block "Counter" "read").map fun d => match d.role with
    | .serviceMethod _ _ _ => { d with request := .string }
    | _ => d

-- control: both profiles locate the malformed request at the same method
#guard serviceFaultIn anyName malformed = some (.serviceMethod "Counter" "read")
#guard serviceFault malformed = some (.serviceMethod "Counter" "read")

/-- Two distinct service names whose TypeScript key and layer constants collide. -/
def layerCollision : List DefDecl := block "Counter" "read" ++ block "CounterLayer" "read"

-- control: role formation does not impose the target's generated names
#guard serviceFaultIn anyName layerCollision = none
#guard serviceFault layerCollision = some (.serviceName "CounterLayer")

-- reader: target acceptance supplies domain role formation at this real service
#guard serviceFault (block "Counter" "read") = none
example (accepted : serviceFault (block "Counter" "read") = none) :
    serviceFaultIn anyName (block "Counter" "read") = none :=
  serviceFaultIn_anyName accepted

-- reader: domain formation supplies the argument reading for this service
example : (Effect4.Codegen.entriesOf (block "Counter" "read")
    ⟨"Counter", 0, [("read", 1, 0)]⟩).isSome = true :=
  entriesOf_isSome (by rfl) (by decide)

-- control: duplicate definition names take precedence over a reserved method name
#guard serviceFault (block "Counter" "delete" ++
    [{ name := "CounterInit", request := .unit, answer := .unit }]) =
  some (.serviceName "CounterInit")

end Test.Codegen.ProgramServices
