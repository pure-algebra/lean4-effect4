import Test.Dogfood.Scenario.Todo.Data
import Effect4.Program.Authoring.ApplicationService

/-!
# The to-do's cached service, as a program

The to-do with the banked Ref cache imposed on its service, built, and one consumer per request
(`consumerBuiltAt`). The battery and its proofs are `Test/Dogfood/Scenario/Todo/Cached.lean`.
These definitions stand apart, over law-free modules, so the LCNF route's to-do lane and its
fixture import no law module (`Test/Dogfood/Scenario/Todo/HostRun.lean`).
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Todo.Cached

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-- The to-do with the banked cache imposed on its service (`Examples.CachedTodo`). -/
def cached : Application NativeOp := Examples.CachedTodo.application

/-- The service's name. -/
def service : String := "TodoApp"

/-- An application's service module, built. -/
def built? (app : Application NativeOp) : Option Api.Built :=
  (app.serviceModule service).toOption.bind fun m => (Api.Author.build m).toOption

/-- A consumer built over the cached service's unchanged definition module.
Each run starts from empty stores and calls its own service initializer. -/
def buildConsumer (main : Src NativeOp) : Option Api.Built :=
  (cached.serviceModule service).toOption.bind fun m =>
    (Api.Author.build { m with main := main }).toOption

/-- One recorded request: make the cached service state once, then invoke the named method.
Unknown entries refuse before the service module builds. -/
def consumerBuiltAt (name : String) (args : List TermSrc) : Option Api.Built :=
  (cached.entry? name).bind fun entry =>
    buildConsumer (bindWith (Def.invoke (service ++ "Context") []) fun state =>
      Def.invoke (service ++ "_" ++ entry.name) (state :: args))

end Test.Dogfood.Scenario.Todo.Cached
