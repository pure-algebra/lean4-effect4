import Effect4.Program.Native

/-! Shared host resource-row fixture; runtime modules do not import test support. -/

namespace Test.Api.AcquireHandleContract
open Effect4 Effect4.Program Effect4.Machine

def resource := "Host.Resource"
def table : RowTable :=
  [ { name := "acquire", spelling := "Host.acquire", kind := .async,
      registration := .external, request := .unit, answer := .handle resource, error := .never, cite := "" }
  , { name := "close", spelling := "Host.close", kind := .async,
      registration := .external, request := .handle resource, answer := .unit, error := .never, cite := "" }
  , { name := "read", spelling := "Host.read", kind := .async,
      registration := .external, request := .handle resource, answer := .nat, error := .never, cite := "" } ]


end Test.Api.AcquireHandleContract
