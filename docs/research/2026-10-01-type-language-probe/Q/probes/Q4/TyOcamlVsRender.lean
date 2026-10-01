import Conform.Effect4.LcnfMl
/-! Seat Q, question 4 (the generatability table): is `LcnfMl.tyOcaml` the target renderer applied
to `LcnfMl.tyT`? If so the string mirror is one function of the value mirror. -/
open Effect4.Program Conform.Effect4.LcnfMl Conform.Lcnf.Target

def samples : List Ty :=
  [.never, .unit, .nat, .int, .string, .bool, .handle "Host.R", .option .nat, .list .string,
   .prod .nat .bool, .except .string .nat, .exitOf .nat .string, .causeOf .string,
   .fiberOf .unit .nat, .union .nat .string, .lit "tag", .refOf .nat, .deferredOf .nat .string,
   .var 3, .unknown, .list (.prod (.option .nat) (.union .never .unknown))]

#eval IO.println (samples.map fun t => s!"{tyOcaml t}  |  {(tyT t).render}")
#eval IO.println s!"equal on {(samples.filter fun t => tyOcaml t == (tyT t).render).length} of {samples.length}"
