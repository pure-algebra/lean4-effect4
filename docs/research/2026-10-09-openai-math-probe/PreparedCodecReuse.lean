import Effect4.Schema.Codec
import Lean

/-! Bounded inspection of compiled prepared-codec operations.
This observes persisted compiler code. It is not a cost theorem or a timing result.
The rejected heads identify rebuilding through the current public functions.
The printed bodies also retain the field projections for source review. -/
set_option autoImplicit false
namespace MathTransferProbe.PreparedCodecReuse
open Effect4 Effect4.Program Effect4.Machine
open Lean Compiler LCNF

-- The same prepare/decode/reencode use as the numeric harness.
def roundTrip (source : Ty) (input : Effect4.Json) : Option Effect4.Json :=
  let prepared := Schema.Codec.prepare source
  (prepared.decode input).bind prepared.encode

run_elab do
  let env ← getEnv
  let methodPrefixes := [``Schema.Codec.Prepared.encode, ``Schema.Codec.Prepared.decode,
    ``Schema.Codec.Prepared.isValue]
  let selected := methodPrefixes ++ [``Schema.Codec.prepare]
  let mut seen : Array Lean.Name := #[]
  let mut methods : Nat := 0
  -- Persisted entries include the compiler's auxiliary declarations.
  for i in [:env.header.modules.size] do
    for decl in monoExt.getModuleEntries env i do
      if selected.any (·.isPrefixOf decl.name) && !seen.contains decl.name then
        seen := seen.push decl.name
        let .code code := decl.value | throwError "missing compiled body: {decl.name}"
        if methodPrefixes.any (·.isPrefixOf decl.name) then
          methods := methods + 1
          code.forM fun node => do
            if let .let binding _ := node then
              if let .const name _ _ := binding.value then
                if [``Schema.Codec.prepare, ``Schema.Codec.wire, ``Ty.normalize].any
                    (·.isPrefixOf name) then
                  throwError "prepared operation rebuilds through {name} in {decl.name}"
        logInfo m!"{← ppDecl' decl .mono}"
  for name in selected do
    unless seen.contains name do throwError "no persisted compiler body for {name}"
  if methods = 0 then throwError "no prepared operation inspected"
  let some consumer ← getMonoDecl? ``roundTrip | throwError "consumer has no compiled body"
  logInfo m!"{← ppDecl' consumer .mono}"
  logInfo m!"PASS: {methods} prepared operation bodies contain no prepare, wire or normalize call"

end MathTransferProbe.PreparedCodecReuse
