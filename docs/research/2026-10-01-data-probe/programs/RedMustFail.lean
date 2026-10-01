import Effect4.Api.Author
import Effect4.Schema.Bridge
import Effect4.Schema.Codec

/-! Seat PROGRAMS of the data probe (2026-10-01), the red control that must FAIL to compile today:
each command asserts what the record stage would make true. Expected: exit 1 with exactly four
errors, one per command below, in order (`RedMustFail.log`). If any of them compiles, the tree
grew the construct and this probe's premise is stale. Scratch, not in the tree. -/

set_option autoImplicit false

namespace Probe.RedMustFail
open Effect4 Effect4.Program Effect4.Program.Authoring

-- 1. A record literal builds (it does not: the checker refuses the term at `[]`).
#guard (Effect4.Api.Author.build { main := succeed (app "record" [str "id", nat 2]) }).toOption.isSome

-- 2. A host row may answer `int` (it may not: admission, `uninhabited` at the column).
#guard (Effect4.Api.Author.build
  { rows := [Row.host "Ledger.balance" .unit .int],
    main := Row.call (Row.host "Ledger.balance" .unit .int) unit }).toOption.isSome

-- 3. A struct schema reads back as a type (it does not: `ofSchema` answers `none`).
#guard (Effect4.Schema.Bridge.ofSchema
  (Effect4.Schema.struct [Effect4.Schema.property "id" (Effect4.Schema.Bridge.schema .nat)])).isSome

-- 4. `Ty` has a record constructor (it has none: an unknown constant).
#check (Ty.record : Ty)

end Probe.RedMustFail
