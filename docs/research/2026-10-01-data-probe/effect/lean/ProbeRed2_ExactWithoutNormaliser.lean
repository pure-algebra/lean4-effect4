import Effect4.Schema.Codec

/-! RED CONTROL (must fail): claims the codec's encoding of `some 1` at `option nat` is the
reordered object that its decoder accepts. Exactness without a key-order normaliser is false.
Expected: `#guard` fails, exit 1. -/

set_option autoImplicit false
open Effect4 Effect4.Program Effect4.Machine

def reordered : Json := .obj [("value", Arch.Json.ofNat 1), ("_tag", .str "Some")]

#guard Schema.decode (.option .nat) reordered = some (.some (.nat 1))
#guard Schema.encode (.option .nat) (.some (.nat 1)) = some reordered
