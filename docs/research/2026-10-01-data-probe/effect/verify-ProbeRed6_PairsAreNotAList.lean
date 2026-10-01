import Effect4.Program.Typed

/-! RED CONTROL (must fail): claims the name-keyed record value `{a: 1, b: 2}`, spelled as a list
of (name, value) pairs, is NOT a member of `list (prod string nat)`. It is. Expected: exit 1. -/

set_option autoImplicit false
open Effect4 Effect4.Program Effect4.Machine

def abPairs : Val := .list [.list [.str "a", .nat 1], .list [.str "b", .nat 2]]

#guard Effect4.Program.Val.hasTy abPairs (.list (.prod .string .nat)) [] = false
