import Effect4.Target.TypeScript.Trace

/-!
# Target.TypeScript.TraceWire

Kernel receipts for the two halves of the wire the host cannot be asked about:
the JSON string escaping of `Effect4.Target.TypeScript.Trace.escape`, and the
shape of a resource-boundary golden's header.

The renderer is an exact target-implementation module and declares no theorem;
these are `#guard`s, evaluated by the kernel, not proofs. They exist because
`escape`'s obligation is a *host* obligation — byte-for-byte agreement with
`JSON.stringify` (ECMA-262 `QuoteJSONString`) — and no golden of the corpus
carries a control character, so nothing else in the tree would notice if the
escaping drifted. The other half of the same fact is planted on the host in
`scripts/test-trace-goldens-gate.sh` (`raw-control`, with `escaped-control`
beside it as the positive control).

counterexample: E4-TARGET-CE-014
-/

namespace Effect4Test.Target.TypeScript.TraceWire

open Effect4.Target.TypeScript.Trace

-- The exact table `JSON.stringify` produces for the C0 range: the five
-- shorthands `\b \t \n \f \r`, and `\uXXXX` in lowercase hex for the rest.
-- Read off the pinned host, `node -e` over `String.fromCharCode(i)`.
def jsonStringifyC0 : List String :=
  [ "\\u0000", "\\u0001", "\\u0002", "\\u0003", "\\u0004", "\\u0005", "\\u0006", "\\u0007"
  , "\\b", "\\t", "\\n", "\\u000b", "\\f", "\\r", "\\u000e", "\\u000f"
  , "\\u0010", "\\u0011", "\\u0012", "\\u0013", "\\u0014", "\\u0015", "\\u0016", "\\u0017"
  , "\\u0018", "\\u0019", "\\u001a", "\\u001b", "\\u001c", "\\u001d", "\\u001e", "\\u001f" ]

-- Every control character below 0x20 is spelled the way the host spells it.
#guard (List.range 32).map (fun n => escape (String.singleton (Char.ofNat n))) == jsonStringifyC0

-- The two structural escapes.
#guard escape "\"" == "\\\""
#guard escape "\\" == "\\\\"

-- DEL is not escaped, and neither is anything above it: `JSON.stringify`
-- escapes only the C0 range, the quote and the backslash.
#guard escape (String.singleton (Char.ofNat 127)) == String.singleton (Char.ofNat 127)
#guard escape "a b" == "a b"
#guard escape "é" == "é"

-- A control character inside a value cell, which is where it would actually
-- appear: the string answer of an operation.
#guard val (.str (String.singleton (Char.ofNat 1))) == "\"\\u0001\""
#guard row (.answer "get" (.str ("a" ++ String.singleton (Char.ofNat 1) ++ "b"))) ==
  "answer\tget\t\"a\\u0001b\""

-- The `nat`/`int` non-injectivity, pinned as a fact rather than left implicit:
-- two different events render the same row, so equal rows do not imply equal
-- events and agreement is stated under the declared answer-type profile.
-- counterexample: E4-TARGET-CE-016
#guard val (.nat 7) == val (.int 7)
#guard (Effect4.Trace.Event.answer "get" (.nat 7)) != (Effect4.Trace.Event.answer "get" (.int 7))
#guard row (.answer "get" (.nat 7)) == row (.answer "get" (.int 7))

-- A golden carries budget rows only when it is a resource-boundary golden, so
-- every other golden is byte-identical to what it was before they existed.
#guard golden "p" [] [] [] == "format\teffect4-trace-v1\nface\tlean\nprogram\tp\ntape\t\nrules\t\n"
#guard golden "p" [] [] [] (budgets := [("default", 19), ("yield3", 79)]) ==
  "format\teffect4-trace-v1\nface\tlean\nprogram\tp\ntape\t\nrules\t\nbudget\tdefault\t19\nbudget\tyield3\t79\n"

end Effect4Test.Target.TypeScript.TraceWire
