import Effects.Conformance

/-- Write the generated conformance ledger. The path defaults to the
committed surface beside this package; the gate regenerates and
byte-compares it. -/
def main (args : List String) : IO Unit := do
  let path := args.headD "CONFORMANCE-LEDGER.md"
  IO.FS.writeFile path Effects.Conformance.fullLedger
