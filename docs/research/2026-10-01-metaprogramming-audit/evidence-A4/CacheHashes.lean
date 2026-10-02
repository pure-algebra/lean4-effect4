import Lake.Build.Trace

def main (args : List String) : IO UInt32 := do
  let [manifest] := args | throw <| IO.userError "expected a tab-separated cache manifest"
  let mut failures := 0
  for line in (← IO.FS.readFile manifest).splitOn "\n" do
    if line.isEmpty then continue
    let [kind, path, expected] := line.splitOn "\t"
      | throw <| IO.userError s!"bad manifest row: {line}"
    let actual ← Lake.computeFileHash path (kind == "text")
    if toString actual != expected then
      IO.println s!"MISMATCH\t{path}\t{expected}\t{actual}"
      failures := failures + 1
  IO.println s!"cache hash mismatches: {failures}"
  return if failures == 0 then 0 else 1
