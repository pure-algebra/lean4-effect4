import Effect4
open Effect4 Effect4.Store

/-- The fixture's program, read by the located reader, then printed both ways. -/
def bytesOf (s : String) : List Nat := s.toUTF8.toList.map (·.toNat)
def textOf (bs : List Nat) : String := String.fromUTF8! ⟨(bs.map (·.toUInt8)).toArray⟩

def main (args : List String) : IO Unit := do
  let src ← IO.FS.readFile (args.headD "program.json")
  match NatJson.parse (bytesOf src) with
  | .error _ => IO.println "parse refused"
  | .ok tree =>
    match Run.Kit.programShape.readLocated tree with
    | .error _ => IO.println "read refused"
    | .ok v =>
      let arrays := textOf (NatJson.render (Run.Kit.programShape.printTree v))
      let cons := textOf (NatJson.render (NatJson.ofBinary64 (Run.Kit.programShape.print v)))
      IO.println s!"ARRAYS {arrays.length}\n{arrays}\nCONS {cons.length}\n{cons}"
