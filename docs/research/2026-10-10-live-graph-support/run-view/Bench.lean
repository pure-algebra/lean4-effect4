import Baseline
import Tools.View.Run
import Effect4.Store.Domain.ProgramWire

open Tools.View Effect4.Program

def readPages (ps : Option (List Page)) : Nat :=
  (ps.getD []).foldl (fun n p => n + p.lines.foldl (fun k line =>
    k + line.text.length + line.type.length) 0 +
      (p.code.map fun c => c.lines.foldl (fun k s => k + s.length) 0).getD 0) 0

def sample (cached : Bool) (repeats : Nat) : IO (Nat × Nat) := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for i in [:repeats] do
    for (name, p) in Effect4.Program.Wire.Corpus.all do
      let name := name ++ toString i
      let pages := if cached then Tools.View.Run.frames name p 32
        else RunViewBaseline.frames name p 32
      checksum := checksum + readPages pages
  let stop ← IO.monoNanosNow
  return (checksum, stop - start)

def main (args : List String) : IO Unit := do
  let repeats := ((args.head?.getD "3").toNat?).getD 3
  let warmOld ← sample false 1
  let warmNew ← sample true 1
  unless warmOld.1 == warmNew.1 do throw (IO.userError "warmup output differs")
  for round in [:3] do
    let (old, fresh) ← if round % 2 == 0 then do
      let old ← sample false repeats
      let fresh ← sample true repeats
      pure (old, fresh)
    else do
      let fresh ← sample true repeats
      let old ← sample false repeats
      pure (old, fresh)
    unless old.1 == fresh.1 do throw (IO.userError "measured output differs")
    IO.println s!"round={round} repetitions={repeats} checksum={old.1} former_ns={old.2} prepared_ns={fresh.2}"
