import Effect4.Program.Wire

/-!
# EffWire — the goldens of the Eff wire

Prints, for every program of `Effect4.Program.Wire.Corpus`, the canonical bytes as hex
and the constructor-index manifest of the families the wire covers, so an implementation
of the same rule in another language (`ocaml/eff`) can be checked byte for byte.

    lake env lean --run src/OCaml5/Tools/EffWire.lean [outdir]

With an output directory: `<outdir>/<name>.hex` per program and `<outdir>/manifest.txt`;
without: everything on stdout. A tool, not a library: it only calls the wire.
-/

open Effect4.Program.Wire

def hexOfByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  let hi := digits[b.toNat / 16]!
  let lo := digits[b.toNat % 16]!
  String.mk [hi, lo]

def hex (bs : List UInt8) : String := String.join (bs.map hexOfByte)

/-- The constructor order every implementation of the wire must agree on. -/
def manifest : String :=
  "\n".intercalate
    [ "Lit: unit nat bool str"
    , "Term: var lit app"
    , "Terms: nil cons"
    , "CauseTerm: fail die interrupt both"
    , "FnName: incr double zeroWhenPositive noChange takeAndBump"
    , "FinalizerStrategy: sequential parallel"
    , "NativeOp: refMake refGet refSet refGetAndSet refSetAndGet refUpdate refGetAndUpdate refUpdateAndGet refUpdateSome refGetAndUpdateSome refUpdateSomeAndGet refModify refModifySome deferredMake deferredIsDone deferredPoll deferredSucceed deferredFail deferredAwait scopeMake"
    , "MaskMode: interruptible uninterruptible inherit"
    , "ObserverMode: awaitValue joinEffect"
    , "ForkOptions: startImmediately daemon maskMode"
    , "Eff: succeed fail failCause yieldError sync suspend perform bind gen catchCause matchCause onExit exit uninterruptible interruptible branch whileLoop yieldNow callback awaitFiber withFiber scoped acquireRelease choose"
    , "Stmt: bindYield yieldDiscard ret ifElse whileTrue breakLoop"
    , "Stmts: nil cons"
    , "Effs: nil cons"
    , "ActionTerm: fork forkIn forkScoped runIn interrupt interruptScoped interruptAll awaitAll awaitAllFailFast snapshotChildren awaitNewChildren raceAll setContext getContext getId closeScope"
    , "tags: bool=1 nat=2 string=3 list=4 pair=5 none=6 some=7 bytes=8 unit=9 ctor=10" ]

def main (args : List String) : IO Unit := do
  match args with
  | [dir] =>
    IO.FS.createDirAll dir
    for (name, p) in Corpus.all do
      IO.FS.writeFile s!"{dir}/{name}.hex" (hex (encodeProgram p) ++ "\n")
    IO.FS.writeFile s!"{dir}/manifest.txt" (manifest ++ "\n")
    IO.println s!"wrote {Corpus.all.length} goldens and manifest.txt to {dir}"
  | _ =>
    IO.println manifest
    for (name, p) in Corpus.all do
      IO.println s!"{name}\t{hex (encodeProgram p)}"
