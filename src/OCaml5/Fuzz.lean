import OCaml5.Fuzz.Term
import OCaml5.Fuzz.Corpus
import OCaml5.Fuzz.Tape

/-!
# OCaml5.Fuzz — the fuzz driver

`ocaml/tools/fuzz.sh` runs `main` below with a subcommand (`lake env lean --run
src/OCaml5/Fuzz.lean …`): `witnesses`, `surface`, `avatar`, `corpus`, `tapes`, `gen`, `cands`,
`one`. Each writes files derived from a seed and prints one summary line; the shell compiles
what was written on the hosts of ruling 7 and compares rows. A thin driver: the generators are
`OCaml5.Fuzz.Gen`, `OCaml5.Fuzz.Term`, `OCaml5.Fuzz.Corpus` and `OCaml5.Fuzz.Tape`.
-/

namespace OCaml5.Fuzz

/-! ## The driver

`fuzz.sh` calls `main` with a subcommand. Everything it writes is derived from a seed, so the
files under `fuzz/` are a cache, not a source. -/

private def rowsText (rows : List String) : String :=
  String.join (rows.map (· ++ "\n"))

private def natOf (s : String) : Nat := (s.toNat?).getD 0

private def writeProgram (dir : String) (name : String) (t : T) (v : Verdict) : IO Unit := do
  IO.FS.writeFile (dir ++ "/" ++ name ++ ".ml") (Term.render t)
  IO.FS.writeFile (dir ++ "/" ++ name ++ ".rows") (rowsText v.rows)

/-- `gen <dir> <firstSeed> <count> <size>`: emit the accepted programs of the seed range, one
`.ml` and one `.rows` each, plus a TSV manifest of every seed with its verdict. -/
def cmdGen (dir : String) (first count size : Nat) : IO Unit := do
  let mut manifest := ""
  let mut kept := 0
  for j in [0:count] do
    let seed := first + j
    let t := programOf seed size
    let v := classify t
    if v.ok then
      let name := "p" ++ toString seed
      writeProgram dir name t v
      kept := kept + 1
      manifest := manifest ++ s!"{seed}\tok\t{v.outcome}\t{v.rows.length}\n"
    else
      manifest := manifest ++ s!"{seed}\t{v.reason}\t{v.outcome}\t{v.rows.length}\n"
  IO.FS.writeFile (dir ++ "/manifest.tsv") manifest
  IO.println s!"kept {kept} of {count}"

/-- `cands <dir> <seed> <size> <path…>`: emit every one-step reduction of the term at `path`
that the machine still accepts, as `c<i>.ml` / `c<i>.rows`, and print their indices. -/
def cmdCands (dir : String) (seed size : Nat) (path : List Nat) : IO Unit := do
  match stepsOf seed size path with
  | Option.none => IO.println "no-such-path"
  | Option.some t =>
    let cs := shrinks t
    let mut names := ""
    for i in [0:cs.length] do
      match cs[i]? with
      | Option.none => pure ()
      | Option.some t' =>
        let v := classify t'
        if v.ok then
          writeProgram dir ("c" ++ toString i) t' v
          names := names ++ toString i ++ "\n"
    IO.FS.writeFile (dir ++ "/cands.txt") names
    IO.println s!"cands {cs.length}"

/-- `one <dir> <name> <seed> <size> <path…>`: emit exactly the term at `path`. -/
def cmdOne (dir name : String) (seed size : Nat) (path : List Nat) : IO Unit := do
  match stepsOf seed size path with
  | Option.none => IO.println "no-such-path"
  | Option.some t =>
    let v := classify t
    writeProgram dir name t v
    IO.println s!"{v.reason}\t{v.outcome}\t{v.rows.length}"

/-- `witnesses <dir>`: render the thirteen witnesses of `OCaml5.Witnesses` and their machine
rows, so `fuzz.sh --witnesses` can check `render` against the corpus the hosts already ran. -/
def cmdWitnesses (dir : String) : IO Unit := do
  for w in corpus do
    IO.FS.writeFile (dir ++ "/" ++ w.name ++ ".ml") (Term.render w.term)
    IO.FS.writeFile (dir ++ "/" ++ w.name ++ ".rows") (rowsText (Witness.machineRows w))
    IO.FS.writeFile (dir ++ "/" ++ w.name ++ ".byte-expected") (rowsText w.byteRows)
  IO.println s!"witnesses {corpus.length}"

/-- `surface <dir>`: render `OCaml5.Avatar.Probe.sample`, the A0 shape probe — the slice of
`src/Effect4/Machine/Fibers.lean` written in the `Ml` declaration surface — and the rows it prints, so
`fuzz.sh surface` can compile and run it on the three hosts. -/
def cmdSurface (dir : String) : IO Unit := do
  IO.FS.writeFile (dir ++ "/surface.ml") (Ml.moduleText Avatar.Probe.sample)
  IO.FS.writeFile (dir ++ "/surface.rows") (rowsText Avatar.Probe.sampleRows)
  IO.println s!"surface {Avatar.Probe.sample.length} declarations"

/-- `avatar <dir>`: render the generated part of the avatar (`OCaml5.Avatar.Fibers`, spike A0's
requests 1, 2, 3 and 5) twice — the fragment on its own, for the diff against
`ocaml/avatar/deep_fibers.ml`, and closed with its hand-written preamble, for the
compile check. -/
def cmdAvatar (dir : String) : IO Unit := do
  IO.FS.writeFile (dir ++ "/generated.ml") (Ml.moduleText Avatar.Fibers.generated)
  IO.FS.writeFile (dir ++ "/avatar_check.ml") (Ml.moduleText Avatar.Fibers.checkModule)
  IO.println (s!"avatar {Avatar.Fibers.generated.length} declarations, "
    ++ s!"{Avatar.Fibers.frameFiber.holes.length} holes in FrameFiber")

/-- `tapes <dir> <seed> <count> <len>`: `count` tapes of `len` decisions over four fibers, as one
wire file and one OCaml module. `fuzz.sh tapes` compiles the module on the three hosts, so every
generated tape is a well-typed `run_decision list` before anything tries to replay it. -/
def cmdTapes (dir : String) (seed count len : Nat) : IO Unit := do
  let (tapes, _) :=
    (((List.range count).foldl (fun (acc : Gen (List (List TapeEntry))) _ => do
        let xs ← acc
        let t ← genTape len 4
        return xs ++ [t]) (pure [])) (rngOf seed))
  IO.FS.writeFile (dir ++ "/tapes.wire")
    (String.join (tapes.map fun t =>
      String.intercalate " | " (t.map (·.wire)) ++ "\n"))
  IO.FS.writeFile (dir ++ "/tapes.ml")
    (Ml.moduleText (Avatar.Fibers.tapeModule (tapes.map fun t => t.map (·.expr))))
  IO.println s!"tapes {tapes.length} of {len} decisions"

/-- `corpus <dir> <first> <count>`: the round-four corpus. Seeds are `first … first+count-1`
and the size of each is a fixed function of its seed, so the schedule is reproducible from the
two numbers alone. Writes `<dir>/<name>/{fixture.ml,fixture.ts,tape,meta.json}` per program,
plus the two aggregates a runner links — `corpus_fixture.ml` and `corpus-fixture.ts` — and an
index. -/
def cmdCorpus (dir : String) (first count : Nat) : IO Unit := do
  let seeds := (List.range count).map (first + ·)
  let progs := seeds.map fun sd => Corpus.genProg sd (5 + (sd * 7 + 3) % 36)
  for p in progs do
    let pdir := dir ++ "/" ++ p.name
    IO.FS.createDirAll pdir
    IO.FS.writeFile (pdir ++ "/fixture.ml") p.mlFile
    IO.FS.writeFile (pdir ++ "/fixture.ts") p.tsFile
    IO.FS.writeFile (pdir ++ "/tape") (p.tapeText ++ "\n")
    IO.FS.writeFile (pdir ++ "/meta.json") p.metaJson
  IO.FS.writeFile (dir ++ "/corpus_fixture.ml") (Corpus.aggregateMl progs)
  IO.FS.writeFile (dir ++ "/corpus-fixture.ts") (Corpus.aggregateTs progs)
  IO.FS.writeFile (dir ++ "/index.tsv")
    ("name\tseed\tops\tforks\tfamilies\tusesExtra\ttape\n" ++
     String.join (progs.map fun p =>
       s!"{p.name}\t{p.seed}\t{p.ops.length}\t{p.forks}\t" ++
       String.intercalate "+" p.services ++ "\t" ++
       (if p.usesExtra then "yes" else "no") ++ "\t" ++ p.tapeText ++ "\n"))
  let opTotal := (progs.map (·.ops.length)).foldl (· + ·) 0
  let forkTotal := (progs.map (·.forks)).foldl (· + ·) 0
  let extra := (progs.filter (·.usesExtra)).length
  IO.println (s!"corpus {progs.length} programs, {opTotal} operations, {forkTotal} forks, "
    ++ s!"{extra} using the extra rows")

def main (args : List String) : IO Unit := do
  match args with
  | ["witnesses", dir] => cmdWitnesses dir
  | ["surface", dir] => cmdSurface dir
  | ["avatar", dir] => cmdAvatar dir
  | ["corpus", dir, first, count] => cmdCorpus dir (natOf first) (natOf count)
  | ["tapes", dir, seed, count, len] =>
      cmdTapes dir (natOf seed) (natOf count) (natOf len)
  | ["gen", dir, first, count, size] =>
      cmdGen dir (natOf first) (natOf count) (natOf size)
  | "cands" :: dir :: seed :: size :: path =>
      cmdCands dir (natOf seed) (natOf size) (path.map natOf)
  | "one" :: dir :: name :: seed :: size :: path =>
      cmdOne dir name (natOf seed) (natOf size) (path.map natOf)
  | _ => IO.println ("usage: witnesses DIR | surface DIR | avatar DIR | corpus DIR FIRST COUNT | tapes DIR SEED COUNT LEN | gen DIR FIRST COUNT SIZE"
      ++ " | cands DIR SEED SIZE PATH… | one DIR NAME SEED SIZE PATH…")


end OCaml5.Fuzz


/-- `lake env lean --run src/OCaml5/Fuzz.lean …`, which is how `tools/fuzz.sh` drives
this module. -/
def main (args : List String) : IO Unit := OCaml5.Fuzz.main args
