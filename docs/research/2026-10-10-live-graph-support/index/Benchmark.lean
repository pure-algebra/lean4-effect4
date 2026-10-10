import Tools.View.Flow

open Tools.Graph Tools.View Tools.View.Flow

namespace GraphIndexBenchmark

/-- Chain constraints, with one edge occurrence per adjacent item. -/
def chain (n : Nat) : List Edge :=
  (List.range (n - 1)).map fun i => { fr := i, to := i + 1 }

/-- Consume every retained height so the benchmark measures actual assignments. -/
def checksum (xs : List (Nat × Int)) : Int := xs.foldl (fun total item => total + item.2) 0

/-- The retained reference calculation. -/
@[noinline] def reference (h : Nat → Int) (es : List Edge) (ord : List Nat)
    (start : Int) : Int := checksum (assignHeights h es start ord [])

/-- The indexed calculation includes construction of the sparse index in each measurement. -/
@[noinline] def indexed (h : Nat → Int) (es : List Edge) (ord : List Nat)
    (start : Int) : Int :=
  checksum (assignHeightsIndexed h (Index.ofList (·.to) es) start ord [])

/-- Wall-clock measurement surrounds the actual Lean calculation and checksum. -/
def measure (mode implementation : String) (n sample : Nat) (work : Nat → Int) : IO Int := do
  let slot ← IO.mkRef (0 : Int)
  let before ← IO.monoNanosNow
  slot.set (work (before % 1024))
  let after ← IO.monoNanosNow
  let answer ← slot.get
  IO.println s!"{mode}\t{implementation}\t{n}\t{sample}\t{after - before}\t{answer}"
  pure answer

/-- Paired runs alternate their order, retaining the same constraints and item-height function. -/
def paired (mode : String) (n : Nat) (h : Nat → Int) : IO Unit := do
  let es := chain n
  let ord := List.range n
  for sample in [0, 1, 2] do
    let start := Int.ofNat sample
    let (old, fresh) ← if sample % 2 = 0 then do
        let old ← measure mode "reference" n sample (fun salt => reference h es ord (start + Int.ofNat salt) -
          Int.ofNat salt * Int.ofNat n)
        let fresh ← measure mode "indexed" n sample (fun salt => indexed h es ord (start + Int.ofNat salt) -
          Int.ofNat salt * Int.ofNat n)
        pure (old, fresh)
      else do
        let fresh ← measure mode "indexed" n sample (fun salt => indexed h es ord (start + Int.ofNat salt) -
          Int.ofNat salt * Int.ofNat n)
        let old ← measure mode "reference" n sample (fun salt => reference h es ord (start + Int.ofNat salt) -
          Int.ofNat salt * Int.ofNat n)
        pure (old, fresh)
    unless old == fresh do throw (IO.userError "assignment checksum differs")

/-- Microbenchmark of assignment, excluding layout, wait analysis, Kahn and rendering. -/
def run : IO Unit := do
  IO.println "mode\timplementation\titems\tsample\tnanoseconds\tchecksum"
  for n in [200, 500, 1000, 2000] do
    paired "constant-item-height" n (fun _ => 0)
    let items := (List.range n).map fun _ => pointAt "" 0
    paired "list-item-height" n (hAt items)

end GraphIndexBenchmark

def main : IO Unit := GraphIndexBenchmark.run
