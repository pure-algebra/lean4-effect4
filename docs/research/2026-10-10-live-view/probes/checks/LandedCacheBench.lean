import Tools.View.LiveChecks
import Tools.View.Motion

/-! The batch's pictures as `writeFrames` draws them (frames and moments of motion), each drawn
on a fresh stroke cache or on one cache carried along, in one process, interleaved. -/

open Effect4 Effect4.Program Tools.View Tools.View.Build
open Tools.View.LiveChecks (chain framesOf)

def countEntries {E : Type} : Tools.Graph.Index E → Nat
  | .empty => 0
  | .node h l r => h.length + countEntries l + countEntries r

def cubicsHeld : Tools.Graph.Index (Laid.StrokeKey × List Cubic) → Nat
  | .empty => 0
  | .node h l r => (h.map (·.2.length)).sum + cubicsHeld l + cubicsHeld r

/-- The pages `writeFrames` draws, in order: each step's moments, then its frame. -/
def pictures (L : Look) (frames : List Frame) (motion : Nat) : List Page :=
  match frames with
  | [] => []
  | first :: _ => first.page :: (frames.zip (frames.drop 1)).flatMap fun (a, b) =>
      (List.range' 1 (motion - 1)).map (fun k => sample L.motion a.page b.page (k * 1000 / motion)) ++ [b.page]

def rows (L : Look) (g : Page) (calls : List (Keyed Call)) : Nat :=
  let (W, H) := pageSize 1280 g
  (stream L W.toNat H.toNat 2 (lowerAll 2 calls)).length

def fresh (L : Look) (ps : List Page) : Nat :=
  ps.foldl (fun n g => n + rows L g (pageCalls L 1280 g)) 0

def carried (L : Look) (ps : List Page) : Nat × Laid.StrokeCache :=
  ps.foldl (fun (n, cache) g =>
    let (calls, cache) := pageCallsCached L 1280 g cache
    (n + rows L g calls, cache)) (0, {})

def ms (ns : Nat) : String := s!"{ns / 1000000}"

def bench (name : String) (p : NativeEff) (motion : Nat) : IO Unit := do
  let L : Look := {}
  let ps := pictures L (framesOf p) motion
  let _ ← IO.lazyPure fun _ => ps.length
  let mut out := s!"{name}, motion {motion}: {ps.length} pictures;"
  for round in [1, 2] do
    let t0 ← IO.monoNanosNow
    let a ← IO.lazyPure fun _ => fresh L ps
    let t1 ← IO.monoNanosNow
    let (b, cache) ← IO.lazyPure fun _ => carried L ps
    let t2 ← IO.monoNanosNow
    out := out ++ s!" round {round}: fresh {ms (t1 - t0)} ms, carried {ms (t2 - t1)} ms (rows {a} = {b}: {a == b});"
    if round == 2 then
      out := out ++ s!" cache {countEntries cache.index} strokes, {cubicsHeld cache.index} segments"
  IO.println out

#eval show IO Unit from do
  IO.println s!"load: {(← IO.Process.output { cmd := "uptime" }).stdout.trimAscii}"
  bench "pFork" Effect4.Program.Wire.Corpus.pFork 20
  bench "chain 6" (chain 6 0) 1
  bench "chain 4" (chain 4 0) 20
  bench "chain 6" (chain 6 0) 20
  IO.println s!"load: {(← IO.Process.output { cmd := "uptime" }).stdout.trimAscii}"
