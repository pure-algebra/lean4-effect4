import Tools.View.Live
import Tools.View.LiveChecks

/-! The landed live step's stages, timed on the last request of a build (the interpreter). -/

open Effect4 Effect4.Program Tools.View Tools.View.Build Tools.View.Retained Tools.View.Live
open Tools.View.LiveChecks (chain)

def timed {α : Type} (f : Unit → α) (size : α → Nat) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let _ := size a
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 100000)

def stages (name : String) (p : NativeEff) : IO Unit := do
  match requests p with
  | none => pure ()
  | some reqs =>
  match reqs.getLast? with
  | none => pure ()
  | some r =>
    let st := (reqs.dropLast).foldl (fun st r => (step {} "t" st r).1) ({} : State)
    let ((tool, _), tA) ← timed (fun _ => Tools.Session.answer st.tool r) (·.2.laws.length)
    match tool.session with
    | none => pure ()
    | some l =>
      let prog := l.sketch.program
      let edited := some r.path
      let (ls, tL) ← timed (fun _ => Inc.lines st.memo edited prog) (·.length)
      let (_, tLf) ← timed (fun _ => Program.lines prog) (·.length)
      let (pg, tP) ← timed (fun _ => Program.sessionPageOf l ls (some r.path) "t" "" "" "") (·.lines.size)
      let holes := l.sketch.holes.map (·.name)
      let (code, tC) ← timed (fun _ => Program.codePanel prog (l.app.withHoles l.sketch.holes).rows holes) fun c => (c.map (·.lines.size)).getD 0
      let (_, tW) ← timed (fun _ => Flow.waits prog) (·.length)
      let (fl, tF) ← timed (fun _ => Inc.flow st.memo edited prog) fun _ => 1
      let label (k : Key) : Option (String × String) := (pg.lines.toList.find? (·.key == k)).map fun l => (l.text, l.type)
      let (laid, tY) ← timed (fun _ => Flow.layout (fl.relabel label)) (·.placed.size)
      let pg := { pg with code, graph := some { title := "program", laid }, gutter := st.gutter, codeAt := st.codeAt }
      let ((gs, _), tK) ← timed (fun _ => pageGroups {} 1280 pg st.cache) (·.1.length)
      let (sc, tS) ← timed (fun _ => Scene.ofGroups gs) (·.order.length)
      let (pt, tD) ← timed (fun _ => diff st.scene sc) (·.ops.length)
      let (rows, tR) ← timed (fun _ => patchRows 2 1 pt) (·.length)
      let (_, tAll) ← timed (fun _ => step {} "t" st r) (·.2.2.length)
      IO.println s!"{name} ({pg.lines.size} lines), tenths of ms: answer {tA}; lines along the edit {tL} (fresh {tLf}); page {tP}; code {tC}; waits {tW}; flow {tF}; layout {tY}; groups {tK}; scene {tS}; diff {tD}; rows {tR} ({rows.length}); whole step {tAll}"

#eval show IO Unit from do
  IO.println s!"load: {(← IO.Process.output { cmd := "uptime" }).stdout.trimAscii}"
  stages "chain 12" (chain 12 0)
  stages "chain 18" (chain 18 0)
  stages "chain 24" (chain 24 0)
