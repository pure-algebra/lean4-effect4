import ProbeView.Live

/-!
Write, for a few programs built by edits, each step's patch rows (`NNN.patch`) and the full
stream of the same page (`NNN.draw`), into `out/NAME/`. `c/scene_test` applies the patches in C
and compares its flattened stream with each `NNN.draw`, byte for byte.
-/

open Effect4 Effect4.Program Tools.View Tools.View.Build Tools.View.Retained Tools.View.Live

namespace Tools.View.PatchFiles
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

def frameName (i : Nat) : String :=
  let s := toString i
  "".pushn '0' (3 - s.length) ++ s

def write (dir : System.FilePath) (name : String) (p : NativeEff) : IO Unit := do
  match requests p with
  | none => IO.println s!"{name}: none"
  | some reqs =>
    let out := dir / name
    IO.FS.createDirAll out
    let s : Settings := {}
    let mut st : State := {}
    for r in reqs do
      let (st', ans, rows) := step s "t" st r
      if !rows.isEmpty then
        match st'.tool.session with
        | none => pure ()
        | some l =>
          -- the full stream of the same page: the live page, drawn whole
          let g := (Live.page "t" r st'.tool ans l st.memo).1
          let g := { g with gutter := st'.gutter, codeAt := st'.codeAt }
          let (W, H) := pageSize s.width g
          let full := stream s.look W.toNat H.toNat s.ratio (lowerAll s.ratio st'.scene.flatten)
          IO.FS.writeFile (out / s!"{frameName st'.frame}.patch") ("\n".intercalate rows ++ "\n")
          IO.FS.writeFile (out / s!"{frameName st'.frame}.draw") ("\n".intercalate full ++ "\n")
      st := st'
    IO.println s!"{name}: {st.frame} frames in {out}"
end Tools.View.PatchFiles

open Tools.View.PatchFiles in
#eval show IO Unit from do
  let dir : System.FilePath := "docs/research/2026-10-10-live-view/probes/out"
  write dir "pFork" Effect4.Program.Wire.Corpus.pFork
  write dir "pScope" Effect4.Program.Wire.Corpus.pScope
  write dir "chain6" (chain 6 0)
