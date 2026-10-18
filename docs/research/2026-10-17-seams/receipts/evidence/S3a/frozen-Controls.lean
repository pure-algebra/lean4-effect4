import Effect4.Tool.Serve
set_option autoImplicit false
namespace Test.SeamsTool
open Effect4 Effect4.Program Program.Check Tool

def ask : Row :=
  { name := "ask", spelling := "ask", kind := .async, registration := .external,
    request := .unit, answer := .nat, cite := "S3a loop1" }
def app : SigApp := .ofTable [ask]
def program : NativeEff :=
  .bind (.perform (.external 0) (.lit .unit)) (.succeed (.var 0))
def opened := (serve Oracle.uncached empty (.act (.open_ "demo" app ⟨program,[]⟩))).value
def snap : Snap := ⟨⟨"demo",0⟩,0⟩
def started := (serve Oracle.uncached opened.1 (.act (.start snap {}))).value
#guard started.1.transcript.length = 2
#guard match started.2.result with
  | .ok (.acted (.started ⟨0⟩ (.snapshot saved originApp originSketch) view)) =>
    saved.doc.name == "demo" && saved.revision == 0 &&
    originApp.rows.length == 1 && originSketch.program == program && view.awaiting.length == 1
  | _ => false

def premature := (serve Oracle.uncached started.1
  (.act (.play ⟨0⟩ [.apply (.row "ask")]))).value
#guard premature.1.transcript.length = 3
#guard premature.1.raw.runs[0]?.map (fun entry => entry.live.run.journal.length) = some 2

def finished := (serve Oracle.uncached premature.1 (.act (.play ⟨0⟩
  [.receive (.key ⟨Api.root,0⟩) (.ofExit (.success (.nat 7))),
   .apply (.key ⟨Api.root,0⟩), .flush]))).value
#guard finished.1.transcript.length = 4
#guard finished.1.raw.runs[0]?.map (fun entry => entry.live.run.exit) =
  some (some (.success (.nat 7)))

-- A successful prefix is discarded when the later selector cannot resolve.
def rolledBack := (serve Oracle.uncached started.1 (.act (.play ⟨0⟩
  [.flush,.apply (.row "missing")]))).value
#guard !rolledBack.2.result.isOk
#guard rolledBack.1.transcript.length = started.1.transcript.length
#guard rolledBack.1.raw.runs[0]?.map (fun entry => entry.live.run.journal) =
  started.1.raw.runs[0]?.map (fun entry => entry.live.run.journal)

-- Dry runs answer the action while retaining the original run list and transcript.
def dry := (serve Oracle.uncached opened.1 (.ask (.dry (.start snap {})))).value
#guard dry.1.transcript.length = 1
#guard dry.1.raw.runs.isEmpty
#guard match dry.2.result with | .ok (.dry (.ok (.started ..))) => true | _ => false
end Test.SeamsTool
