import Effect4.Program.Typing.SourceDocument

/-! A run's historical document origin is data. Restored standalone runs invent no document.
The snapshot carrier comes from S1's document owner.
This stays non-module through Sketch's specialization-site imports (decisions row 202). -/
set_option autoImplicit false
namespace Effect4.Tool
/-- **Where a run came from.** -/
inductive Origin where
  /-- started from a document at this snapshot, with the application and sketch it held then -/
  | snapshot (snap : Program.Snap) (app : Program.SigApp) (sketch : Program.Sketch)
  /-- restored from a saved record, with no document -/
  | standalone
end Effect4.Tool
