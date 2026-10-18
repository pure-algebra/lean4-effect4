import Effect4.Program.Typing.SourceDocument

/-! A run's historical document origin is data. Restored standalone runs invent no document.
The snapshot carrier comes from S1's document owner.
This stays non-module through Sketch's specialization-site imports (decisions row 202). -/
set_option autoImplicit false
namespace Effect4.Tool
inductive Origin where
  | snapshot (snap : Program.Snap) (app : Program.SigApp) (sketch : Program.Sketch)
  | standalone
end Effect4.Tool
