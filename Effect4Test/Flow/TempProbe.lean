import Effect4.Layer.LayerFamily
import Effect4.Context.ContextFamily
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Flow.TempProbe

#eval IO.println (String.intercalate "\n" (Effect4.LayerFamily.layerPrograms.map (fun e =>
  e.name ++ " || " ++ String.intercalate " | " (e.log.map Effect4.Target.TypeScript.Trace.row))))

#eval IO.println "=== layer rows ==="
#eval IO.println (String.intercalate "\n"
  (Effect4.LayerFamily.Layers.rows.ops.map (fun r =>
    r.name ++ "\t" ++ r.tsAnswer ++ "\t" ++ String.intercalate "," (r.tsParams.map (·.2)))))

#eval IO.println "=== context logs ==="
#eval IO.println (String.intercalate "\n" (Effect4.ContextFamily.contextPrograms.map (fun e =>
  e.name ++ " || " ++ String.intercalate " | " (e.log.map Effect4.Target.TypeScript.Trace.row))))

#eval IO.println "=== context rows ==="
#eval IO.println (String.intercalate "\n"
  (Effect4.ContextFamily.Contexts.rows.ops.map (fun r =>
    r.name ++ "\t" ++ r.tsAnswer ++ "\t" ++ String.intercalate "," (r.tsParams.map (·.2)) ++ "\t" ++
      (match r.error with | some (a, b) => a ++ "/" ++ b | none => "-"))))

end Effect4Test.Flow.TempProbe
