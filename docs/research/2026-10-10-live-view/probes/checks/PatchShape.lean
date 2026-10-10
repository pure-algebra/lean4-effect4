import ProbeView.Live

open Effect4 Effect4.Program Tools.View Tools.View.Build Tools.View.Retained Tools.View.Live

namespace Tools.View.PatchShape
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

/-- An object's kind by its key: a line or box at an address, a route, a region, or the page. -/
def kindOf (k : Key) : String :=
  if k.isEmpty then "page" else if k.startsWith "code:" then "code" else if (k.splitOn "→").length > 1 then "route"
  else if (k.splitOn "↺").length > 1 then "lane" else if (k.splitOn "/region").length > 1 then "region"
  else if k.startsWith "[" then "address" else "other"

def shape (name : String) (p : NativeEff) (k : Nat) : IO Unit := do
  match requests p with
  | none => pure ()
  | some reqs =>
    let st := (reqs.take (reqs.length - k)).foldl (fun st r => (step {} "t" st r).1) ({} : State)
    match reqs.drop (reqs.length - k) |>.head? with
    | none => pure ()
    | some r =>
      let (st', _, rows) := step {} "t" st r
      let pt := diff st.scene st'.scene
      let count (f : Op → Option String) : List (String × Nat) :=
        let ks := pt.ops.filterMap f
        ks.eraseDups.map fun x => (x, ks.count x)
      IO.println s!"{name}, step {reqs.length - k + 1} of {reqs.length} ({r.op} {r.path}): {rows.length} rows; order row {pt.order.isSome}"
      IO.println s!"   puts by kind: {count fun | .put id _ => some (kindOf id.key) | _ => none}"
      IO.println s!"   moves by kind: {count fun | .move id _ _ => some (kindOf id.key) | _ => none}"
      IO.println s!"   shifts: {count fun | .shift g _ _ => some g | _ => none}"
      let putCalls : List (String × Nat) := pt.ops.filterMap fun
        | .put id o => some (kindOf id.key, o.rel.length)
        | _ => none
      let kinds := (putCalls.map (·.1)).eraseDups
      IO.println s!"   calls by put kind: {kinds.map fun k => (k, (putCalls.filter (·.1 == k)).foldl (· + ·.2) 0)}"
end Tools.View.PatchShape

open Tools.View.PatchShape in
#eval show IO Unit from do
  shape "chain 12" (chain 12 0) 1
  shape "chain 12" (chain 12 0) 40
