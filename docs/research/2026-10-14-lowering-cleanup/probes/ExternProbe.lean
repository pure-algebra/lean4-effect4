import Lean
import OCaml5.Lcnf.Builtins
import Conform.Lcnf.Index
import Conform.Effect4.LcnfSemantics

/-! A probe: for each builtin row, whether the Lean constant is an extern, its C symbol, and
whether it has a persisted mono body; and whether the source evaluator's table names it. -/

open Lean Compiler LCNF

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4 }, { module := `OCaml5.Lcnf.Builtins },
    { module := `Conform.Effect4.LcnfSemantics }] {} 0
  let mono := Conform.Lcnf.persistedMonoIndex env
  for b in OCaml5.Lcnf.builtins do
    let n := b.lean
    let known := env.contains n
    let ext := (getExternAttrData? env n)
    let sym := getExternNameFor env `c n
    let body := (mono.findIn? env n).map fun d => match d.value with
      | .code _ => "code" | .extern _ => "extern"
    let prim := (Conform.Effect4.LcnfSemantics.tyPrims.lookup? n).map toString
    IO.println s!"{n}\tknown={known}\textern={ext.isSome}\tc={sym}\tmono={body}\tsource={prim}"
