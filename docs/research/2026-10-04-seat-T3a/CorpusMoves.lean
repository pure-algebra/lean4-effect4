import Test.Program.Gen
import Effect4.Store.Domain.ProgramWire
import Effect4.Api

/-! Measurement for seat T3a's design note (phase 1): which committed corpus verdicts can T3a's
template rows move? The corpus is `generated/corpus-index.tsv`'s source: the 400 programs of
`Test.Program.Gen.program i 4` and `Wire.Corpus.all` (`tools/Drivers/Corpus.lean`).

For each program the checker refuses with `requestNotSubtype` at a `Ref` or `Deferred` row, the
probe prints the row, the request type, and whether the request matches the row's T3a template
under today's `checkRow` (`Ty.matchTemplate` and the formation check). A match means the refusal
at that node goes away: the program's verdict row (`wellTyped`, `reason`, `path`) can move. The
templates here are scratch copies of the design note's table, not the tree's rows. Replay:
`lake env lean docs/research/2026-10-04-seat-T3a/CorpusMoves.lean` under the shared lock. -/

open Effect4 Effect4.Program

namespace T3aProbe

def r0 : Ty := .refOf (.var 0)
def d01 : Ty := .deferredOf (.var 0) (.var 1)

/-- The T3a template of a row, by the row's name; `none` for a row T3a leaves closed. -/
def template? (name : String) : Option Row :=
  let mk (request answer : Ty) (error : Ty := .never) : Row :=
    { name, spelling := "", kind := .sync, request, answer, error, cite := "" }
  match name with
  | "refMake" => some (mk (.var 0) r0)
  | "refGet" => some (mk r0 (.var 0))
  | "refSet" => some (mk (.prod r0 (.var 0)) r0)
  | "refGetAndSet" => some (mk (.prod r0 (.var 0)) (.var 0))
  | "refSetAndGet" => some (mk (.prod r0 (.var 0)) (.var 0))
  | "deferredIsDone" => some (mk d01 .bool)
  | "deferredPoll" => some (mk d01 .bool)
  | "deferredSucceed" => some (mk (.prod d01 (.var 0)) .bool)
  | "deferredFail" => some (mk (.prod d01 (.var 1)) .bool)
  | "deferredAwait" => some (mk d01 (.var 0) (.var 1))
  | _ => none

def corpus : List (String × Eff NativeOp) :=
  ((List.range 400).map fun i => (s!"g{i}", Test.Program.Gen.program i 4)) ++ Wire.Corpus.all

end T3aProbe

open T3aProbe in
#eval show IO Unit from do
  let mut moved := 0
  let mut refusedAtRow := 0
  for (name, p) in corpus do
    match Api.explain p with
    | some ⟨path, .requestNotSubtype row request expected⟩ =>
      match template? row with
      | some t =>
        refusedAtRow := refusedAtRow + 1
        let accepts := (rowTy t.normalizeTypes request).isSome
        if accepts then moved := moved + 1
        IO.println s!"{name}\t{row}\tpath {path}\trequest {request.render}\texpected {expected.render}\tT3a template accepts: {accepts}"
      | none => pure ()
    | _ => pure ()
  IO.println s!"refused at a templated row: {refusedAtRow}; of them the template accepts: {moved}"

/-! Second measurement: admitted programs whose own annotations or checked type name a native
handle spelling. After T3a no value fits `Ref.Ref<number>` as a handle spelling, so such a program
could move from admitted to refused. -/

def T3aProbe.spellings : List String := ["Ref.Ref<number>", "Deferred.Deferred<number, number>"]

/-- Whether a raw type mentions one of the two native handle spellings. -/
def T3aProbe.mentions (t : Ty) : Bool :=
  (Formation.nodes t).any fun
    | .handle target | .app target _ => T3aProbe.spellings.contains target
    | _ => false

open T3aProbe in
#eval show IO Unit from do
  let mut hits := 0
  for (name, p) in corpus do
    let annotated := (Formation.programAnnotations p).any fun (_, t) => mentions t
    let typed := match Api.typeOf p [] with
      | some t => mentions t.answer || mentions t.error
      | none => false
    if annotated || typed then
      hits := hits + 1
      IO.println s!"{name}\tannotation {annotated}\ttype {typed}\twellTyped {Api.wellTyped p}"
  IO.println s!"programs naming a native handle spelling in an annotation or their type: {hits}"
