import Effect4.Api.Author
import Effect4.Api.HostSession
import Effect4.Api
import Effect4.Schema.Codec
import TypeScript.Render

/-!
# Seat R, question 5: the stage-1 acceptance harness, as a skeleton that compiles today

Type-language probe, 2026-10-01. The data probe's `ProbeTodayP2.lean` (programs seat), re-spelled
with records: p2's handler (`docs/research/2026-09-30-model-probe/programs/ts/p2-handler-layers.ts`
`:58-106`, handler only) authored through `Api.Author` with two host rows, checked at answer
`Response`, run through the live keyed session (`Api/HostSession.lean`) against a scripted host
that answers rc.112's objects as JSON, the answers laid out by the row adapter (route A), printed,
read back, and compared with rc.112's three answers (`hostruns.log`:
`{"status":200,"body":"bob"}`, `{"status":404,"body":"no user 9"}`,
`{"status":401,"body":"bad token"}`).

Everything here is the tree's code except the parts the data wave adds, which are an interface
(`DataWave`) assembled from `parts`, each `none` today and named by the seat and commit that owns
it. The harness is written against the interface, so it is complete today and checks nothing yet;
commit 8 is the diff that fills `parts` and turns the two `none` pins below into the acceptance:
`acceptance = some expected` and `missing = []`.

What stays as in `ProbeTodayP2.lean`, and why (the bounded target of synthesis §3.2, Codex's
practical review item 5): the errors are DB-15's literal-tagged pairs (payloads are stage 3); the
id's decimal text is threaded by the caller (`natToString` is row 131); the query and the decode
live in the host, which answers the decoded record (route A); `CurrentUser` is a value, since a
structured service carrier is row 118's. Not a stage-1 obligation: the full layered program.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Probe.P2Records
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api.HostSession

/-! ## 1. What the data wave supplies -/

/-- The parts the acceptance needs from the data wave. -/
structure DataWave where
  /-- Seat P, commit 4: `Ty.record (fields : List (String × Ty))`, canonical order by name. -/
  recordTy : List (String × Ty) → Ty
  /-- Seat R, commit 6: the authoring builders of `Term.record` (written order kept) … -/
  record : List (String × TermSrc) → TermSrc
  /-- … and of `Term.field` (by name; the position, if row 119's value clause keeps positional
  values, is resolved by the checker). -/
  field : TermSrc → String → TermSrc
  /-- Seat S, commit 5: the codec's record arm, `Schema.encode` at a record type (strict). -/
  encode : Ty → Val → Option Json
  /-- Seat S, commit 5: the strict decoder, for the paired control. -/
  decode : Ty → Json → Option Val
  /-- Route A (Q4 of seat R): the row adapter, host JSON laid out at a row's answer type, extra
  keys dropped. -/
  adapt : Ty → Json → Option Val

/-- The parts, each `none` until its commit lands. -/
structure Parts where
  recordTy? : Option (List (String × Ty) → Ty) := none
  record? : Option (List (String × TermSrc) → TermSrc) := none
  field? : Option (TermSrc → String → TermSrc) := none
  encode? : Option (Ty → Val → Option Json) := none
  decode? : Option (Ty → Json → Option Val) := none
  adapt? : Option (Ty → Json → Option Val) := none

/-- Today: none of them. Commit 8's diff fills this structure and nothing else in sections 2-6. -/
def parts : Parts := {}

def Parts.missing (p : Parts) : List String :=
  (if p.recordTy?.isSome then [] else ["Ty.record (seat P, data-wave commit 4)"]) ++
  (if p.record?.isSome then [] else ["Term.record and its authoring builder (seat R, commit 6)"]) ++
  (if p.field?.isSome then [] else ["Term.field and its authoring builder (seat R, commit 6)"]) ++
  (if p.encode?.isSome then [] else ["the codec's record arm, encode (seat S, commit 5)"]) ++
  (if p.decode?.isSome then [] else ["the codec's record arm, decode (seat S, commit 5)"]) ++
  (if p.adapt?.isSome then [] else ["the row adapter at a record answer (route A, commit 8)"])

def Parts.assemble (p : Parts) : Option DataWave := do
  let recordTy ← p.recordTy?
  let record ← p.record?
  let field ← p.field?
  let encode ← p.encode?
  let decode ← p.decode?
  let adapt ← p.adapt?
  pure { recordTy, record, field, encode, decode, adapt }

/-! ## 2. The data and the handler, against the interface -/

section Handler
variable (F : DataWave)

/-- `role: Schema.Literals(["admin", "member"])` (p2:29): exact today. -/
def roleTy : Ty := .union (.lit "admin") (.lit "member")
/-- `User = { id: number, name: string, role }` (p2:26-30). -/
def userTy : Ty := F.recordTy [("id", .nat), ("name", .string), ("role", roleTy)]
/-- `AppConfig = { adminToken: string, pageSize: number }` (p2:37-40). -/
def configTy : Ty := F.recordTy [("adminToken", .string), ("pageSize", .nat)]
/-- `Response = { status: number, body: string }` (p2:96-99). -/
def responseTy : Ty := F.recordTy [("status", .nat), ("body", .string)]
/-- `SqlError | SchemaError`, crossing as DB-15's pair through the row adapter's `toPair`. -/
def infraErrTy : Ty := .prod .string .string

def getConfig : RowDef := Row.host "AppConfig.get" .unit (configTy F) .never "p2-handler-layers.ts:51-55"
def findById : RowDef :=
  Row.host "UserRepo.findById" .nat (.option (userTy F)) infraErrTy "p2-handler-layers.ts:58-70"

def response (status body : TermSrc) : TermSrc := F.record [("status", status), ("body", body)]

/-- p2:62-67, the decode in the host. -/
def findOrFail (id idText : TermSrc) : Src NativeOp :=
  bindName "found" (Row.call (findById F) id) fun found =>
    selectOption "user" found
      (fail (app "pair" [str "NotFound", idText]))
      (succeed (var "user"))

/-- `getProfile(id)` (p2:85-93): `me.role !== "admin" && me.id !== id`. -/
def getProfile (me id idText : TermSrc) : Src NativeOp :=
  ifElse (app "and" [app "not" [app "eq" [F.field me "role", str "admin"]],
                     app "not" [app "eq" [F.field me "id", id]]])
    (fail (app "pair" [str "Unauthorized", str "not yours"]))
    (findOrFail F id idText)

/-- `withAuth(token, getProfile(id))` (p2:74-83): `token !== config.adminToken`. -/
def withAuth (token id idText : TermSrc) : Src NativeOp :=
  bindName "config" (Row.call (getConfig F) unit) fun config =>
    ifElse (app "not" [app "eq" [token, F.field config "adminToken"]])
      (fail (app "pair" [str "Unauthorized", str "bad token"]))
      (bindName "me" (findOrFail F (nat 1) (str "1")) fun me =>
        getProfile F me id idText)

/-- `handle(token, id)` (p2:101-106): `{ status: 200, body: user.name }` and the two tagged
failures as 404 and 401 responses. -/
def handle (token id idText : TermSrc) : Src NativeOp :=
  catchIf "e" (app "tagIs" [str "NotFound", var "e"])
    (catchIf "e2" (app "tagIs" [str "Unauthorized", var "e2"])
      (bindName "user" (withAuth F token id idText) fun user =>
        succeed (response F (nat 200) (F.field user "name")))
      (succeed (response F (nat 401) (app "snd" [var "e2"]))))
    (succeed (response F (nat 404) (app "concat" [str "no user ", app "snd" [var "e"]])))

def caseModule (token : String) (id : Nat) (idText : String) : Module NativeOp :=
  { rows := [getConfig F, findById F], main := handle F (str token) (nat id) (str idText) }

end Handler

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

/-! ## 3. The scripted host: rc.112's objects, laid out by the row adapter -/

def num (n : Nat) : Json := Effect4.Arch.Json.ofNat n

/-- The users table of `run-p2.ts:13`, as rc.112's decoder hands each row to the program, with one
column the type does not name (`createdAt`), which the adapter drops. -/
def userJson : Nat → Option Json
  | 1 => some (.obj [("role", .str "admin"), ("id", num 1), ("createdAt", num 0), ("name", .str "ada")])
  | 2 => some (.obj [("name", .str "bob"), ("createdAt", num 0), ("id", num 2), ("role", .str "member")])
  | _ => none

/-- rc.112's `Schema.toCodecJson` image of an `Option` (`Schema.ts:9720-9734`). -/
def optionJson : Option Json → Json
  | none => .obj [("_tag", .str "None")]
  | some v => .obj [("_tag", .str "Some"), ("value", v)]

def configJson : Json := .obj [("pageSize", num 20), ("adminToken", .str "secret")]

abbrev HostAnswer := Completion Val Err Defect FiberId Ann

def jsonHost (F : DataWave) (b : Effect4.Api.Built) (op : NativeOp) (request : Val) :
    Option HostAnswer :=
  match op with
  | .external i =>
    if some i = b.positionOf "AppConfig.get" then
      (F.adapt (configTy F) configJson).map fun v => .ofExit (.success v)
    else if some i = b.positionOf "UserRepo.findById" then
      match request with
      | .nat n => (F.adapt (.option (userTy F)) (optionJson (userJson n))).map fun v => .ofExit (.success v)
      | _ => none
    else none
  | _ => none

/-! ## 4. The keyed session driver (as `ProbeTodayP2.lean`) -/

structure Driver (b : Effect4.Api.Built) where
  session : Session b.program b.table
  refused : List Effect4.Api.HostSession.Refusal := []
  stopped : Bool := false

def step (b : Effect4.Api.Built) (host : Effect4.Api.Built → NativeOp → Val → Option HostAnswer)
    (d : Driver b) : Driver b :=
  if d.stopped then d else
  let s := d.session
  match outstanding s with
  | (fiber, token, op, request) :: _ =>
    let call : Call := ⟨version, "p2", b.table, s.nextCall, fiber, op, request⟩
    let r1 := bindCall s call token
    match r1.phase with
    | .refused why => { d with refused := d.refused ++ [why], stopped := true }
    | _ =>
      match host b op request with
      | none => { d with session := r1.session, stopped := true }
      | some completion =>
        let reply : Reply := ⟨version, "p2", call.callId, ⟨fiber, token⟩, completion⟩
        let r2 := submit r1.session reply
        match r2.phase with
        | .refused why => { d with session := r1.session, refused := d.refused ++ [why], stopped := true }
        | _ => { d with session := (applyReply r2.session reply.key 1000).session }
  | [] => { d with session := (advance s 1000 Api.flush).session }

def drive (b : Effect4.Api.Built) (host : Effect4.Api.Built → NativeOp → Val → Option HostAnswer) :
    Nat → Driver b → Driver b
  | 0, d => d
  | n + 1, d => drive b host n (step b host d)

def runLive (m : Module NativeOp) (host : Effect4.Api.Built → NativeOp → Val → Option HostAnswer) :
    Option (Option ExitV × List Effect4.Api.HostSession.Refusal) :=
  (built? m).bind fun b =>
    match start b.program b.table "p2" ⟨version, "p2", "p2", b.table⟩ 1000 with
    | .error _ => none
    | .ok s0 =>
      let d := drive b host 60 { session := (advance s0 1000 Api.evaluate).session }
      some ((d.session.machine.fiber? Api.root).bind (·.exit), d.refused)

/-! ## 5. The comparison with rc.112's answers, modulo object key order (`N_J`) -/

/-! ## 1. Names, their order, the canonical field list -/

/-- The UTF-8 byte order on names: the key order `Ty.key` uses for a `lit` (`Ty.lean:155-176`). -/
def nameLt (a b : String) : Bool :=
  Effect4.Program.Ty.ltKey (Effect4.Program.Ty.key (.lit a)) (Effect4.Program.Ty.key (.lit b))

/-- Insert by name; an equal name already present wins, so a left fold keeps the first. -/
def ins {α : Type} (p : String × α) : List (String × α) → List (String × α)
  | [] => [p]
  | q :: qs => if nameLt p.1 q.1 then p :: q :: qs else if p.1 = q.1 then q :: qs else q :: ins p qs

/-- Canonical field order: ascending by name, the first of a repeated name kept. -/
def canon {α : Type} (xs : List (String × α)) : List (String × α) :=
  xs.foldl (fun acc p => ins p acc) []

theorem ins_map {α β : Type} (f : α → β) (p : String × α) (l : List (String × α)) :
    ins (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) = (ins p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [List.map_cons, ins, if_pos h1]
    · by_cases h2 : p.1 = q.1
      · simp only [List.map_cons, ins, if_neg h1, if_pos h2]
      · simp only [List.map_cons, ins, if_neg h1, if_neg h2, ih]

theorem foldl_ins_map {α β : Type} (f : α → β) (xs acc : List (String × α)) :
    (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => ins p a) (acc.map (fun q => (q.1, f q.2))) =
      (xs.foldl (fun a p => ins p a) acc).map (fun q => (q.1, f q.2)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ins_map f x acc]
    exact ih (ins x acc)

/-- The canonicaliser is payload-polymorphic: it commutes with any map of the payloads. -/
theorem canon_map {α β : Type} (f : α → β) (xs : List (String × α)) :
    canon (xs.map (fun q => (q.1, f q.2))) = (canon xs).map (fun q => (q.1, f q.2)) :=
  foldl_ins_map f xs []

theorem mem_ins {α : Type} (p x : String × α) (l : List (String × α)) (h : x ∈ ins p l) :
    x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [ins, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [ins, if_pos h1, List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · by_cases h2 : p.1 = q.1
      · simp only [ins, if_neg h1, if_pos h2] at h
        exact Or.inr h
      · simp only [ins, if_neg h1, if_neg h2, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

theorem mem_foldl_ins {α : Type} (x : String × α) (xs acc : List (String × α))
    (h : x ∈ xs.foldl (fun a p => ins p a) acc) : x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons y ys ih =>
    simp only [List.foldl_cons] at h
    rcases ih (ins y acc) h with h' | h'
    · rcases mem_ins y x acc h' with h'' | h''
      · exact Or.inr (List.mem_cons.mpr (Or.inl h''))
      · exact Or.inl h''
    · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- Every field of the canonical list is a field of the input. -/
theorem mem_canon {α : Type} (x : String × α) (xs : List (String × α)) (h : x ∈ canon xs) :
    x ∈ xs := by
  rcases mem_foldl_ins x xs [] h with h' | h'
  · cases h'
  · exact h'

/-- The value of a name in a field list, first match. -/
def lookupName {α : Type} (n : String) : List (String × α) → Option α
  | [] => none
  | (m, a) :: rest => if m = n then some a else lookupName n rest


mutual
/-- `N_J`: object entries in canonical key order, recursively. -/
def normJ : Json → Json
  | .obj entries => .obj (canon (normEntries entries))
  | .arr xs => .arr (normList xs)
  | j => j
def normEntries : List (String × Json) → List (String × Json)
  | [] => []
  | (k, v) :: rest => (k, normJ v) :: normEntries rest
def normList : List Json → List Json
  | [] => []
  | x :: xs => normJ x :: normList xs
end

/-- The three requests of `run-p2.ts:18` and rc.112's answers there. -/
def cases : List (String × Nat × String × Json) :=
  [ ("secret", 2, "2", .obj [("status", num 200), ("body", .str "bob")])
  , ("secret", 9, "9", .obj [("status", num 404), ("body", .str "no user 9")])
  , ("wrong", 2, "2", .obj [("status", num 401), ("body", .str "bad token")]) ]

/-- One case: the exit's success value encoded at `Response` by the codec, against rc.112's JSON. -/
def caseAgrees (F : DataWave) (c : String × Nat × String × Json) : Option Bool := do
  let (exit?, refused) ← runLive (caseModule F c.1 c.2.1 c.2.2.1) (jsonHost F)
  let exit ← exit?
  match exit with
  | .success v => do
    let j ← F.encode (responseTy F) v
    pure (normJ j == normJ c.2.2.2 && refused.isEmpty)
  | .failure _ => pure false

/-! ## 6. The acceptance report -/

structure Report where
  /-- The checked type: answer `Response`, error the infrastructure pair. -/
  checked : Bool
  /-- The three answers equal rc.112's, modulo key order, with no refusal. -/
  answers : List Bool
  /-- The printed module reads back as the built program (`Api.readModule`). -/
  readBack : Bool
  /-- The paired control at the harness: the adapter strips `createdAt`, the codec refuses it. -/
  paired : Bool
deriving DecidableEq, Repr

def report (F : DataWave) : Option Report := do
  let m := caseModule F "secret" 2 "2"
  let b ← built? m
  let checked := b.admitted.ty.answer == (responseTy F).normalize && b.admitted.ty.error == infraErrTy
  let answers ← cases.mapM (caseAgrees F)
  let module ← Effect4.Api.printModule "handle" b.program b.table
  let readBack := match Effect4.Api.readModule module b.table with
    | .ok p => decide (p = b.program)
    | .error _ => false
  let wide ← userJson 2
  let paired := (F.adapt (userTy F) wide).isSome && (F.decode (userTy F) wide).isNone
  pure { checked, answers, readBack, paired }

def acceptance : Option Report := parts.assemble.bind report

/-- What commit 8 must reach: `acceptance = some expected`. -/
def expected : Report := { checked := true, answers := [true, true, true], readBack := true, paired := true }

/-- The printed module, rendered, for the `tsgo` check against p2's idiomatic signatures
(`R/host/p2/printed-p2-records.ts` is the text it must equal, up to the prelude and the row
declarations that file adds). -/
def printedText : Option String := do
  let F ← parts.assemble
  let b ← built? (caseModule F "secret" 2 "2")
  let module ← Effect4.Api.printModule "handle" b.program b.table
  pure (TypeScript.Render.module TypeScript.house0 module)

-- Today: the harness is complete and the data wave's parts are missing, by name.
/-- info: ["Ty.record (seat P, data-wave commit 4)", "Term.record and its authoring builder (seat R, commit 6)",
 "Term.field and its authoring builder (seat R, commit 6)", "the codec's record arm, encode (seat S, commit 5)",
 "the codec's record arm, decode (seat S, commit 5)", "the row adapter at a record answer (route A, commit 8)"] -/
#guard_msgs in
#eval parts.missing

-- Commit 8 turns each of these into its acceptance: `acceptance = some expected`, `printedText`
-- equal to the target module's text, `parts.missing = []`.
#guard acceptance == none
#guard printedText == none

/-! ## 7. What compiles and runs today, unchanged by commit 8

The driver, the keyed session and the comparison run today on the pair spelling (the programs
seat's `pairHost`, its records as nested pairs), which keeps them honest: if commit 8 changes
one of them, it is a design change, not a fill-in. -/

def pairUserTy : Ty := .prod .nat (.prod .string roleTy)

/-- The data wave's interface, spelled with today's pairs: `recordTy` nests products, `record`
builds nested `pair`s, `field` projects by position. A stand-in to run the harness today, not a
design: it is exactly what the record forms replace. -/
def pairsWave : DataWave where
  recordTy fs := fs.foldr (fun p acc => if acc = .unit then p.2 else .prod p.2 acc) .unit
  record fs := fs.foldr (fun p acc => match acc with
    | none => some p.2
    | some rest => some (app "pair" [p.2, rest])) none |>.getD unit
  field t name :=
    match name with
    | "id" | "adminToken" | "status" => app "fst" [t]
    | "name" => app "fst" [app "snd" [t]]
    | "role" => app "snd" [app "snd" [t]]
    | "pageSize" | "body" => app "snd" [t]
    | _ => t
  encode t v := Effect4.Schema.encode t v
  decode t j := Effect4.Schema.decode t j
  adapt _ _ := none

/-- Today's host for the pair spelling: the answers the programs seat's `pairHost` gave. -/
def pairHost (b : Effect4.Api.Built) (op : NativeOp) (request : Val) : Option HostAnswer :=
  match op with
  | .external i =>
    if some i = b.positionOf "AppConfig.get" then
      some (.ofExit (.success (.list [.str "secret", .nat 20])))
    else if some i = b.positionOf "UserRepo.findById" then
      match request with
      | .nat 1 => some (.ofExit (.success (.some (.list [.nat 1, .list [.str "ada", .str "admin"]]))))
      | .nat 2 => some (.ofExit (.success (.some (.list [.nat 2, .list [.str "bob", .str "member"]]))))
      | .nat _ => some (.ofExit (.success .none))
      | _ => none
    else none
  | _ => none

-- the handler of section 2, over today's pairs, through the same driver: rc.112's three answers
#guard (runLive (caseModule pairsWave "secret" 2 "2") pairHost) == some (some (.success (.list [.nat 200, .str "bob"])), [])
#guard (runLive (caseModule pairsWave "secret" 9 "9") pairHost) == some (some (.success (.list [.nat 404, .str "no user 9"])), [])
#guard (runLive (caseModule pairsWave "wrong" 2 "2") pairHost) == some (some (.success (.list [.nat 401, .str "bad token"])), [])
-- the comparison step, on today's codec: `[200, "bob"]` is a JSON array, not rc.112's object
#guard (Effect4.Schema.encode (.prod .nat .string) (.list [.nat 200, .str "bob"])).isSome
#guard (Effect4.Schema.encode (.prod .nat .string) (.list [.nat 200, .str "bob"])).map normJ !=
  some (normJ (.obj [("status", num 200), ("body", .str "bob")]))
-- the checked type over pairs, and the printed module reads back today
#guard (built? (caseModule pairsWave "secret" 2 "2")).map (fun b => (b.admitted.ty.answer, b.admitted.ty.error)) ==
  some (.prod .nat .string, .prod .string .string)
#guard ((built? (caseModule pairsWave "secret" 2 "2")).bind fun b =>
  (Effect4.Api.printModule "handle" b.program b.table).map fun module =>
    match Effect4.Api.readModule module b.table with
    | .ok p => decide (p = b.program)
    | .error _ => false) == some true
-- N_J ignores key order and nothing else
#guard normJ (.obj [("b", .str "x"), ("a", num 1)]) == normJ (.obj [("a", num 1), ("b", .str "x")])
#guard normJ (.obj [("a", num 1)]) != normJ (.obj [("a", num 2)])

end Probe.P2Records
