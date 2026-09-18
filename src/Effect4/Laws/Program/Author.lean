import Effect4.Laws.Program.Authoring.Sugar
import Effect4.Program.Author

/-!
# Laws.Program.Author — what a module's declarations guarantee

The authoring surface gained three things a proof must carry: rows called by their spelling,
services declared with their carrier, and names the surface mints for itself. This module is
what each of them is worth.

* **The table an author declares is lawful.** `build_table_lawful`: distinct spellings, none
  of them a built-in's, and the host shape (a call with no trailing name) are exactly the
  three conditions `Table.lawful` decides. All three are decidable facts of the declarations,
  so one proof serves every program written against them, and an author learns before
  building what admission would otherwise tell them after.
* **A call reaches the row it names.** `build_rows_resolve`: in the scope a module elaborates
  in, a declared row's call performs the external position its own table put the row at, and
  the table has that row there. An external index is a position in the table supplied beside
  the program (DI-22); this is why the two cannot drift apart when the author writes neither.
* **A minted name cannot be captured.** `var_push_minted`: a binder the surface minted leaves
  every name an author wrote reading exactly what it read before, because a minted name is
  reserved, an author's is not, and a binder of a different name changes no level. With
  `var_reserved` — an author who writes a reserved name is refused at the site — that is B-9
  closed for every name the surface mints under `Env.mint`.
* **Two declarations of one key agree.** `ServiceDef.carrier_unique`.
* The scope lemma for `Row.call` and one for each new convenience, in the shape of the 48
  generated lift lemmas, so `authoring_scoped` discharges a program written in the new
  surface exactly as it discharges one written in the old.

Every proof here is a search (`aesop`) or one application of an existing lemma, except where
noted at the proof: two places need a fact stated first, and the residual goal that asked for
it is named there.
-/

set_option autoImplicit false

namespace Effect4.Program.Authoring

open Effect4.Program

/-- A string comparison is its decision, by `rfl`. The library's lemmas about `==` at
`String` reach `Classical.choice` through the lawfulness instance, so a search that
normalises `==` with them leaves the gate's ceiling; normalising with this equation keeps it.
It mentions no type of the project, and it is registered for this module's searches only. -/
theorem beq_decide (a b : String) : (a == b) = decide (a = b) := rfl

attribute [local aesop norm simp] beq_decide

/-! ## The scope lemma for a declared row's call -/

/-- A declared row's call is scoped when its request is: the call is `perform` at the
position the module resolved, and `perform`'s lemma is the one the table generates. -/
theorem Row.call_scoped (r : RowDef) {request : TermSrc} (h1 : request.Scoped) :
    ((Row.call r request) : Src NativeOp).Scoped := by
  refine ⟨fun env p e h => ?_⟩
  unfold Row.call at h
  have s1 := h1.holds env p
  aesop (add norm simp [Eff.scopedAt])

/-! ## Minted names cannot be captured (B-9)

The one class of silently wrong program the named surface was built to remove was still
reachable: a convenience that binds a fixed spelling, handed that spelling as its own
argument, binds the wrong variable, and the result is scoped, types and runs. The reservation
(`Authoring.reservedPrefix`, `Env.mint`, `var`'s refusal) closes it, and these are the facts
that say so. -/

/-- A binder of a different name leaves a level alone, whatever is already in scope. The
accumulator carries the level found so far, so the statement is over every starting pair. -/
theorem Names.resolve_go_append_ne {target binder : String} (hb : binder ≠ target) :
    ∀ (names : Names) (k : Nat) (acc : Option Nat),
      Names.resolve.go target (names ++ [binder]) k acc
        = Names.resolve.go target names k acc := by
  intro names
  induction names with
  | nil => intro k acc; aesop (add norm simp [Names.resolve.go])
  | cons z zs ih => intro k acc; aesop (add norm simp [Names.resolve.go], safe forward ih)

/-- A binder of a different name does not change what a name resolves to. -/
theorem Names.resolve_append_ne {target binder : String} (hb : binder ≠ target) (names : Names) :
    Names.resolve (names ++ [binder]) target = Names.resolve names target := by
  unfold Names.resolve
  exact Names.resolve_go_append_ne hb names 0 none

/-- A binder of a different name leaves a variable reading exactly what it read. -/
theorem var_push_ne {binder x : String} (hb : binder ≠ x) (env : Env) (p : List Nat) :
    var x (env.push [binder]) p = var x env p := by
  have hr := Names.resolve_append_ne hb env.names
  unfold var minted Env.push
  aesop (add norm simp [hr])

/-- A name only the surface may write is refused where an author writes it, at that site. -/
theorem var_reserved {x : String} (h : Name.reserved x = true) (env : Env) (p : List Nat) :
    var x env p = .error ⟨p, .reservedName x⟩ := by
  unfold var
  aesop

/-- No name an author wrote is bound in a minted name's place: a minted name is reserved and
an author's is not, so they are different names, and a binder of a different name changes no
level. This is what makes a convenience that mints its own binder safe to hand any name. -/
theorem var_push_minted {binder x : String} (hb : Name.reserved binder = true)
    (hx : Name.reserved x = false) (env : Env) (p : List Nat) :
    var x (env.push [binder]) p = var x env p := by
  refine var_push_ne ?_ env p
  aesop

/-! ## The table a module assembles -/

/-- No spelling twice: `duplicate?` answers nothing exactly when the spellings are distinct. -/
theorem RowDef.nodup_of_duplicate? : ∀ (rows : List RowDef), RowDef.duplicate? rows = none →
    (rows.map (fun r => r.row.spelling)).Nodup := by
  intro rows
  induction rows with
  | nil => aesop (add norm simp [RowDef.duplicate?])
  | cons r rest ih => aesop (add norm simp [RowDef.duplicate?], safe forward ih)

/-- A declared spelling is found at the position the declaration order gave it. The two facts
stated before the search are the ones its residual goals named: the head's spelling is not the
one being looked for (from `duplicate?`), and the index arithmetic of counting from `base`. -/
theorem RowDef.namesFrom_find? : ∀ (rows : List RowDef) (base i : Nat) (r : RowDef),
    rows[i]? = some r → RowDef.duplicate? rows = none →
    (RowDef.namesFrom base rows).find? (fun entry => entry.1 == r.row.spelling)
      = some (r.row.spelling, base + i) := by
  intro rows
  induction rows with
  | nil => intro base i r hi; aesop
  | cons r0 rest ih =>
    intro base i r hi hd
    cases i with
    | zero => aesop (add norm simp [RowDef.namesFrom, RowDef.duplicate?])
    | succ j =>
      have hj : rest[j]? = some r := by simpa using hi
      have hmem : r ∈ rest := List.mem_of_getElem? hj
      have ihj := ih (base + 1) j r hj
      have hne : ¬ (r0.row.spelling = r.row.spelling) := by
        have hnd := RowDef.nodup_of_duplicate? (r0 :: rest) hd
        aesop
      have harith : base + 1 + j = base + (j + 1) := by omega
      aesop (add norm simp [RowDef.namesFrom, RowDef.duplicate?, harith], safe forward ihj)

/-- Rows that declare no trailing name have distinct table keys exactly when their spellings
are distinct: a key is the spelling and the trailing names. -/
theorem RowDef.nodup_keys : ∀ (rows : List RowDef), (∀ r ∈ rows, r.row.trailing = []) →
    RowDef.duplicate? rows = none → ((RowDef.table rows).map rowKey).Nodup := by
  intro rows
  induction rows with
  | nil => aesop (add norm simp [RowDef.table])
  | cons r0 rest ih =>
    aesop (add norm simp [RowDef.table, RowDef.duplicate?, rowKey], safe forward ih)

/-- **O-11.** A table assembled from row declarations is lawful when they are host rows (a
call with no trailing name, which is what `Row.host` writes), their spellings are distinct,
and none is a spelling a built-in already has. Those are the three conditions `Table.lawful`
decides, so this is one proof for every program written against such declarations. -/
theorem build_table_lawful (rows : List RowDef)
    (hcall : ∀ r ∈ rows, r.row.shape = .call)
    (hplain : ∀ r ∈ rows, r.row.trailing = [])
    (hfresh : ∀ r ∈ rows,
      (NativeOp.all.map (fun op => (nativeRowOf [] op).key)).contains (rowKey r.row) = false)
    (hnodup : RowDef.duplicate? rows = none) :
    Table.lawful (RowDef.table rows) = true := by
  have hkeys := RowDef.nodup_keys rows hplain hnodup
  aesop (add norm simp [Table.lawful, RowDef.table, Row.key, rowKey])

/-- A host row is a call with no trailing name, so `Row.host` declarations meet two of the
three conditions by construction. -/
theorem Row.host_shape (spelling : String) (request answer error : Ty) (cite : String) :
    (Row.host spelling request answer error cite).row.shape = .call
      ∧ (Row.host spelling request answer error cite).row.trailing = [] := by
  aesop

/-- **O-12.** Every row a module declares resolves, in the scope the module elaborates in, to
the position its own table put it at: the call performs the external row at that index, and
the table has the declared row there. -/
theorem build_rows_resolve {Op : Type} (m : Module Op) (names : RowNames)
    (hnames : rowNamesOf m.rowDefs = .ok names)
    (i : Nat) (r : RowDef) (hr : m.rowDefs[i]? = some r)
    {env : Env} (henv : env.rows = names) {request : TermSrc} {p : List Nat} {t : Term}
    (ht : request env p = .ok t) :
    Row.call r request env p = .ok (.perform (.external i) t) ∧ m.table[i]? = some r.row := by
  have hsplit : RowDef.duplicate? m.rowDefs = none ∧ names = RowDef.names m.rowDefs := by
    unfold rowNamesOf at hnames
    aesop
  obtain ⟨hd, hnm⟩ := hsplit
  have h0 := RowDef.namesFrom_find? m.rowDefs 0 i r hr hd
  have hfind : env.rows.find? (fun entry => entry.1 == r.row.spelling)
      = some (r.row.spelling, i) := by
    aesop (add norm simp [henv, hnm, RowDef.names, h0])
  aesop (add norm simp [Row.call, Module.table, RowDef.table, List.getElem?_map, hfind])

/-! ## What a build carries -/

/-- A built program's table is the module's own, and its row names are the module's. -/
theorem build_table {m : Module NativeOp} {b : Api.Built} (h : Api.Author.build m = .ok b) :
    b.table = m.table ∧ b.rowNames = m.rowNames := by
  unfold Api.Author.build at h
  aesop

/-- A built program's table is lawful: the certificate says so, and `build_table_lawful` is
what lets an author know it before the build. -/
theorem build_lawful {b : Api.Built} : Table.lawful b.table = true := b.admitted.lawful

/-- A built program's table can be registered by this runner: every row is an external
asynchronous row, which is what `Row.host` writes. -/
theorem build_runnable {b : Api.Built} : checkTable b.table = none := b.admitted.runnable

/-! ## Services -/

/-- **`carrier_unique`.** Two declarations of one key cannot disagree about its carrier: each
agrees with the signature, and the signature answers once. -/
theorem ServiceDef.carrier_unique {Op : Type} {sig : Signature Op} {a b : ServiceDef}
    (hk : a.key = b.key) (ha : ServiceDef.Agrees sig a = true)
    (hb : ServiceDef.Agrees sig b = true) : a.carrier = b.carrier := by
  unfold ServiceDef.Agrees at ha hb
  aesop

/-- A declaration that agrees is the carrier the signature types its key at. -/
theorem ServiceDef.agrees_serviceTy {Op : Type} {sig : Signature Op} {s : ServiceDef}
    (h : ServiceDef.Agrees sig s = true) : sig.serviceTy s.key = some s.carrier := by
  unfold ServiceDef.Agrees at h
  aesop

/-! ## The new conveniences preserve scope

One lemma per definition, named so `authoring_scoped` finds it, each one application of the
lemma of the lift it is made of. -/

theorem ServiceDef.use_scoped {Op : Type} (s : ServiceDef) : ((s.use : Src Op)).Scoped :=
  service_scoped s.key

theorem ServiceDef.give_scoped {Op : Type} (s : ServiceDef) {value : TermSrc} {body : Src Op}
    (h1 : value.Scoped) (h2 : body.Scoped) : ((s.give value body : Src Op)).Scoped :=
  provideService_scoped s.key h1 h2

theorem ServiceDef.layer_scoped {Op : Type} (s : ServiceDef) {build : Src Op}
    (h : build.Scoped) : ((s.layer build : LayerSrc Op)).Scoped :=
  Layer.effect_scoped s.key h

theorem Layer.value_scoped {Op : Type} (key : Effect4.ServiceKey) {value : TermSrc}
    (h : value.Scoped) : ((Layer.value key value : LayerSrc Op)).Scoped :=
  Layer.effect_scoped key (Authoring.succeed_scoped h)

theorem ServiceDef.constant_scoped {Op : Type} (s : ServiceDef) {value : TermSrc}
    (h : value.Scoped) : ((s.constant value : LayerSrc Op)).Scoped :=
  Layer.value_scoped s.key h

theorem Layer.empty_scoped {Op : Type} : ((Layer.empty : LayerSrc Op)).Scoped :=
  Layer.effectDiscard_scoped (Authoring.succeed_scoped Authoring.unit_scoped)

theorem Layer.all_scoped {Op : Type} {layers : List (LayerSrc Op)}
    (h : ∀ l ∈ layers, l.Scoped) : ((Layer.all layers : LayerSrc Op)).Scoped :=
  Layer.mergeAll_scoped h

theorem with__scoped {Op : Type} {layer : LayerSrc Op} {body : Src Op}
    (h0 : layer.Scoped) (h1 : body.Scoped) : ((with_ layer body : Src Op)).Scoped :=
  provideLayer_scoped false h0 h1

theorem provideAll_scoped {Op : Type} {layers : List (LayerSrc Op)} {body : Src Op}
    (h0 : ∀ l ∈ layers, l.Scoped) (h1 : body.Scoped) :
    ((provideAll layers body : Src Op)).Scoped :=
  provideLayer_scoped false (Layer.all_scoped h0) h1

theorem provideFresh_scoped {Op : Type} {layer : LayerSrc Op} {body : Src Op}
    (h0 : layer.Scoped) (h1 : body.Scoped) : ((provideFresh layer body : Src Op)).Scoped :=
  provideLayer_scoped true h0 h1

theorem fork_scoped {Op : Type} {body : Src Op} (options : Effect4.Supervision.ForkOptions)
    (h : body.Scoped) : ((fork body options : Src Op)).Scoped :=
  withFiber_scoped (Action.fork_scoped options h)

theorem daemonFork_scoped {Op : Type} {body : Src Op} (h : body.Scoped) :
    ((daemonFork body : Src Op)).Scoped :=
  withFiber_scoped (Action.fork_scoped daemonOptions h)

theorem daemonForkIn_scoped {Op : Type} {body : Src Op} {scope : TermSrc}
    (h : body.Scoped) (hs : scope.Scoped) : ((daemonForkIn body scope : Src Op)).Scoped :=
  withFiber_scoped (Action.forkIn_scoped daemonOptions h hs)

theorem await_scoped {Op : Type} {fiber : TermSrc} (h : fiber.Scoped) :
    ((await fiber : Src Op)).Scoped :=
  awaitFiber_scoped .awaitValue h

theorem join_scoped {Op : Type} {fiber : TermSrc} (h : fiber.Scoped) :
    ((join fiber : Src Op)).Scoped :=
  awaitFiber_scoped .joinEffect h

/-! ## The conveniences are what they unfold to

Each is a Lean function over a generated lift, so its equation is `rfl` and there is one
owner of what the program means and prints. -/

theorem fork_eq {Op : Type} (body : Src Op) (options : Effect4.Supervision.ForkOptions) :
    fork body options = withFiber (Action.fork body options) := rfl

theorem daemonFork_eq {Op : Type} (body : Src Op) :
    daemonFork body = withFiber (Action.fork body daemonOptions) := rfl

theorem daemonForkIn_eq {Op : Type} (body : Src Op) (scope : TermSrc) :
    daemonForkIn body scope = withFiber (Action.forkIn body daemonOptions scope) := rfl

theorem await_eq {Op : Type} (fiber : TermSrc) :
    (await fiber : Src Op) = awaitFiber fiber .awaitValue := rfl

theorem join_eq {Op : Type} (fiber : TermSrc) :
    (join fiber : Src Op) = awaitFiber fiber .joinEffect := rfl

theorem with__eq {Op : Type} (layer : LayerSrc Op) (body : Src Op) :
    with_ layer body = provideLayer layer false body := rfl

theorem provideAll_eq {Op : Type} (layers : List (LayerSrc Op)) (body : Src Op) :
    provideAll layers body = provideLayer (Layer.mergeAll layers) false body := rfl

theorem provideFresh_eq {Op : Type} (layer : LayerSrc Op) (body : Src Op) :
    provideFresh layer body = provideLayer layer true body := rfl

theorem Layer.value_eq {Op : Type} (key : Effect4.ServiceKey) (value : TermSrc) :
    (Layer.value key value : LayerSrc Op) = Layer.effect key (Authoring.succeed value) := rfl

theorem Layer.empty_eq {Op : Type} :
    (Layer.empty : LayerSrc Op) = Layer.effectDiscard (Authoring.succeed Authoring.unit) := rfl

theorem Layer.all_eq {Op : Type} (layers : List (LayerSrc Op)) :
    (Layer.all layers : LayerSrc Op) = Layer.mergeAll layers := rfl

theorem ServiceDef.use_eq {Op : Type} (s : ServiceDef) :
    (s.use : Src Op) = Authoring.service s.key := rfl

theorem ServiceDef.give_eq {Op : Type} (s : ServiceDef) (value : TermSrc) (body : Src Op) :
    s.give value body = Authoring.provideService s.key value body := rfl

theorem ServiceDef.layer_eq {Op : Type} (s : ServiceDef) (build : Src Op) :
    s.layer build = Layer.effect s.key build := rfl

end Effect4.Program.Authoring
