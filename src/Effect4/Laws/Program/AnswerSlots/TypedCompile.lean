import Effect4.Laws.Program.AnswerSlots.Typed

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: stable source compilation supplies the protected typed native graph.
Reach: ordinary points of the direct lexical fragment, with initialized leading bindings.
Limit: captured release entry and acquisition-body connection typing remain separate producers.
Consumer: the stable native head and callback family of both crews.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- The crew's selected paths instantiate the shared acquisition-site certificate. -/
theorem sites (spec : Spec) : AcquisitionSites spec.root spec.acquisitions := by
  intro path member
  change path ∈ spec.identities.map spec.acquirePath at member
  obtain ⟨identity, selected, same⟩ := List.mem_map.mp member
  subst path
  exact spec.sites identity selected

/-- A zero child never enters an acquisition's release destination. -/
theorem ordinary_zero (spec : Spec) (point : Point) : Ordinary spec.acquisitions (point.child 0) :=
  child_ordinary spec.root spec.acquisitions (sites spec) point 0 (.inl (by decide))

/-- An ordinary source operation records enough provenance for its actual write. -/
theorem operation_at (spec : Spec) (point : Point) (row : NativeOp) (request : Term)
    (value : Val) (operation : SyncOp) (source : SourceScope.At spec.root point)
    (slots : Prefix spec.bindings point.env) (ordinary : PointPermission spec point)
    (found : Node.at_ (.eff spec.root) point.path = some (.eff (.perform row request)))
    (reads : evalTerm point.env request = some value) (answer : row.syncOpOf point.env value = some operation) :
    OpAt spec operation := by
  cases operation <;> dsimp only [OpAt]
  case refMake | refSet | refGetAndSet | refSetAndGet | refUpdate | refGetAndUpdate
      | refUpdateAndGet | refUpdateSome | refGetAndUpdateSome | refUpdateSomeAndGet
      | refModify | refModifySome =>
    exact ⟨point, row, request, value, ⟨source, slots, ordinary⟩, found, reads, answer⟩
  case scopeAdd scope fin =>
    exact (SourceScope.source_no_scopeAdd row point.env value scope fin answer).elim

/-- Registration names carry neither a protected source callback nor a captured value. -/
theorem asyncRoute_at (spec : Spec) (row : NativeOp) (request : Term) (point : Point)
    (found : Node.at_ (.eff spec.root) point.path = some (.eff (.perform row request))) :
    CodeAt spec .root (asyncRoute row request point) := by
  have lexical := SourceScope.asyncRoute_at spec.root row request point found
  have leading := AnswerSlots.asyncRoute_at spec.bindings row request point
  fun_cases asyncRoute row request point
  all_goals aesop (add norm simp [CodeAt, NameAt, OrdinaryName, ProtectedName, StoreNameAt,
    SourceScope.CodeAt, SourceScope.NameAt, SourceScope.StoreNameAt, SourceScope.AsyncCancelAt,
    AnswerSlots.CodeAt, AnswerSlots.NameAt, AnswerSlots.StoreNameAt, badShape])

/-- A provider's child-zero region retains the protected source certificate. -/
theorem provideContext_region (spec : Spec) (point : Point) (context : Term) (body : NativeEff)
    (found : Node.at_ (.eff spec.root) point.path = some (.eff (.provideContext context body)))
    (source : SourceScope.At spec.root point) (slots : Prefix spec.bindings point.env) :
    RegionAt spec (.program (point.child 0)) :=
  ⟨SourceScope.provideContext_region spec.root point context body found source,
    slots, .inl (ordinary_zero spec point)⟩

/-- A completed native exit needs no constrained success answer at the broad class. -/
theorem exit_at (spec : Spec) (exit : ExitV) : CodeAt spec .root (Prim.ofExit exit) := by
  cases exit <;> trivial

/-- Ordinary source compilation constructs the protected native graph at the broad answer class. -/
theorem compile_at (spec : Spec) (fragment : SourceScope.Fragment spec.root) (effect : NativeEff)
    (point : Point) (found : Node.at_ (.eff spec.root) point.path = some (.eff effect))
    (source : SourceScope.At spec.root point) (slots : Prefix spec.bindings point.env)
    (ordinary : PointPermission spec point) : CodeAt spec .root (compileEff effect point) := by
  revert found source slots ordinary
  fun_induction compileEff effect point
  case case13 p n hf row request kind value hval operation hop nex ncall nparam =>
    intro found source slots ordinary
    simp only [kind, hval, hop]
    exact ⟨rfl, SourceScope.opAt_origin spec.root operation ⟨p, row, request, value, found, source, hval, hop⟩,
      AnswerSlots.operation_at spec.bindings p.env row value operation slots hop,
      operation_at spec p row request value operation source slots ordinary found hval hop⟩
  case case18 p n hf first rest ih =>
    intro found source slots ordinary
    refine ⟨.root, ih (Agreement.at_child found 0) ?_ slots (.inl (ordinary_zero spec p)), ?_⟩
    · exact SourceScope.child_at spec.root p 0 (SourceScope.next_of_at spec.root p _ 0 0 found source rfl)
    · exact ⟨⟨SourceScope.next_of_at spec.root p _ 1 1 found source rfl, first, rest, found⟩, slots, ⟨source, slots, ordinary⟩⟩
  case case20 p n hf body handler ih =>
    intro found source slots ordinary
    refine ⟨rfl, ih (Agreement.at_child found 0) ?_ slots (.inl (ordinary_zero spec p)), ?_⟩
    · exact SourceScope.child_at spec.root p 0 (SourceScope.next_of_at spec.root p _ 0 0 found source rfl)
    · exact ⟨⟨SourceScope.next_of_at spec.root p _ 1 1 found source rfl, body, handler, found⟩, slots, ⟨source, slots, ordinary⟩⟩
  case case21 p n hf test body handler ih =>
    intro found source slots ordinary
    refine ⟨rfl, ih (Agreement.at_child found 0) ?_ slots (.inl (ordinary_zero spec p)), ?_⟩
    · exact SourceScope.child_at spec.root p 0 (SourceScope.next_of_at spec.root p _ 0 0 found source rfl)
    · exact ⟨⟨SourceScope.next_of_at spec.root p _ 1 1 found source rfl, test, body, handler, found⟩, slots, ⟨source, slots, ordinary⟩⟩
  case case22 p n hf body success failure ih =>
    intro found source slots ordinary
    refine ⟨rfl, ih (Agreement.at_child found 0) ?_ slots (.inl (ordinary_zero spec p)), ?_, ?_⟩
    · exact SourceScope.child_at spec.root p 0 (SourceScope.next_of_at spec.root p _ 0 0 found source rfl)
    · exact ⟨⟨SourceScope.next_of_at spec.root p _ 1 1 found source rfl, body, success, failure, found⟩, slots, ⟨source, slots, ordinary⟩⟩
    · exact ⟨SourceScope.next_of_at spec.root p _ 2 1 found source rfl, slots, ⟨source, slots, ordinary⟩⟩
  case case23 p n hf body finalizer ih =>
    intro found source slots ordinary
    refine ⟨rfl, ih (Agreement.at_child found 0) ?_ slots (.inl (ordinary_zero spec p)), ?_⟩
    · exact SourceScope.child_at spec.root p 0 (SourceScope.next_of_at spec.root p _ 0 0 found source rfl)
    · exact ⟨⟨SourceScope.next_of_at spec.root p _ 1 1 found source rfl, body, finalizer, found⟩, slots, ⟨source, slots, ordinary⟩⟩
  case case25 p n hf body noexit ih =>
    intro found source slots ordinary
    exact ⟨rfl, ih (Agreement.at_child found 0)
      (SourceScope.child_at spec.root p 0 (SourceScope.next_of_at spec.root p _ 0 0 found source rfl))
      slots (.inl (ordinary_zero spec p))⟩
  case case37 p n hf acquire release =>
    intro found source slots ordinary
    refine ⟨.root, ?_, ?_⟩
    · exact ⟨rfl, trivial, trivial, trivial⟩
    · exact ⟨⟨SourceScope.next_of_at spec.root p _ 0 0 found source rfl,
        SourceScope.next_of_at spec.root p _ 1 2 found source rfl, acquire, release, found⟩, slots,
        ⟨⟨source, slots, ordinary⟩, spec.complete p.path ⟨acquire, release, found⟩⟩⟩
  case case40 p n hf key value body val read =>
    intro found source slots ordinary
    refine ⟨.root, ⟨rfl, trivial, trivial, trivial⟩, ?_⟩
    exact ⟨SourceScope.child_at spec.root p 0
      (SourceScope.next_of_at spec.root p _ 0 0 found source rfl), slots,
      ⟨SourceScope.child_at spec.root p 0
        (SourceScope.next_of_at spec.root p _ 0 0 found source rfl), slots,
        .inl (ordinary_zero spec p)⟩⟩
  case case42 =>
    intro found source slots ordinary
    exact exit_at spec _
  case case46 p n hf saved body mask ih =>
    intro found source slots ordinary
    exact ih (Agreement.at_child found 0)
      (SourceScope.child_at spec.root p 0 (SourceScope.next_of_at spec.root p _ 0 0 found source rfl))
      slots (.inl (ordinary_zero spec p))
  all_goals intro found source slots ordinary
  all_goals have head := fragment.at found
  all_goals have lexical := SourceScope.compile_at spec.root fragment _ _ found source
  all_goals have leading := AnswerSlots.compile_at spec.root fragment spec.bindings _ _ found slots
  all_goals aesop (add safe forward [provideContext_region, SourceScope.provideContext_region]) (add safe apply [ordinary_zero]) (add norm simp [exit_at, asyncRoute_at, provideContext_region, CodeAt, ValueAt, ThunkAt, NameAt, OrdinaryName,
    ProtectedName, StoreNameAt, StoreThunkAt, StoreActionAt, ProgAt, FinAt, SourceScope.CodeAt,
    SourceScope.ThunkAt, SourceScope.NameAt, SourceScope.StoreThunkAt, SourceScope.OpAt,
    AnswerSlots.CodeAt, AnswerSlots.ThunkAt, AnswerSlots.NameAt, AnswerSlots.StoreThunkAt,
    SourceScope.directHead, Prim.ofExit, OpAt, SourcePoint, PointPermission, RegionAt]) (add norm unfold [frontier, badShape, updateContextAt])

/-- Resolving an ordinary stable point supplies its protected broad native class. -/
theorem resolve_at (spec : Spec) (fragment : SourceScope.Fragment spec.root) (point : Point)
    (source : SourceScope.At spec.root point) (slots : Prefix spec.bindings point.env)
    (ordinary : PointPermission spec point) : CodeAt spec .root (resolve spec.root point) := by
  unfold resolve
  split
  · rename_i effect found
    exact compile_at spec fragment effect point found source slots ordinary
  · trivial
/-- The combined source-point certificate resolves directly into the stable typed graph. -/
theorem resolve_source (spec : Spec) (fragment : SourceScope.Fragment spec.root) (point : Point)
    (source : SourcePoint spec point) : CodeAt spec .root (resolve spec.root point) :=
  resolve_at spec fragment point source.1 source.2.1 source.2.2
end Effect4.Program.AnswerSlots.Typed
