import Effect4.Program.Handler
import Effect4.Api.Session
import Effect4.Laws.Program.ApplicationService
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Codegen.Services
import Effect4.Laws.Auto.Semantics
import ProofGraph.GoalTag

/-!
# Handler interfaces and their consumers

The placement of each claim follows the handler brief and its proposed decisions row 445.
The design is `docs/research/2026-10-21-handlers/README.md`.
Interface equality compares protocol columns. It states nothing about clause meaning or host progress.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4.Api Effect4.Program.Authoring

/-- Concept 7, initial-algebras-folds. Claim handler-fold-root, role fundamental property, R14.
Reach: every operation alphabet and root definition block, including all children.
Consumer: the handlers relation. This states the fold equation, not clause meaning or host behaviour. -/
@[simp, semantics "initial-algebras-folds" (requirement := R14)]
theorem handlersOf_defs {Op : Type} (ds : List DefDecl) (bodies : Effs Op)
    (main : Eff Op) (layers : LayerTerms Op) :
    handlersOf (.defs ds bodies main layers) =
      (servicesOf ds).filterMap (Handler.ofService ds) ++
        (cata_effs handlerAlgebra bodies ++ handlersOf main ++ cata_layers handlerAlgebra layers) := by
  simp only [handlersOf, cata_eff, handlerAlgebra, EffAlgebra.ofLayer,
    List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil, List.append_assoc]

/-- Helper of handler-fit-protocol: the interface's clause determines its protocol port.
Consumer: ports_of_interface. No clause execution is observed. -/
private def clausePort (c : Clause) : Ty × Program.Row :=
  (.prod (.lit c.1) (requestTy c.2.1),
    (Authoring.Row.host (ServiceSession.replyPrefix ++ c.1)
      (.exitOf c.2.2.1 c.2.2.2) .unit).row)

/-- Helper of handler-fit-protocol: successful interface reading determines all method ports.
Consumer: rows_of_interface. The declaration positions may differ between handlers. -/
private theorem ports_of_interface (decls : List DefDecl) (h : Handler) (cs : List Clause)
    (read : h.interface decls = some cs) :
    h.clauses.mapM (ServiceSession.methodPort decls ⟨h.service, h.init, h.clauses⟩ h.state) =
      .ok (cs.map clausePort) := by
  rcases h with ⟨service, state, init, methods, requires, forwards⟩
  induction methods generalizing cs with
  | nil =>
    change some [] = some cs at read
    cases read
    rfl
  | cons m ms ih =>
    rcases m with ⟨name, position, arity⟩
    simp only [Handler.interface, List.mapM_cons] at read
    obtain ⟨c, hc, rest⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨tail, ht, last⟩ := Option.bind_eq_some_iff.mp rest
    cases last
    obtain ⟨d, hd, hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨args, ha, hc⟩ := Option.bind_eq_some_iff.mp hc
    cases hc
    have tailPorts := ih tail ht
    have port : ServiceSession.methodPort decls
        ⟨service, init, (name, position, arity) :: ms⟩ state (name, position, arity) =
        .ok (clausePort (name, args, d.answer, d.error)) := by
      unfold ServiceSession.methodPort Handler.interface
      simp only [List.mapM_cons, List.mapM_nil, hd, Option.bind_eq_bind,
        Option.pure_def, Option.bind_some, ha]
      rfl
    rw [List.mapM_cons, port]
    change (do
      let ps ← ms.mapM (ServiceSession.methodPort decls ⟨service, init, ms⟩ state)
      pure (clausePort (name, args, d.answer, d.error) :: ps)) = _
    rw [tailPorts]
    rfl

/-- Concept 9, host-session-protocol. Claim handler-fit-protocol, role compatibility, R6.
Reach: two handlers of one service with the same successfully read interface.
Consumer: service-session clients. Failed reads do not constitute fit.
This compares protocol rows, not answers, termination or host behaviour. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem Handler.rows_of_interface (decls decls' : List DefDecl) (h h' : Handler)
    (_sameService : h.service = h'.service) (cs : List Clause)
    (left : h.interface decls = some cs) (right : h'.interface decls' = some cs) :
    ServiceSession.rows decls ⟨h.service, h.init, h.clauses⟩ h.state =
      ServiceSession.rows decls' ⟨h'.service, h'.init, h'.clauses⟩ h'.state := by
  unfold ServiceSession.rows
  rw [ports_of_interface decls h cs left, ports_of_interface decls' h' cs right]

/-- Concept 8, context-requirements. Claim layer-provide-assoc-conditional, role compatibility, R4.
Reach: each key read by the outer layer and supplied by the inner layer remains visible
through the middle layer or remains required by the inner layer. The owner approves this
condition after the brief's condition fails on one key. Consumer: handler layer composition.
This compares layer types. It states no build, sharing or host execution law. -/
@[semantics "context-requirements" (requirement := R4)]
theorem provide_assoc_conditional (a b c : LayerTy)
    (visible : ∀ k, k ∈ a.requires → k ∈ c.out → k ∈ b.out ∨ k ∈ c.requires) :
    LayerTy.provide (LayerTy.provide a b) c = LayerTy.provide a (LayerTy.provide b c) := by
  have requirements :
      Effect4.Row.union
          (Effect4.Row.diff (Effect4.Row.union (Effect4.Row.diff a.requires b.out) b.requires) c.out)
          c.requires =
        Effect4.Row.union (Effect4.Row.diff a.requires b.out)
          (Effect4.Row.union (Effect4.Row.diff b.requires c.out) c.requires) := by
    apply Effect4.Row.eq_of_mem_iff
    intro k
    simp only [Effect4.Row.mem_union, Effect4.Row.mem_diff]
    constructor
    · rintro (⟨ha | hb, hc⟩ | hc)
      · exact .inl ha
      · exact .inr (.inl ⟨hb, hc⟩)
      · exact .inr (.inr hc)
    · rintro (⟨ha, hb⟩ | (⟨hb, hc⟩ | hc))
      · by_cases hc : k ∈ c.out
        · rcases visible k ha hc with hb' | hc'
          · exact (hb hb').elim
          · exact .inr hc'
        · exact .inl ⟨.inl ⟨ha, hb⟩, hc⟩
      · exact .inl ⟨.inr hb, hc⟩
      · exact .inr hc
  unfold LayerTy.provide
  rw [Ty.join_assoc, requirements]

/-! The following helpers serve handler-fit-imposed. They compare declarations only.
Their consumer is Handler.interface_imposed, under concept 9 and requirement R6. -/

/-- Removing the state from a declared request returns exactly its remaining parameters. -/
private theorem methodArgTys_request (ts : List Ty) :
    methodArgTys ts.length (requestTy ts) = some ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases ts with
    | nil => rfl
    | cons u us =>
      change (methodArgTys (u :: us).length (requestTy (u :: us))).map (t :: ·) =
        some (t :: u :: us)
      rw [ih]
      rfl

/-- The state is the first parameter, including a method with no other parameter. -/
private theorem methodArgs_request (state : Ty) (ts : List Ty) (d : DefDecl)
    (request : d.request = requestTy (state :: ts)) :
    methodArgs state d ts.length = some ts := by
  cases ts with
  | nil => simp only [List.length_nil, methodArgs, request, requestTy, ↓reduceIte]
  | cons t ts =>
    simp only [List.length_cons, methodArgs, request, requestTy, ↓reduceIte]
    exact methodArgTys_request (t :: ts)

/-- A service's method positions depend only on the declarations' roles. -/
private theorem serviceMethods_roles (ds ds' : List DefDecl) (service : String)
    (roles : ds.map (·.role) = ds'.map (·.role)) :
    serviceMethods service ds = serviceMethods service ds' := by
  have lengths : ds.length = ds'.length := by
    simpa only [List.length_map] using congrArg List.length roles
  unfold serviceMethods
  rw [lengths]
  apply congrArg (fun f => (List.range ds'.length).filterMap f)
  funext i
  have atIndex := congrArg (fun xs => xs[i]?) roles
  simp only [List.getElem?_map] at atIndex
  unfold methodAt
  cases hd : ds[i]? <;> cases hd' : ds'[i]? <;>
    simp only [hd, hd', Option.map_none, Option.map_some, Option.some.injEq] at atIndex
  · rfl
  · cases atIndex
  · cases atIndex
  · dsimp only
    rw [atIndex]

/-- Mapping a successful traversal keeps the entry paired with its checked type. -/
private theorem methods_as_typed (app : Application NativeOp) (service : String)
    (entries : List (Application.Entry NativeOp)) :
    (entries.mapM fun e => do
      let t ← app.entryTy e
      pure (app.methodDef service e t)) =
      (entries.mapM fun e => do
        let t ← app.entryTy e
        pure (e, t)).map (fun (typed : List (Application.Entry NativeOp × EffTy)) =>
          typed.map fun (e, t) => app.methodDef service e t) := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    simp only [List.mapM_cons]
    rw [ih]
    cases he : app.entryTy e with
    | error why => rfl
    | ok t =>
      cases ht : es.mapM (fun e => do let t ← app.entryTy e; pure (e, t)) <;> rfl

/-- Pointwise agreement on the methods is agreement of their whole interface. -/
private theorem mapM_eq_on {α β : Type} (f g : α → Option β) (xs : List α)
    (same : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, same x List.mem_cons_self,
      ih (fun y hy => same y (List.mem_cons_of_mem x hy))]

/-- The same checked entries have the same interface at either application's state. -/
private theorem interface_typed (app app' : Application NativeOp) (service : String)
    (typed : List (Application.Entry NativeOp × EffTy)) :
    let ds := ((app.contextDef service) ::
      typed.map fun (e, t) => app.methodDef service e t).map DefSrc.decl
    let ds' := ((app'.contextDef service) ::
      typed.map fun (e, t) => app'.methodDef service e t).map DefSrc.decl
    ((Handler.ofService ds ⟨service, 0, serviceMethods service ds⟩).bind
      (Handler.interface ds)) =
    ((Handler.ofService ds' ⟨service, 0, serviceMethods service ds'⟩).bind
      (Handler.interface ds')) := by
  dsimp only
  let ds := ((app.contextDef service) ::
    typed.map fun (e, t) => app.methodDef service e t).map DefSrc.decl
  let ds' := ((app'.contextDef service) ::
    typed.map fun (e, t) => app'.methodDef service e t).map DefSrc.decl
  have roles : ds.map (·.role) = ds'.map (·.role) := by
    simp only [ds, ds', List.map_cons, List.map_map]
    rfl
  have methods := serviceMethods_roles ds ds' service roles
  change (⟨service, app.stateTy, 0, serviceMethods service ds, _, _⟩ : Handler).interface ds =
    (⟨service, app'.stateTy, 0, serviceMethods service ds', _, _⟩ : Handler).interface ds'
  unfold Handler.interface
  rw [← methods]
  apply mapM_eq_on
  intro m hm
  rcases m with ⟨name, position, arity⟩
  obtain ⟨d, hd, role⟩ := mem_serviceMethods.mp hm
  cases position with
  | zero =>
    change some (app.contextDef service).decl = some d at hd
    cases hd
    cases role
  | succ i =>
    simp only [ds, List.map_cons, List.getElem?_cons_succ, List.getElem?_map] at hd
    cases ht : typed[i]? with
    | none => simp only [ht, Option.map_none] at hd; cases hd
    | some et =>
      rcases et with ⟨e, t⟩
      simp only [ht, Option.map_some, Option.some.injEq] at hd
      cases hd
      have arityEq : e.params.length = arity := by
        change DefRole.serviceMethod service e.name e.params.length =
          .serviceMethod service name arity at role
        exact (DefRole.serviceMethod.inj role).2.2
      have a := methodArgs_request app.stateTy (e.params.map (·.2))
        (app.methodDef service e t).decl rfl
      have b := methodArgs_request app'.stateTy (e.params.map (·.2))
        (app'.methodDef service e t).decl rfl
      simp only [List.length_map, arityEq] at a b
      simp only [ds, ds', List.map_cons, List.getElem?_cons_succ, List.getElem?_map,
        ht, Option.map_some, Option.bind_eq_bind, Option.bind_some, a, b, Option.pure_def]
      rfl

/-- Concept 9, host-session-protocol. Claim handler-fit-imposed, role compatibility, R6.
Reach: every application, imposed list and service name, when both serviceDefs constructions succeed.
Consumer: rows_of_interface, hence clients of the service's session protocol.
The handlers come from the generated declarations' init and method roles.
This compares interfaces only. Clause answers, host behaviour and progress remain outside the claim. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem Handler.interface_imposed (app : Application NativeOp)
    (ms : List (Application.Imposed NativeOp)) (service : String)
    (defs defs' : List (DefSrc NativeOp))
    (left : app.serviceDefs service = .ok defs)
    (right : (Application.serviceDefs { app with imposed := ms } service) = .ok defs') :
    let ds := defs.map DefSrc.decl
    let ds' := defs'.map DefSrc.decl
    ((Handler.ofService ds ⟨service, 0, serviceMethods service ds⟩).bind
      (Handler.interface ds)) =
    ((Handler.ofService ds' ⟨service, 0, serviceMethods service ds'⟩).bind
      (Handler.interface ds')) := by
  unfold Application.serviceDefs at left right
  rw [methods_as_typed] at left right
  have entryTypes (e : Application.Entry NativeOp) :
      Application.entryTy { app with imposed := ms } e = app.entryTy e := rfl
  simp only [entryTypes] at right
  cases typed : app.entries.mapM (fun e => do let t ← app.entryTy e; pure (e, t)) with
  | error why => rw [typed] at left; cases left
  | ok ts =>
    rw [typed] at left right
    cases left
    cases right
    exact interface_typed app { app with imposed := ms } service ts

/-- Concept 8, context-requirements. Claim layer-provide-tensor-interchange, role compatibility, R4.
Reach: each upper layer requires only keys provided by its own lower layer.
Consumer: composition of handler layer types. This states no build or host execution law.
The side conditions exclude requirements supplied only by the other lower layer. -/
@[semantics "context-requirements" (requirement := R4)]
theorem provide_tensor_interchange (a b c d : LayerTy)
    (left : Effect4.Row.Subset a.requires c.out)
    (right : Effect4.Row.Subset b.requires d.out) :
    LayerTy.provide (LayerTy.merge a b) (LayerTy.merge c d) =
      LayerTy.merge (LayerTy.provide a c) (LayerTy.provide b d) := by
  have combined : Effect4.Row.Subset (Effect4.Row.union a.requires b.requires)
      (Effect4.Row.union c.out d.out) := by
    intro k hk
    rcases (Effect4.Row.mem_union k _ _).mp hk with ha | hb
    · exact (Effect4.Row.mem_union k _ _).mpr (.inl (left k ha))
    · exact (Effect4.Row.mem_union k _ _).mpr (.inr (right k hb))
  have dl := (Effect4.Row.diff_eq_empty_iff_subset _ _).mpr left
  have dr := (Effect4.Row.diff_eq_empty_iff_subset _ _).mpr right
  have dc := (Effect4.Row.diff_eq_empty_iff_subset _ _).mpr combined
  have errors : (a.error.join b.error).join (c.error.join d.error) =
      (a.error.join c.error).join (b.error.join d.error) := by
    rw [Ty.join_assoc a.error, ← Ty.join_assoc b.error,
      Ty.join_comm b.error c.error, Ty.join_assoc c.error, ← Ty.join_assoc a.error]
  unfold LayerTy.provide LayerTy.merge
  rw [dl, dr, dc, Effect4.Row.union_empty_left, Effect4.Row.union_empty_left,
    Effect4.Row.union_empty_left, errors]

/-- Concept 9, host-session-protocol. Claim imposed-wrap-tensor, role compatibility, R6.
Reach: applications share declarations and have disjoint entry names. Wrappers name only left entries.
All three serviceDefs constructions succeed. The combined service concatenates the entry lists.
Consumer: handler interface composition. The owner chooses interface equality after removing state.
This states no equality of clause behaviour, state translation, build or host execution. -/
@[semantics "host-session-protocol" (requirement := R6)]
proof_goal wrap_tensor (a b : Application NativeOp) (ms : List (Application.Imposed NativeOp))
    (service : String) (combined left right : List (DefSrc NativeOp))
    (declarations : a.declarations = b.declarations)
    (disjoint : ∀ e ∈ a.entries, ∀ e' ∈ b.entries, e.name ≠ e'.name)
    (wraps : ∀ m ∈ ms, ∀ around ∈ m.around, around.1 ∈ a.entryNames)
    (hc : Application.serviceDefs { a with entries := a.entries ++ b.entries, imposed := ms }
      service = .ok combined)
    (hl : Application.serviceDefs { a with imposed := ms } service = .ok left)
    (hr : b.serviceDefs service = .ok right) :
    let read := fun (defs : List (DefSrc NativeOp)) =>
      let ds := defs.map DefSrc.decl
      (Handler.ofService ds ⟨service, 0, serviceMethods service ds⟩).bind (Handler.interface ds)
    read combined = do
      let cs ← read left
      let cs' ← read right
      pure (cs ++ cs')

end Effect4.Program
