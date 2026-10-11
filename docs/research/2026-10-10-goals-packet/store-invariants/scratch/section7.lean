
/-! ## 7. The census of the shop's write sites, and `shop_sites_used` decomposed

`shop_sites_used` (section 4) is decomposed here into a census, decided by the kernel on the
elaborated program, and one lemma per family of sites. The decision's family is proved
(section 6); the allocations and the reads are proved here; the deposit, the refill and the
note are planned goals of the same shape as `decision_used`. -/

/-- The `perform` sites of a program: each address of a `perform` node, its row, its request and
its level. -/
def performSites (root : NativeEff) : List (List Nat × NativeOp × Term × Option Nat) :=
  (Node.addresses (.eff root)).filterMap fun path =>
    match Node.at_ (.eff root) path with
    | some (.eff (.perform op request)) => some (path, op, request, levelAt (.eff root) 0 path)
    | _ => none

/-- **The site list is complete**: every `perform` node of a program is listed, with its level. -/
theorem performSites_complete {root : NativeEff} {path : List Nat} {op : NativeOp}
    {request : Term} (h : Node.at_ (.eff root) path = some (.eff (.perform op request))) :
    (path, op, request, levelAt (.eff root) 0 path) ∈ performSites root := by
  refine List.mem_filterMap.mpr ⟨path, (mem_addresses_iff (.eff root) path).mpr ?_, ?_⟩
  · rw [h]
    rfl
  · rw [h]

/-- A build keeps the elaborated program and the module's table. -/
theorem build_elaborates {m : Authoring.Module NativeOp} {b : Api.Built}
    (h : Effect4.Api.Author.build m = .ok b) :
    Authoring.elaborateModule m = .ok b.program ∧ b.table = m.table := by
  unfold Effect4.Api.Author.build at h
  split at h
  · cases h
  · rename_i program hprog
    split at h
    · cases h
    · unfold Effect4.Api.Author.Internal.finishBuild at h
      split at h
      · cases h
        exact ⟨hprog, rfl⟩
      · split at h <;> cases h
      · cases h

/-- The shop's elaborated program. -/
def shopProgram : Option NativeEff := (Authoring.elaborateModule (shop .none)).toOption

/-- p5's deposit of `id` at level `d`, as the elaborator wrote it for the shop. -/
def depositAt (id d : Nat) : Term :=
  tpair (.app "add" (.cons (tfield d "balance") (.cons (.lit (.nat id)) .nil)))
    (.recordSet (.recordSet (.var d) "balance"
        (.app "add" (.cons (tfield d "balance") (.cons (.lit (.nat id)) .nil))))
      "history" (.app "append" (.cons (tfield d "history") (.cons (.app "cons"
        (.cons (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)] ["_tag", "amount"]
            (.cons (.lit (.str "Deposit")) (.cons (.lit (.nat id)) .nil)))
          (.cons (.app "nil" .nil) .nil))) .nil))))

/-- p4's refill at level `d`: the window with `used = 0`. -/
def refillAt (d : Nat) : Term := .recordSet (.var d) "used" (.lit (.nat 0))

/-- The finalizer's note of `id` at level `d`: the log with `[id, admitted + rejected]` appended,
the window read one level below. -/
def noteAt (id d : Nat) : Term :=
  .app "append" (.cons (.var d) (.cons (.app "cons" (.cons
    (tpair (.lit (.nat id)) (.app "add" (.cons (tfield (d - 1) "admitted")
      (.cons (tfield (d - 1) "rejected") .nil))))
    (.cons (.app "nil" .nil) .nil))) .nil))

/-- The window's allocation request. -/
def window0T : Term :=
  .record [("used", false, .nat), ("admitted", false, .nat), ("rejected", false, .nat)]
    ["used", "admitted", "rejected"]
    (.cons (.lit (.nat 0)) (.cons (.lit (.nat 0)) (.cons (.lit (.nat 0)) .nil)))

/-- The account's allocation request. -/
def account0T : Term :=
  .record [("id", false, .string), ("balance", false, .nat),
      ("history", false, .list (.union
        (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)])
        (.record [("_tag", false, .lit "Withdraw"), ("amount", false, .nat)])))]
    ["id", "balance", "history"]
    (.cons (.lit (.str "acc-1")) (.cons (.lit (.nat 0)) (.cons (.app "nil" .nil) .nil)))

/-- The cleanup log's allocation request. -/
def logT : Term :=
  .field .required (.record [("v", false, .list (.prod .nat .nat))] ["v"]
    (.cons (.app "nil" .nil) .nil)) "v"

/-- **The families of the shop's sites**, as a test: each site's row and term. -/
def siteOk : NativeOp → Term → Option Nat → Bool
  | .refMake, request, _ => request == window0T || request == account0T || request == logT
  | .refGet, _, _ => true
  | .sleep, _, _ => true
  | .refModifyWith f, _, some l =>
    f == decisionAt l || (List.range 7).any fun id => f == depositAt id l
  | .refUpdateWith f, _, some l =>
    f == refillAt l || (List.range 7).any fun id => f == noteAt id l
  | _, _, _ => false

/-- **The census** (kernel evaluation of the elaborated shop, about three seconds): every one
of the shop's `perform` sites is in a family. -/
theorem shop_census :
    (shopProgram.map fun p => (performSites p).all fun site =>
      siteOk site.2.1 site.2.2.1 site.2.2.2) = some true := by
  decide

/-- An allocation of a value that satisfies a cell predicate keeps it. -/
theorem make_keeps {P : Val → Prop} (v : Val) (hv : P v) : OpKeeps P (.refMake v) := by
  intro s s' ans h hok
  have h' : (refStep (.refMake v) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  simp only [refStep, Option.map_some] at h'
  have hs : s.refs ++ [v] = s'.refs :=
    congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')
  rw [← hs]
  intro i w hw
  rw [List.getElem?_append] at hw
  split at hw
  · exact hok i w hw
  · cases hi : i - s.refs.length with
    | zero =>
      rw [hi] at hw
      cases hw
      exact hv
    | succ k =>
      rw [hi] at hw
      cases hw

/-- A read keeps every cell predicate. -/
theorem get_keeps {P : Val → Prop} (q : RefKey) : OpKeeps P (.refGet q) := by
  intro s s' ans h hok
  have h' : (refStep (.refGet q) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  cases hp : refPeek s.refs q with
  | none =>
    simp only [refStep, hp, Option.map_none] at h'
    cases h'
  | some a =>
    simp only [refStep, hp, Option.map_some] at h'
    have hs : s.refs = s'.refs :=
      congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')
    rw [← hs]
    exact hok

/-- **The deposit's write site keeps the used bound** (program-specific; new): the deposit sets
`balance` and `history` and leaves `used`. Placement: a step of `shop_sites_used`. Route: as
`decision_used`, with `read_after_set` at two fields other than `used`. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal deposit_keeps_used (id : Nat) (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refModify q (depositAt id env.length) env)

/-- **The refill's write site keeps the used bound** (program-specific; new): it writes
`used = 0`. Placement: a step of `shop_sites_used`. Route: `read_after_set` at `used`. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal refill_keeps_used (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refUpdate q (refillAt env.length) env)

/-- **The note's write site keeps the used bound** (program-specific; new): it writes a list,
whose `used` field reads as `0`. Placement: a step of `shop_sites_used`. Route: `listAppend`
answers a list, and `Record.read` of a list is `none`. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal note_keeps_used (id : Nat) (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refUpdate q (noteAt id env.length) env)

/-- One closed allocation request: its value satisfies `UsedOk` at every environment. -/
theorem closed_used (request : Term) (env : List Val)
    (hclosed : evalTerm env request = evalTerm [] request)
    (hcheck : (evalTerm [] request).all (fun v => decide (natField (some v) "used" ≤ 3)) = true)
    (v : Val) (hv : evalTerm env request = some v) : UsedOk v := by
  rw [hclosed, hv] at hcheck
  exact of_decide_eq_true hcheck

/-- The three allocations write values whose `used` field is at most three. -/
theorem allocations_used (env : List Val) (request : Term)
    (h : (request == window0T || request == account0T || request == logT) = true) (v : Val)
    (hv : evalTerm env request = some v) : UsedOk v := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl
  · exact closed_used window0T env rfl (by decide) v hv
  · exact closed_used account0T env rfl (by decide) v hv
  · exact closed_used logT env rfl (by decide) v hv

/-- **`shop_sites_used`, decomposed**: modulo the three family goals above. -/
theorem shop_sites_used_modulo (b : Api.Built)
    (hb : Effect4.Api.Author.build (shop .none) = .ok b) : SitesKeep b.program UsedOk := by
  intro path op request env val o hnode hlevel hval hop
  have hprog : shopProgram = some b.program := by
    unfold shopProgram
    rw [(build_elaborates hb).1]
    rfl
  have hmem := performSites_complete hnode
  rw [hlevel] at hmem
  have hall : (performSites b.program).all
      (fun site => siteOk site.2.1 site.2.2.1 site.2.2.2) = true := by
    have h := shop_census
    rw [hprog] at h
    exact Option.some.inj h
  have hok : siteOk op request (some env.length) = true := List.all_eq_true.mp hall _ hmem
  unfold siteOk at hok
  split at hok
  · unfold NativeOp.syncOpOf at hop
    cases hop
    exact make_keeps val (allocations_used env request hok val hval)
  · unfold NativeOp.syncOpOf at hop
    split at hop
    · cases hop
      exact get_keeps _
    · cases hop
  · unfold NativeOp.syncOpOf at hop
    cases hop
  · rename_i f l hl
    cases hl
    unfold NativeOp.syncOpOf at hop
    split at hop
    · cases hop
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hok
      rcases hok with rfl | ⟨id, _, rfl⟩
      · exact decision_keeps_used _ env
      · exact deposit_keeps_used id _ env
    · cases hop
  · rename_i f l hl
    cases hl
    unfold NativeOp.syncOpOf at hop
    split at hop
    · cases hop
      simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hok
      rcases hok with rfl | ⟨id, _, rfl⟩
      · exact refill_keeps_used _ env
      · exact note_keeps_used id _ env
    · cases hop
  · cases hok

