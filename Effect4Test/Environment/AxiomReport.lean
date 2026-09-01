import Effect4.Context.Key

/-!
Fresh kernel dependency report for the environment slice.

This file is **coordinator-owned**. `docs/ENVIRONMENT-DAG.md` keeps it out of
every builder's fence on purpose: in the preceding Schema slice a shared
receipts file sat inside one builder's fence, two obligations landed after that
builder had measured its work and finished, and the receipts for them were
orphaned at a seam no fence covered. Receipts here are appended by the
coordinator after each layer closes, from the `#print axioms` output the layer's
builder reports.

Layer L0, node `F-KEY`, implementation receipts green 2026-08-31. Every frozen
declaration is axiom-free — neither `propext` nor `Quot.sound` is reached. The
`ENV-LEAF-KEY-IDENTITY` plus the local receipts for
`ENV-LEAF-KEY-ORDER-BRIDGE`; this report supplies only their axiom component.
The bridge's `DATA-PG-ROW/ORDER` attachment and
`ENV-PG-CONTEXT/ENV-KEY-INTERP` both remain open.
-/

-- D0: the two nominal carriers.
#print axioms Effect4.ServiceName
#print axioms Effect4.ServiceTypeCode
#print axioms Effect4.instDecidableEqServiceName
#print axioms Effect4.instDecidableEqServiceTypeCode

-- D1: the key itself.
#print axioms Effect4.ServiceKey
#print axioms Effect4.instDecidableEqServiceKey
#print axioms Effect4.instReprServiceKey

-- D2: the decidable strict linear order a canonical row over keys will cite.
#print axioms Effect4.ServiceKey.Lt
#print axioms Effect4.instLTServiceKey
#print axioms Effect4.instDecidableLtServiceKey
#print axioms Effect4.ServiceKey.lt_iff
#print axioms Effect4.ServiceKey.lt_irrefl
#print axioms Effect4.ServiceKey.lt_trans
#print axioms Effect4.ServiceKey.lt_trichotomy

-- Additive standard-order bridge for DATA-PG-ROW/ORDER. These declarations
-- derive `LE` and Std's law instances from the already-frozen `<`; they do not
-- introduce another comparison or alter the 25-name Context Key contract API.
#print axioms Effect4.ServiceKey.Le
#print axioms Effect4.ServiceKey.instLE
#print axioms Effect4.ServiceKey.le_iff
#print axioms Effect4.ServiceKey.instDecidableLE
#print axioms Effect4.ServiceKey.lt_asymm
#print axioms Effect4.ServiceKey.le_refl
#print axioms Effect4.ServiceKey.le_trans
#print axioms Effect4.ServiceKey.le_antisymm
#print axioms Effect4.ServiceKey.le_total
#print axioms Effect4.ServiceKey.lt_iff_le_not_le
#print axioms Effect4.ServiceKey.instIsPreorder
#print axioms Effect4.ServiceKey.instIsPartialOrder
#print axioms Effect4.ServiceKey.instIsLinearOrder
#print axioms Effect4.ServiceKey.instLawfulOrderLT

-- D3: nominal collision under differing service codes.
#print axioms Effect4.ServiceKey.Conflict
#print axioms Effect4.ServiceKey.instDecidableConflict
#print axioms Effect4.ServiceKey.conflict_iff

-- D4: the trusted boundary object and its transport.
#print axioms Effect4.ServiceUniverse
#print axioms Effect4.ServiceKey.Carrier
#print axioms Effect4.ServiceKey.carrier_def
#print axioms Effect4.ServiceKey.transport
#print axioms Effect4.ServiceKey.transport_rfl

-- The give-up, proved rather than asserted: distinct codes may read as the
-- same type, so type identity never recovers code identity.
#print axioms Effect4.ServiceUniverse.exists_carrier_collision
