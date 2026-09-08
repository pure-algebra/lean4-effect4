import Effect4.Ingest.Taxonomy

/-! The table's partition, distinct wire codes and total spectrum. Fixture reachability
belongs to the recognizers' T1 gate; this contract does not claim that gate has run. -/
namespace Test.Ingest.TaxonomyContract
open Effect4.Ingest
#guard Code.all.length == 23
#guard (Code.all.filter (fun c => c.status == .active)).length == 22
#guard Code.all.filter (fun c => c.status == .reserved) == [.helperUnpinned]
#guard Code.argClosure.spectrum == .classification
#guard Code.answerHigherOrder.spectrum == .classification
#guard Code.importOpaque.spectrum == .classification
#guard Code.bindShape.spectrum == .applicativeGap
#guard Code.node.spectrum == .instrument
#print axioms Code.all_complete
#print axioms Code.reserved_iff
end Test.Ingest.TaxonomyContract
