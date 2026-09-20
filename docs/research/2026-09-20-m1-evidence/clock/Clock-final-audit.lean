import Effect4.Laws.Machine.Clock
#auto_census Effect4.Data.ClockMillis using aesop (rule_sets := [Effect4.Stores])
#auto_census Effect4.Store.Clock using aesop (rule_sets := [Effect4.Stores])
#print axioms Effect4.ClockMillis.ofDecimal
#print axioms Effect4.ClockMillis.ofDecimal_toDecimal
#print axioms Effect4.ClockMillis.ofDecimal_exact
#print axioms Effect4.Store.instCanonicalClockMillis
open Effect4
#guard ClockMillis.ofDecimal "0" = some 0
#guard ClockMillis.ofDecimal "9007199254740993" = some (ClockMillis.ofNat 9007199254740993)
#guard ClockMillis.ofDecimal "" = none
#guard ClockMillis.ofDecimal "00" = none
#guard ClockMillis.ofDecimal "01" = none
#guard ClockMillis.ofDecimal "-1" = none
#guard ClockMillis.ofDecimal "1_000" = none
#guard ClockMillis.ofDecimal "１２" = none
#guard Store.ClockCanonical.toVal (ClockMillis.ofNat 9007199254740993) = .str "9007199254740993"
#guard Store.ClockCanonical.ofVal (.str "9007199254740993") = some (ClockMillis.ofNat 9007199254740993)
#guard Store.ClockCanonical.ofVal (.str "01") = none
#guard Store.ClockCanonical.ofVal (.nat 1) = none
