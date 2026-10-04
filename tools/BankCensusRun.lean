import Effect4.Laws

/-! `make bank-census`: every `Effect4.*` aesop rule bank with its rules, simp lemmas, and the
clauses that name it under `src` and `Test` (`src/Effect4/Laws/Auto/BankCensus.lean`). Not a
library module; run by `lake env lean`. An instrument, never a gate. -/
#bank_census "src" "Test"
