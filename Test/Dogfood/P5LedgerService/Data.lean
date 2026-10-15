import Effect4.Author

/-! Program data shared by the battery and scenario fixtures. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.P5LedgerService

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The state: a record with a list of variants, in one cell -/

/-- `type Entry = { _tag: "Deposit"; amount } | { _tag: "Withdraw"; amount }`. -/
def entryTy : Ty :=
  .union (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)])
    (.record [("_tag", false, .lit "Withdraw"), ("amount", false, .nat)])

/-- `interface Account { id: string; balance: number; history: ReadonlyArray<Entry> }`. -/
def accountFields : List (String × Bool × Ty) :=
  [("id", false, .string), ("balance", false, .nat), ("history", false, .list entryTy)]

/-- The initial account, `{ id: "acc-1", balance: 0, history: [] }`. -/
def account0 : TermSrc :=
  record accountFields [("id", str "acc-1"), ("balance", nat 0), ("history", app "nil" [])]

/-- `{ _tag: "Deposit", amount }`. -/
def depositEntry (amount : TermSrc) : TermSrc :=
  record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)]
    [("_tag", str "Deposit"), ("amount", amount)]

/-- `{ ...a, balance: a.balance + amount, history: [...a.history, { _tag: "Deposit", amount }] }`,
the account a deposit leaves (`p5-ledger-service.ts`, `deposit`). -/
def deposited (a amount : TermSrc) : TermSrc :=
  recordSet (recordSet a "balance" (app "add" [field a "balance", amount]))
    "history" (app "append" [field a "history", app "cons" [depositEntry amount, app "nil" []]])

end Test.Dogfood.P5LedgerService
