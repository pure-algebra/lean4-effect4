import Effect4.Author
import Effect4.Program.Authoring.Application

/-!
# Bank accounts with deposits, withdrawals and transfers that keep the total of the balances

The ledger is a service of two host rows: an account's balance, and a new balance written. A
withdrawal never takes more than the balance holds. A transfer moves an amount between two
accounts: it takes from one balance exactly what it adds to the other, so the total stays the
same. The ledger's write declares the protocol that the balance it answers is the one written.
-/

set_option autoImplicit false

namespace Examples.BankAccount

open Effect4 Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Authoring.Atom (add sub lt eq pair)

/-! ## The data -/

eff_failure InsufficientFunds where available : .nat, needed : .nat
eff_failure SameAccount where account : .nat
eff_failure LedgerError message

/-! ## The ledger -/

/-- The ledger's service key. -/
def ledgerKey : ServiceKey := ⟨⟨31⟩, ⟨6⟩⟩

eff_rows Ledger key ledgerKey error LedgerError.ty cite "the bank account" where
  balance(.nat) : .nat,
  write(.prod .nat .nat) : .nat

/-- `write(account, balance)` answers the balance that it wrote. -/
def writeProtocol : RowProtocol :=
  { post := .app "eq" (termsOfList [.var 1, .app "snd" (termsOfList [.var 0])]) }

/-! ## The API -/

/-- `deposit(account, amount)`: the new balance. -/
def deposit (account amount : TermSrc) : Src NativeOp := eff do
  let balance ← Ledger.balance account
  Ledger.write (pair account (add balance amount))

/-- `withdraw(account, amount)`: the new balance; more than the balance fails, and writes
nothing. -/
def withdraw (account amount : TermSrc) : Src NativeOp := eff do
  let balance ← Ledger.balance account
  if lt balance amount then
    InsufficientFunds.raise balance amount
  else
    Ledger.write (pair account (sub balance amount))

/-- `transfer(source, target, amount)`: both new balances. The source must differ from the
target and hold the amount; otherwise nothing is written. -/
def transfer (source target amount : TermSrc) : Src NativeOp := eff do
  if eq source target then
    SameAccount.raise source
  else
    let from_ ← withdraw source amount
    let to_ ← deposit target amount
    return pair from_ to_

/-- `balance(account)`: the account's balance. -/
def balance (account : TermSrc) : Src NativeOp := Ledger.balance account

/-! ## The application -/

/-- The bank: the ledger's rows, the write's protocol, and the four programs. -/
def application : Application NativeOp :=
  { name := "bankAccount"
    rows := Ledger.rows
    protocols := [("Ledger.write", writeProtocol)]
    entries :=
      [ { name := "deposit", params := [("account", .nat), ("amount", .nat)]
          body := deposit (var "account") (var "amount") }
      , { name := "withdraw", params := [("account", .nat), ("amount", .nat)]
          body := withdraw (var "account") (var "amount") }
      , { name := "transfer", params := [("source", .nat), ("target", .nat), ("amount", .nat)]
          body := transfer (var "source") (var "target") (var "amount") }
      , { name := "balance", params := [("account", .nat)], body := balance (var "account") } ] }

end Examples.BankAccount
