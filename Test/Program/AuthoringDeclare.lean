import Effect4.Api
import Effect4.Program.Authoring.Declare
import Effect4.Program.Authoring.Records
import Effect4.Program.Authoring.Sugar
import Effect4.Program.TyEq

/-!
# AuthoringDeclare — battery for declared records and tagged failures

This file tests `eff_record` and `eff_failure` commands. It checks that declared types
and constructors match hand-written ones, and verifies the keyword `message` does not collide.
-/

set_option autoImplicit false

namespace Test.Program.AuthoringDeclare

open Effect4 Effect4.Program Effect4.Program.Authoring

/-! ## 1. Declared record -/

eff_record Todo where id : .nat, title : .string, done : .bool

/-- Hand-written record fields for comparison. -/
def handTodoFields : List (String × Bool × Ty) :=
  [("id", false, .nat), ("title", false, .string), ("done", false, .bool)]

/-- Hand-written record type for comparison. -/
def handTodoTy : Ty := .record handTodoFields

/-- Hand-written record constructor for comparison. -/
def handTodoMk (id title done : TermSrc) : TermSrc :=
  record handTodoFields [("id", id), ("title", title), ("done", done)]

#guard Todo.fields == handTodoFields
#guard Todo.ty == handTodoTy
#guard (Todo.mk (nat 1) (str "buy milk") (bool false)) {} [] ==
  (handTodoMk (nat 1) (str "buy milk") (bool false)) {} []
#guard (Todo.id (var "t")) {} [] == (field (var "t") "id") {} []
#guard (Todo.title (var "t")) {} [] == (field (var "t") "title") {} []
#guard (Todo.done (var "t")) {} [] == (field (var "t") "done") {} []

/-! ## 2. Declared failure with fields -/

eff_failure NotFound where id : .nat

/-- Hand-written failure fields for comparison. -/
def handNotFoundFields : List (String × Bool × Ty) :=
  [("_tag", false, .lit "NotFound"), ("id", false, .nat)]

/-- Hand-written failure type for comparison. -/
def handNotFoundTy : Ty := .record handNotFoundFields

/-- Hand-written failure constructor for comparison. -/
def handNotFoundMk (id : TermSrc) : TermSrc :=
  record handNotFoundFields [("_tag", str "NotFound"), ("id", id)]

#guard NotFound.fields == handNotFoundFields
#guard NotFound.ty == handNotFoundTy
#guard (NotFound.mk (nat 42)) {} [] == (handNotFoundMk (nat 42)) {} []
#guard (NotFound.is (var "err")) {} [] == (app "tagIs" [str "NotFound", var "err"]) {} []
#guard (NotFound.raise (nat 42) : Src NativeOp) {} [] ==
  (fail (NotFound.mk (nat 42)) : Src NativeOp) {} []

/-! ## 3. Declared failure with message -/

eff_failure SqlError message

/-- Hand-written message failure type for comparison. -/
def handSqlErrTy : Ty := .prod (.lit "SqlError") .string

/-- Hand-written message failure constructor for comparison. -/
def handSqlErrMk (text : TermSrc) : TermSrc :=
  app "pair" [str "SqlError", text]

#guard SqlError.ty == handSqlErrTy
#guard (SqlError.mk (str "table not found")) {} [] == (handSqlErrMk (str "table not found")) {} []
#guard (SqlError.is (var "err")) {} [] == (app "tagIs" [str "SqlError", var "err"]) {} []
#guard (SqlError.raise (str "table not found") : Src NativeOp) {} [] ==
  (fail (SqlError.mk (str "table not found")) : Src NativeOp) {} []

/-! ## 4. Keyword control: binder named `message` parses without collision -/

/-- `eff` block with a binder named `message`. -/
def testBinderMessage : Src NativeOp := eff {
  let message ← succeed (str "ok");
  succeed message
}

#guard (elaborate testBinderMessage).toOption.map Api.wellTyped = some true

/-! ## 5. Declared block of host rows (slice ROWS) -/

eff_rows TodoRepo error SqlError.ty cite "the to-do scenario" where
  insert(.string) : Todo.ty,
  all(.unit) : .list Todo.ty,
  setDone(.prod .nat .bool) : .option Todo.ty,
  delete(.nat) : .bool

/-- Hand-written row for insert. -/
def handInsert : RowDef := Row.host "TodoRepo.insert" .string Todo.ty SqlError.ty "the to-do scenario"

/-- Hand-written row for all. -/
def handAll : RowDef := Row.host "TodoRepo.all" .unit (.list Todo.ty) SqlError.ty "the to-do scenario"

/-- Hand-written row for setDone. -/
def handSetDone : RowDef :=
  Row.host "TodoRepo.setDone" (.prod .nat .bool) (.option Todo.ty) SqlError.ty "the to-do scenario"

/-- Hand-written row for delete. -/
def handDelete : RowDef := Row.host "TodoRepo.delete" .nat .bool SqlError.ty "the to-do scenario"

#guard TodoRepo.row.insert == handInsert
#guard TodoRepo.row.all == handAll
#guard TodoRepo.row.setDone == handSetDone
#guard TodoRepo.row.delete == handDelete
#guard TodoRepo.rows == [handInsert, handAll, handSetDone, handDelete]

-- A call of a declared row elaborates to Row.call of it
#guard elaborateModule { rows := TodoRepo.rows, main := TodoRepo.insert (str "milk") } =
  elaborateModule { rows := TodoRepo.rows, main := Row.call TodoRepo.row.insert (str "milk") }

#guard elaborateModule { rows := TodoRepo.rows, main := TodoRepo.insert (str "milk") } =
  .ok (.perform (.external 0) (.lit (.str "milk")))

end Test.Program.AuthoringDeclare
