import Effect4.Program.Ty

/-!
Probe (scratch): does `Ty.sub` distribute a union inside a product, an option, a record and an
exit, the cases where every value of the left fits the right? The tsgo 7 control
(`tsprobe/distrib.ts`) admits cases 1 and 2 and refuses 3 to 6.
-/

open Effect4.Program

def AB : Ty := .union (.lit "A") (.lit "B")
def NS : Ty := .union .nat .string

-- 1. a tuple with a literal-union head, against the distributed union (tsgo: admitted)
#eval Ty.sub (.prod AB .string) (.union (.prod (.lit "A") .string) (.prod (.lit "B") .string))
-- 2. a record with a literal-union `_tag` (tsgo: admitted)
#eval Ty.sub (.record [("_tag", false, AB), ("x", false, .nat)])
  (.union (.record [("_tag", false, .lit "A"), ("x", false, .nat)])
          (.record [("_tag", false, .lit "B"), ("x", false, .nat)]))
-- 3. a union in a non-discriminant tuple position (tsgo: refused)
#eval Ty.sub (.prod NS .bool) (.union (.prod .nat .bool) (.prod .string .bool))
-- 4. an option of a union (no tsgo spelling; the values are equal sets)
#eval Ty.sub (.option NS) (.union (.option .nat) (.option .string))
-- 5. an exit with a union in its value (tsgo: refused)
#eval Ty.sub (.exitOf NS .never) (.union (.exitOf .nat .never) (.exitOf .string .never))
-- 6. control: a list does not distribute (mixed lists); must be false
#eval Ty.sub (.list NS) (.union (.list .nat) (.list .string))
-- 7. the other direction holds by the union rule on the left
#eval Ty.sub (.union (.prod (.lit "A") .string) (.prod (.lit "B") .string)) (.prod AB .string)
-- normal forms: does normalization distribute? (it would make 1 and 2 hold by reflexivity)
#eval repr (Ty.normalize (.prod AB .string))

-- The checker's order: `sub` on normal forms.
def subNorm (a b : Ty) : Bool := Ty.sub a.normalize b.normalize
#eval [subNorm (.prod AB .string) (.union (.prod (.lit "A") .string) (.prod (.lit "B") .string)),
  subNorm (.record [("_tag", false, AB), ("x", false, .nat)])
    (.union (.record [("_tag", false, .lit "A"), ("x", false, .nat)])
            (.record [("_tag", false, .lit "B"), ("x", false, .nat)])),
  subNorm (.prod NS .bool) (.union (.prod .nat .bool) (.prod .string .bool)),
  subNorm (.option NS) (.union (.option .nat) (.option .string)),
  subNorm (.exitOf NS .never) (.union (.exitOf .nat .never) (.exitOf .string .never)),
  subNorm (.list NS) (.union (.list .nat) (.list .string)),
  subNorm (.tuple [NS, .bool, .bool]) (.union (.tuple [.nat, .bool, .bool]) (.tuple [.string, .bool, .bool]))]
