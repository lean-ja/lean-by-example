import LeanByExample.Type.Linter.DocBlameThm

/-⋆-//--
warning: `ex`にドキュメントコメントを与えてください。

Note: This linter can be disabled with `set_option linter.docBlameThm false`
-/
#guard_msgs in --#
theorem ex : True := by trivial

-- example に対しては warning が出ない
#guard_msgs in --#
example : True := by trivial

-- `def`に対しては warning が出ない
def hoge := 42
