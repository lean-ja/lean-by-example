import LeanByExample.Option.MissingDocs.DocBlameThm

/-⋆-//--
warning: `ex`にドキュメントコメントを与えてください。

Note: This linter can be disabled with `set_option linter.docBlameThm false`
-/
#guard_msgs in --#
theorem ex : True := by trivial

-- `private` な定理に対しては warning が出ない
#guard_msgs in --#
private theorem ex2 : True := by trivial

-- example に対しては warning が出ない
#guard_msgs in --#
example : True := by trivial

-- `def`に対しては warning が出ない
#guard_msgs in --#
def hoge := 42
