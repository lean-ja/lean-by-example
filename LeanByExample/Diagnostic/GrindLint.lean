/- # \#grind_lint

`#grind_lint` コマンドは、[`grind`](#{root}/Tactic/Grind.md) タクティクのために登録した定理がインスタンスの暴発を引き起こさないかどうか検査するためのコマンドです。
-/

/- ## inspect サブコマンド

`#grind_lint inspect thm` は、指定した定理を個別に詳しく調べます。
-/
set_option linter.unusedVariables false in --#

def wrap (x : Nat) : Nat := 0

theorem wrap_branch (x : Nat)
    : wrap x = wrap (2 * x) ∧ wrap x = wrap (2 * x + 1) := by
  simp [wrap]

grind_pattern wrap_branch => wrap x

-- wrap_branch を展開すると wrap が指数関数的に増えていくので、
-- 膨大なインスタンスが生成される。
/--
info: instantiating `wrap_branch` triggers more than 100 additional `grind` theorem instantiations
---
info: wrap_branch
[thm] instances
  [thm] wrap_branch ↦ 100
---
info: Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect wrap_branch
-/
#guard_msgs in --#
#grind_lint inspect wrap_branch

/-
生成されたインスタンス数が閾値を超えた場合にだけ報告をします。
閾値の値は、`(min := n)` という構文で指定できるので、全て報告してほしい場合は `min := 0` とします。
-/

def Nat.factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * Nat.factorial n

theorem Nat.factorial_succ (n : Nat) :
    Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  simp [Nat.factorial]

grind_pattern Nat.factorial_succ => n.factorial

#grind_lint inspect (min := 0) Nat.factorial_succ
