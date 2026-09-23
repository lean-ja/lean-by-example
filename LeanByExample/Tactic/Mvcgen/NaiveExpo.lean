import Std.Tactic.Do
import Std.WP

open Std.WP

/-- 素朴に実装されたべき乗関数 -/
def naiveExpo (x n : Nat) : Nat := Id.run do
  let mut result := 1
  for _ in [:n] do
    result := result * x
  return result

-- `vcgen` が実験的機能であることを明示する
set_option experimental.vcgen true in

theorem naiveExpo_correct (x n : Nat) : naiveExpo x n = x ^ n := by
  generalize h : naiveExpo x n = r
  apply Id.of_run_eq_wp h

  vcgen invariants
  -- 不変条件を指定する
  -- `pref` は処理済みの要素のリストで、
  -- `pref.length` はこれまでにループが回った回数を表す
  -- `result` はループ内で更新される変数の値を表す
  · fun pref _ result => result = x ^ pref.length
  all_goals simp_all +zetaDelta [Nat.pow_succ]
