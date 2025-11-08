import Std.Tactic.Do

set_option mvcgen.warning false

open Std.Do

/-- 素朴に実装されたべき乗関数 -/
def naiveExpo (x n : Nat) : Nat := Id.run do
  let mut result := 1
  for _ in [:n] do
    result := result * x
  return result

theorem naiveExpo_correct (x n : Nat) : naiveExpo x n = x ^ n := by
  generalize h : naiveExpo x n = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  -- 不変条件を指定する
  -- ここでは`xs`がループの進捗を表していて、
  -- `xs.prefix.length`はこれまでにループが回った回数を表す
  -- `result`はループ内で更新される変数の値を表す
  · ⇓⟨xs, result⟩ => ⌜result = x ^ xs.prefix.length⌝
  with simp_all <;> grind -- すべてのゴールに対して `mleave` に加えて `simp_all <;> grind` を適用してみる
