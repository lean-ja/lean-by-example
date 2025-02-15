/- # zify

`zify` タクティクは、自然数 `Nat` についての命題を整数 `Int` についての命題に変換します。
-/
import Mathlib.Tactic.Zify -- `zify` タクティクを使うのに必要
import Mathlib.Tactic.GCongr

example (x : Nat) (h : x ≥ 5) : 15 ≤ 3 * x := by
  -- 仮定とゴールを整数の不等式に変換する
  zify at h ⊢

  -- 整数についての命題に変換した
  guard_hyp h : x ≥ (5 : Int)
  guard_target = (15 : Int) ≤ 3 * ↑x

  have : (15 : Int) ≤ 3 * ↑x := calc
    (15 : Int) = 3 * 5 := by rfl
    _ ≤ 3 * ↑x := by gcongr; simp_all
  assumption
