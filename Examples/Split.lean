import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Says
import Std.Tactic.Replace

set_option says.no_verify_in_CI true

-- ANCHOR: first
-- if 式を使って関数を定義する
def myabs (x : Int) : Int :=
  if x ≥ 0 then x else - x

example (x : Int) : myabs (2 * x) = 2 * myabs x := by
  -- `myabs` の定義を展開する
  unfold myabs

  -- ゴールの中に if 式があって複雑
  show (if 2 * x ≥ 0 then 2 * x else -(2 * x)) = 2 * if x ≥ 0 then x else -x

  -- `split` タクティクでケース分割する
  split

  case inl h =>
    -- `2 * x ≥ 0` の場合
    guard_hyp h: 2 * x ≥ 0

    -- 左辺にあった if 式が消えた
    show 2 * x = 2 * if x ≥ 0 then x else -x

    replace h : x ≥ 0 := by linarith [h]

    -- `simp` で if を消すことができる
    simp? [h] says
      simp only [ge_iff_le, h, ite_true]

  case inr h =>
    -- `2 * x < 0` の場合
    guard_hyp h: ¬2 * x ≥ 0

    -- 左辺にあった if 式が消えた
    show -(2 * x) = 2 * if x ≥ 0 then x else -x

    -- if 式を消すための補題を準備する
    have hx : ¬ x ≥ 0 := by linarith [h]

    -- `simp` で簡約
    simp? [h, hx] says
      simp only [ge_iff_le, hx, ite_false, mul_neg]
-- ANCHOR_END: first
