import Mathlib.Tactic.Set -- `set` のために必要
import Mathlib.Tactic.Linarith -- `linarith` を使うため
import Std.Tactic.Replace -- `replace` を使うため

/-! ## if 式と split -/

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
    simp [h]

  case inr h =>
    -- `2 * x < 0` の場合
    guard_hyp h: ¬2 * x ≥ 0

    -- 左辺にあった if 式が消えた
    show -(2 * x) = 2 * if x ≥ 0 then x else -x

    -- if 式を消すための補題を準備する
    have hx : ¬ x ≥ 0 := by linarith [h]

    -- `simp` で簡約
    simp [h, hx]

/-! ## match 式と split -/

-- match式を使って関数を定義する
def mysgn (x : Int) :=
  match x with
  | Int.negSucc _ => -1
  | Int.ofNat 0 => 0
  | _ => 1

example (x : Int) : mysgn (mysgn x) = mysgn x := by
  -- mysgn x を k と置く
  set k := mysgn x with h
  -- h の mysgn の定義を展開する
  unfold mysgn at h
  -- h の match の結果によって場合分け
  -- すべての場合 (k = -1, 0, 1) に関して mysgn の定義に従い計算する
  split at h
  all_goals
    rw [h]
    rfl
