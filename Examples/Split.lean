import Mathlib.Tactic.Linarith
import Std.Tactic.Replace

/-! ## split -/

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

-- match式を使って関数を定義する
def mysgn (n: Int) :=
  match n with
  | Int.negSucc _ => -1
  | Int.ofNat 0 => 0
  | _ => 1

example : ∀n, mysgn (mysgn n) = mysgn n := by
  intro n
  -- mysgn n を k と置く (h: mysgn n = k という仮定がついかされる)
  generalize h: mysgn n = k
  -- h の mysgn の定義を展開する
  unfold mysgn at h
  -- h の match の結果によって場合分け，すべての場合 (k = -1, 0, 1) に関して mysgn の定義に従い計算すると同じ結果になることが得られる
  split at h <;> rw [←h] <;> rfl
