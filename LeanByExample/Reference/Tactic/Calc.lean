/- # calc
`calc` は計算モードに入るためのタクティクです。推移律が成り立つような二項関係をつなげて、一つの証明項を構成します。
-/
-- `calc` そのものは `import` なしで使える
import Mathlib.Tactic -- 大雑把に import する

variable (a b : ℝ)

example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  -- a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 を示せばよい
  suffices a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 from by
    linarith

  -- 少しずつ式変形して示していく
  calc a ^ 2 - 2 * a * b + b ^ 2
    _ = (a - b) ^ 2 := by ring
    _ ≥ 0 := by positivity

/- `calc` の直後に来る項も `_` で省略することができます。 -/

/-- 掛け算 `ℝ × ℝ → ℝ` の原点における連続性 -/
example : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt

  -- 以下を示せばよい
  show |x * y| < ε

  calc
    _ = |x| * |y| := abs_mul x y
    _ < ε * ε := by gcongr
    _ ≤ 1 * ε := by gcongr
    _ = ε := by simp

/- ## カスタマイズ
自前で定義した二項関係も、`Trans` 型クラスのインスタンスにすれば `calc` で使用することができます。-/

/-- 絶対値が同じであることを表す二項関係 -/
def same_abs (x y : Int) : Prop := x = y ∨ x = - y

-- same_abs のための中値記法を用意する
-- このファイル内でだけ有効にするために local と付けた
local infix:50 " ≡ " => same_abs

/-- `same_abs` の反射性 -/
@[refl] theorem same_abs_refl (x : Int) : x ≡ x := by
  simp [same_abs]

variable {x y z : Int}

-- メタ変数の番号を表示しないようにする
set_option pp.mvars false

-- `calc` を使おうとすると
-- `Trans` 型クラスのインスタンスではないというエラーになってしまう
/--
error: invalid 'calc' step, failed to synthesize `Trans` instance
  Trans same_abs same_abs ?_
Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
  example (hxy : x ≡ y) (h : y = z) : x ≡ z := calc
    x ≡ y := hxy
    _ ≡ z := by rw [h]

/-- same_abs の推移律 -/
def same_abs_trans (hxy : x ≡ y) (hyz : y ≡ z) : x ≡ z := by
  dsimp [same_abs]

  -- hxy と hyz について場合分けをする
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz

  -- omega でカタをつける
  all_goals omega

/-- same_abs を「推移的な二項関係」として登録する -/
instance : Trans same_abs same_abs same_abs where
  trans := same_abs_trans

-- same_abs についても calc が使えるようになった！
example (hxy : x ≡ y) (h : y = z) : x ≡ z := calc
  x ≡ y := hxy
  _ ≡ z := by rw [h]
