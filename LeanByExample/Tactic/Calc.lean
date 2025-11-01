/- # calc
`calc` は計算モードに入るためのタクティクです。推移律が成り立つような二項関係をつなげて、一つの証明項を構成します。
-/
-- `calc` そのものは `import` なしで使える
import Mathlib.Tactic -- 大雑把に import する

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  -- `a ^ 2 - 2 * a * b + b ^ 2 ≥ 0` を示せばよい
  suffices hyp : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 from by
    linarith

  -- 少しずつ式変形して示していく
  have : a ^ 2 - 2 * a * b + b ^ 2 ≥ 0 := calc
    _ = (a - b) ^ 2 := by ring
    _ ≥ 0 := by positivity
  assumption

/- `≤` と `<` を `calc` で繋げることもできます。 -/

/-- 掛け算 `ℝ × ℝ → ℝ` の原点における連続性 -/
example : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt

  have : |x * y| < ε := calc
    _ = |x| * |y| := abs_mul x y
    _ < ε * ε := by gcongr
    _ ≤ 1 * ε := by gcongr
    _ = ε := by simp
  assumption

/- ## カスタマイズ
自前で定義した二項関係も、`Trans` 型クラスのインスタンスにすれば `calc` で推移律を連鎖させることができます。（ただし、細かいですが、推移律を連鎖させることが必要なければ `Trans` 型クラスのインスタンスでなくても `calc` は使えます）-/

/-- 絶対値が同じであることを表す二項関係 -/
def same_abs (x y : Int) : Prop := x = y ∨ x = - y

-- same_abs のための中置記法の2項演算子を用意する
infix:50 " ≡ " => same_abs

/-- `same_abs` の反射性 -/
@[refl] theorem same_abs_refl (x : Int) : x ≡ x := by
  simp [same_abs]

-- メタ変数の番号を表示しないようにする
set_option pp.mvars false

-- `calc` が推移律と関係なければ使えるが...
example (x : Int) : x ≡ x := calc
  _ ≡ x := by rfl

-- `calc` で推移律を連鎖させようとすると
-- `Trans` 型クラスのインスタンスではないというエラーになってしまう
/-⋆-//--
error: invalid 'calc' step, failed to synthesize `Trans` instance
  Trans same_abs same_abs ?_

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in --#
example {x y z : Int} (hxy : x ≡ y) (h : y = z) : x ≡ z := calc
  x ≡ y := hxy
  _ ≡ z := by rw [h]

/-- same_abs の推移律 -/
def same_abs_trans {x y z : Int} (hxy : x ≡ y) (hyz : y ≡ z) : x ≡ z := by
  dsimp [same_abs]

  -- hxy と hyz について場合分けをする
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz

  -- omega でカタをつける
  all_goals omega

/-- same_abs を「推移的な二項関係」として登録する -/
instance : Trans same_abs same_abs same_abs where
  trans := same_abs_trans

-- same_abs についても calc が使えるようになった！
example {x y z : Int}(hxy : x ≡ y)(h : y = z) : x ≡ z := calc
  x ≡ y := hxy
  _ ≡ z := by rw [h]

/- ## 証明が１行で終わらないとき

`calc` を使用しているとき、証明を見やすく保つためには各行の証明は１行で完結させた方が良いのですが、そうもいかない場合があります。そのような場合、その行の証明項をメタ変数で置き換えると、証明を後回しにすることができます。
-/

example {x y z : Int} (hxy : x = y) (h : y = z) : x = z := by
  have : x = z := calc
    x = y := ?lem -- この行の証明を後回しにすることができる
    _ = z := by rw [h]
  assumption

  -- 後回しにした証明を埋める
  case lem =>
    rw [hxy]
