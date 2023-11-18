import Mathlib.Tactic

/-!
  # check

  `#check` コマンドは，項の型を表示します．
  すべての項には型があるので，どんな項にも使えます．
-/

/-!
  ## 基本的な項の型
-/

-- 1 : ℕ 自然数
#check 1

-- 1.0 : Float 浮動小数点数
#check 1.0

-- -2 : ℤ 整数
#check -2

-- 実数の名前空間を開き，`Real.pi` に `π` でアクセスできるようにする
open Real

-- π : ℝ 実数
#check π

-- `1` はそのままだと自然数扱いになるが，整数にキャストできる
#check (1 : ℤ)

/- 自然数のリスト
[1, 2, 3] : List ℕ -/
#check [1, 2, 3]

/- 自然数の配列
#[1, 2, 3] : Array ℕ -/
#check #[1, 2, 3]

/- 自然数の部分集合
{1, 2, 3} : Set ℕ -/
#check ({1, 2, 3} : Set ℕ)

-- 関数 fun x => x + 42 : ℕ → ℕ
#check fun x ↦ x + 42

-- Bool.true : Bool 真偽値
#check true

-- True : Prop 命題
#check True

/-!
  ## 型の型
  「すべての」項には型があるので，型も型を持ちます．
-/

-- Prop : Type
#check Prop

-- Set ℕ : Type
#check (Set ℕ)

/-
Lean では `List` は Type を受け取って，Type を返す関数.
List.{u} (α : Type u) : Type u
-/
#check List

-- Set.{u} (α : Type u) : Type u
#check Set

/- `Type` 自身も型を持っており…
Type : Type 1 -/
#check Type

/- この調子でいつまでも続く
Type 1 : Type 2 -/
#check Type 1

/-!
  ## 命題と証明

  Lean では命題やその証明にも型があります．
  命題の型は `Prop` で，
  命題の項が証明になっています．
-/

-- 1 + 1 = 2 : Prop 命題
#check 1 + 1 = 2

-- `1 + 1 = 2` の証明 `two_eq_add_one` を構成
theorem two_eq_add_one : 2 = 1 + 1 := by rfl

/- 証明の型が命題になっている
two_eq_add_one : 2 = 1 + 1 -/
#check two_eq_add_one

/-!
  ## 型としての True/False

  `True` は型としては一点集合であり，
  `False` は型としては空集合です．
-/

-- `trivial : True` は `True` 型を持つ項
#check trivial

/-!
  ## 関数としての証明

  命題 `P → Q` の証明は，`P → Q` という型を持つ項です．
  つまり，`P` の証明 `h : P` に対して `Q` の証明を返す関数です．
-/

lemma tautology : True -> True := fun a ↦ a

/-
暗黙の変数を明示的にするために `@` を付けたものの
`tautology : True → True` と出力されるので，
`tautology` は `True → True` という関数であることがわかる
-/
#check @tautology

/-
実際に `trivial : True` を「代入」すると
`tautology trivial : True` となり，
確かに `True` 型の項が得られていることがわかる．
-/
#check tautology trivial
