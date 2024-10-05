/- # \#check

`#check` コマンドは、項の型を表示します。Lean ではすべての項に型があるので、どんな項にも使えます。`#check term` というコマンドで、`term` の型を表示します。逆に `term` の型が `T` であることを確かめるには [`example`](../Declarative/Example.md) コマンドを使用して `example : T := term` とします。

## 基本的な項の型 -/

-- 文字
#check 'a'

-- 文字列
#check "Hello"

-- 自然数
#check 1

-- 浮動小数点数
#check 1.0

-- 整数
#check -2

-- `1` はそのままだと自然数扱いになるが、整数にキャストできる
#check (1 : Int)

-- 自然数のリスト
#check [1, 2, 3]

-- 自然数の配列
#check #[1, 2, 3]

-- 関数
#check fun x ↦ x + 42

-- Bool, 真偽値
#check true

-- 命題
#check True

/- ## 型の型
「すべての」項には型があるので、型も型を持ちます。
-/
-- 宇宙変数を宣言する
universe u

#check (Prop : Type)

-- Lean では `List` は Type を受け取って、Type を返す関数。
#check (List : (α : Type u) → Type u)

-- 配列も同じ。型を型に変換する関数。
#check (Array : (α : Type u) → Type u)

-- `Type` 自身も型を持っており…
#check (Type : Type 1)

#check (Type 1 : Type 2)

-- この調子で限りなく続く
#check (Type u : Type (u + 1))

/- ## 命題と証明
Lean では命題やその証明にも型があります。命題の型は `Prop` で、命題の項が証明になっています。逆に言えば、Lean ではある命題 `P : Prop` を証明するということは、`P` という型を持つ項 `proof : P` を構成することと同じです。
-/

#check (1 + 1 = 2 : Prop)

-- `1 + 1 = 2` の証明 `two_eq_add_one` を構成
theorem two_eq_add_one : 2 = 1 + 1 := by rfl

-- 証明の型が命題になっている
#check (two_eq_add_one : 2 = 1 + 1)

/- ## 型としての True/False
`True` は型としては一点集合であり、
`False` は型としては空集合です。
-/

-- `trivial : True` は `True` 型を持つ項
#check trivial

/- ## 関数としての証明
命題 `P → Q` の証明は、`P → Q` という型を持つ項です。
つまり、`P` の証明 `h : P` に対して `Q` の証明を返す関数です。
-/

theorem tautology : True -> True := fun a ↦ a

-- 暗黙の変数を明示的にするために `@` を付けた。
-- `tautology : True → True` と出力されるので、
-- `tautology` は `True → True` という関数であることがわかる
#check (@tautology : True → True)

-- 実際に `trivial : True` を「代入」すると
-- `tautology trivial : True` となり、
-- 確かに `True` 型の項が得られていることがわかる。
#check (tautology trivial : True)
