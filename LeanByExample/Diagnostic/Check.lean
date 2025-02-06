/- # \#check

`#check` コマンドは、**項(term)** の型を表示します。Lean ではすべての項に型があるので、どんな項にも使えます。`#check term` という構文で、`term` の型を表示することができます。-/

-- 文字
/-⋆-//-- info: 'a' : Char -/
#guard_msgs in --#
#check 'a'

-- 文字列
/-⋆-//-- info: "Hello" : String -/
#guard_msgs in --#
#check "Hello"

-- 自然数
/-⋆-//-- info: 1 : Nat -/
#guard_msgs in --#
#check 1

-- 浮動小数点数
/-⋆-//-- info: 1.0 : Float -/
#guard_msgs in --#
#check 1.0

-- 整数
/-⋆-//-- info: -2 : Int -/
#guard_msgs in --#
#check -2

-- `1` はそのままだと自然数扱いになるが、整数にキャストできる
/-⋆-//-- info: 1 : Int -/
#guard_msgs in --#
#check (1 : Int)

-- 自然数のリスト
/-⋆-//-- info: [1, 2, 3] : List Nat -/
#guard_msgs in --#
#check [1, 2, 3]

-- 自然数の配列
/-⋆-//-- info: #[1, 2, 3] : Array Nat -/
#guard_msgs in --#
#check #[1, 2, 3]

-- 関数
/-⋆-//-- info: fun x => x + 42 : Nat → Nat -/
#guard_msgs in --#
#check fun x ↦ x + 42

-- 真偽値
/-⋆-//-- info: Bool.true : Bool -/
#guard_msgs in --#
#check true

-- 命題
/-⋆-//-- info: True : Prop -/
#guard_msgs in --#
#check True

/- 逆に `term` の型が `T` であることを確かめるには [`example`](#{root}/Declarative/Example.md) コマンドを使用して `example : T := term` とします。 -/

example : Nat := 42

example : Int := - 13

/- ## 型の型
「すべての」項には型があるので、特に型も型を持ちます。多くの組み込み型の型は [`Type`](#{root}/Type/Type.md) になっています。
-/

-- 文字列型の型は Type
/-⋆-//-- info: String : Type -/
#guard_msgs in --#
#check String

-- 自然数型の型は Type
/-⋆-//-- info: Nat : Type -/
#guard_msgs in --#
#check Nat
