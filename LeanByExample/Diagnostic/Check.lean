/- # \#check

`#check` コマンドは、項の型を表示します。Lean ではすべての項に型があるので、どんな項にも使えます。`#check term` というコマンドで、`term` の型を表示します。-/

-- 文字 `Char`
#check 'a'

-- 文字列 String
#check "Hello"

-- 自然数 Nat
#check 1

-- 浮動小数点数 Float
#check 1.0

-- 整数 Int
#check -2

-- `1` はそのままだと自然数扱いになるが、整数にキャストできる
#check (1 : Int)

-- 自然数のリスト
#check ([1, 2, 3] : List Nat)

-- 自然数の配列
#check (#[1, 2, 3] : Array Nat)

-- 関数
#check (fun x ↦ x + 42 : Nat → Nat)

-- 真偽値 Bool
#check true

-- 命題 Prop
#check True

/- 逆に `term` の型が `T` であることを確かめるには [`example`](#{root}/Declarative/Example.md) コマンドを使用して `example : T := term` とします。 -/

example : Nat := 42

example : Int := - 13

/- ## 型の型
「すべての」項には型があるので、型も型を持ちます。多くの組み込み型の型は [`Type`](#{root}/Type/Type.md) になっています。
-/

-- 文字列型の型は Type
#check (String : Type)

-- 自然数型の型は Type
#check (Nat : Type)
