/- # 無名コンストラクタ

**無名コンストラクタ(anonymous constructor)** を使用すると、単一のコンストラクタしか持たない帰納型 `T` に対して、コンストラクタ名を指定せずに `T` 型の項を構成することができます。`⟨x1, x2, ...⟩` という構文により使うことができます。
-/

/-- 単一のコンストラクタしか持たない帰納型の例 -/
inductive Foo where
  | mk (x y : Nat)
deriving DecidableEq

#guard
  -- コンストラクタを使って項を作る場合
  let foo₁ := Foo.mk 1 2

  -- 無名コンストラクタを使って項を作る場合
  let foo₂ := ⟨1, 2⟩

  -- 両者は同じものを表す！
  foo₁ = foo₂

/- 一般の[帰納型](#{root}/Declarative/Inductive.md)に対しては使用できません。-/

/-- 複数のコンストラクタを持つ帰納型の例 -/
inductive Sample where
  | fst (foo bar : Nat)
  | snd (foo bar : String)

-- 「コンストラクタが一つしかない帰納型でなければ使用できない」というエラーになる
/--
info: Invalid `⟨...⟩` notation: The expected type `Sample` has more than one constructor

Note: This notation can only be used when the expected type is an inductive type with a single constructor
-/
#guard_msgs in --#
#check_failure (⟨"foo", "bar"⟩ : Sample)

/- ## 構造体への使用
[構造体](#{root}/Declarative/Structure.md)は単一コンストラクタしか持たない帰納型なので、構造体に対しても無名コンストラクタ構文が使用できます。-/

/-- 2つのフィールドを持つ構造体 -/
structure Hoge where
  foo : Nat
  bar : Nat

#check (⟨1, 2⟩ : Hoge)

/- ## 平坦化

コンストラクタが入れ子になっている場合、末尾側の入れ子の `⟨⟩` を省略することができます。
-/

#guard
  -- 入れ子にした場合
  let x : Nat × (Int × String) := ⟨1, ⟨-1, "hello"⟩⟩

  -- 平坦化した場合
  let y : Nat × (Int × String) := ⟨1, -1, "hello"⟩

  -- 両者は同じものを表している！
  x = y

/-
末尾側ではないと、省略できません。
-/

#check_failure
  let x := ⟨1, -1, "hello"⟩
  (x : (Nat × Int) × String)
