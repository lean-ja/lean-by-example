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
/-⋆-//--
info: invalid constructor ⟨...⟩, expected type must be an inductive type with only one constructor ⏎
  Sample
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
コンストラクタが入れ子になっている場合でも平坦化することができます。-/

#guard
  -- 入れ子にした場合
  let x : Nat × (Int × String) := ⟨1, ⟨2, "hello"⟩⟩

  -- 平坦化した場合
  let y : Nat × (Int × String) := ⟨1, 2, "hello"⟩

  -- 両者は同じものを表している！
  x = y

/- 上の例は構造体の同種のコンストラクタが入れ子になっている例ですが、`structure` コマンドで定義された型でなくても、同種のコンストラクタでもなくても、同様に平坦化することができます。 -/

/-- Prod を真似て自作した帰納型 -/
inductive MyProd (α β : Type) where
  | mk (fst : α) (snd : β)
deriving DecidableEq

-- Prod のための2項演算子
@[inherit_doc] infixr:35 " ×ₘ " => MyProd

-- 平坦化ができている！
#check (⟨1, 2, 1, 2, 1⟩ : Nat × Nat ×ₘ Nat ×ₘ Nat × Nat)

/- しかし、時には平坦化ができないケースもあります。-/
section

  variable {α β : Type} (f : α → Option (α × β))

  example (a : α) (h : ∃ (x : α × β), f a = some x) : True := by
    -- 平坦化ができない
    fail_if_success obtain ⟨a, b, hx⟩ := h

    -- 代わりにネストさせると通る
    obtain ⟨⟨a, b⟩, hx⟩ := h

    trivial
end
