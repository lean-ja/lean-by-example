/-
# inductive
`inductive` コマンドは，帰納型(inductive type)を定義することができます．Lean でユーザが新しい型を定義する主要な方法です．

## 列挙型
帰納型の最も基本的な例は，次のような列挙型です．列挙型とは，固定された値のどれかを取るような型です．
-/
namespace Inductive --#

/-- 真か偽のどちらかの値をとる型 -/
inductive Bool : Type where
  | true
  | false

#check (Bool.true : Bool)

/- 列挙型は，帰納型の中でもすべてのコンストラクタが引数を持たないような特別な場合といえます．

## 一般の帰納型
一般には，帰納型のコンストラクタは引数を持つことができます．
-/
universe u v

/-- `α` と `β` の直和型 -/
inductive Sum (α : Type u) (β : Type v) where
  | inl (a : α) : Sum α β
  | inr (b : β) : Sum α β

/- コンストラクタの引数の型が定義しようとしているその帰納型自身であっても構いません． -/

/-- ペアノの公理によって定義された自然数 -/
inductive Nat : Type where
  | zero : Nat
  | succ (n : Nat) : Nat

end Inductive --#
