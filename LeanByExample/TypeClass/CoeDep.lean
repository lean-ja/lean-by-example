/-
# CoeDep
`CoeDep` は[型強制](#{root}/TypeClass/Coe.md)を行うための型クラスですが、[`Coe`](#{root}/TypeClass/Coe.md) と異なり「項に依存する型強制」(dependent coercion)を行うことができます。

たとえば空でないリストからなる型 `NonEmptyList` を定義したとします。空リストを変換する方法がないため、`List α → NonEmptyList α` という変換を定義する自然な方法はありません。しかし `CoeDep` を使えば空でないリストに限って `NonEmptyList` に変換するという型強制を定義することができます。
-/

/-- 空でないリスト -/
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

-- 型強制がないのでエラー
#check_failure ([1, 2] : NonEmptyList Nat)

variable {α : Type}

/-- 型強制。`x :: xs` という形をしている `List` の要素だけを `NonEmptyList` の項に変換する -/
instance {x : α} {xs : List α} : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := {head := x, tail := xs}

-- 型強制が定義された
#check ([1, 2] : NonEmptyList Nat)
