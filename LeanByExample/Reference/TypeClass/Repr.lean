/-
# Repr
`Repr` は、その型の項をどのように表示するかを指示する型クラスです。

たとえば、以下のように新しく[構造体](../Declarative/Structure.md) `Point` を定義したとき、何も指定しなくても `Point` の項を `#eval` で表示することはできますが、裏で使用しているのが `Repr` インスタンスです。
-/
namespace Repr --#

-- 平面上の点を表す構造体
structure Point (α : Type) : Type where
  x : α
  y : α

-- 原点
def origin : Point Nat := ⟨0, 0⟩

-- Repr インスタンスを暗黙的に生成しない
set_option eval.derive.repr false

/--
error: could not synthesize a 'Repr' or 'ToString' instance for type
  Point Nat
-/
#guard_msgs in #eval origin

/- エラーメッセージが示すように、`Point` が型クラス `Repr` または `ToString` のインスタンスではないため `#eval` が実行できずエラーになります。

`Repr` インスタンスの登録方法ですが、通り一遍の表示で構わなければ [`deriving`](../Declarative/Deriving.md) コマンドで Lean に自動生成させることができます。-/

deriving instance Repr for Point

#eval origin

/- あるいは、`Point` の定義時に以下のようにしても構いません。-/
namespace Hidden --#

structure Point (α : Type) : Type where
  x : α
  y : α
deriving Repr

def origin : Point Nat := ⟨0, 0⟩

#eval origin

end Hidden --#
/- ## deriving を使わない場合
`Repr` のインスタンスは [`deriving`](../Declarative/Deriving.md) コマンドで生成できますが、手動で作ることもできます。
-/

variable {α : Type}

/-- 入れ子になったリスト -/
inductive NestedList (α : Type) where
| elem : α → NestedList α
| list : List (NestedList α) → NestedList α

open Std

protected partial def NestedList.repr [Repr α] (a : NestedList α) (n : Nat) : Format :=
  let _instToFormat : ToFormat (NestedList α) := ⟨(NestedList.repr · 0)⟩
  match a, n with
  | elem x, _ => reprPrec x n
  | list as, _ => Format.bracket "[" (Format.joinSep as ("," ++ Format.line)) "]"

def sample : NestedList Nat :=
  .list [.elem 1, .list [.elem 2, .elem 3], .elem 4]

section --#
/-- Repr インスタンスを登録 -/
local instance [Repr α] : Repr (NestedList α) where
  reprPrec := NestedList.repr

/-- info: [1, [2, 3], 4] -/
#guard_msgs in #eval sample
end --#

/- また、`Repr` インスタンスがなくても [`ToString`](./ToString.md) クラスのインスタンスがあればそれが表示に使われます。-/

/-- `NestedList` を文字列に変換 -/
partial def NestedList.toString [ToString α] : NestedList α → String
  | NestedList.elem x => ToString.toString x
  | NestedList.list xs => "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

/-- `NestedList` の `ToString` インスタンスを宣言 -/
instance [ToString α] : ToString (NestedList α) where
  toString nl := NestedList.toString nl

/-- info: [1, [2, 3], 4] -/
#guard_msgs in #eval sample

end Repr --#
