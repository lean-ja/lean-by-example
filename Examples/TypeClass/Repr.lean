/-
# Repr
`Repr` は，その型の項をどのように表示するかを指示する型クラスです．

たとえば，以下のように新しく構造体 `Point` を定義したとき，特に何も指定しなければ `Point` の項を `#eval` で表示することはできません．
-/
namespace Repr --#

-- 平面上の点を表す構造体
structure Point (α : Type) : Type where
  x : α
  y : α

-- 原点
def origin : Point Nat := ⟨0, 0⟩

/--
error: expression
  origin
has type
  Point Nat
but instance
  Lean.Eval (Point Nat)
failed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `Lean.Eval` class
-/
#guard_msgs in --#
#eval origin

/- エラーメッセージが示すように，これは `Point` が型クラス `Lean.Eval` のインスタンスではないからです．エラーメッセージには，`Repr` クラスのインスタンスであれば自動的に `Lean.Eval` のインスタンスにもなることが書かれています．通常，`Lean.Eval` のインスタンスを手で登録することはなく，`Repr` インスタンスによって自動生成させます．

`Repr` インスタンスの登録方法ですが，通り一遍の表示で構わなければ `deriving` コマンドで Lean に自動生成させることができます．-/

deriving instance Repr for Point

#eval origin

/- あるいは，`Point` の定義時に以下のようにしても構いません．-/
namespace Hidden --#

structure Point (α : Type) : Type where
  x : α
  y : α
deriving Repr

def origin : Point Nat := ⟨0, 0⟩

#eval origin

end Hidden --#
end Repr --#
