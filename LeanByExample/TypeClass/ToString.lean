import Lean --#
/-
# ToString
`ToString` は、文字列 `String` への変換方法を提供する型クラスです。`ToString` のインスタンスになっている型の項は、`ToString.toString` 関数で文字列に変換することができます。また、[`export`](#{root}/Declarative/Export.md) されているので、単に `toString` と書いても使えます。
-/

example {α : Type} [ToString α] : ToString.toString (α := α) = toString := by rfl

/- ## 使用例 -/

/-- 標準ライブラリの `List` を真似て作った自前のリスト -/
inductive MyList (α : Type) where
  | nil : MyList α
  | cons (hd : α) (tl : MyList α) : MyList α

namespace MyList

  variable {α : Type}

  /-- リストをリストらしく `"[a₁, a₂, ..., aₙ]"` という文字列に変換する
  注意: `ToString.toString` と紛らわしいことがあるので `protected` で修飾している
  -/
  protected def toString [ToString α] : MyList α → String
    | nil => "[]"
    | ls@(cons _hd _tail) =>
      "[" ++ helper ls ++ "]"
  where
    /-- 外側の括弧抜きでリストの中身を `,` でつないで表示する -/
    helper : MyList α → String
      | nil => ""
      | cons hd .nil => toString hd
      | cons hd tail => toString hd ++ ", " ++ helper tail

  instance [ToString α] : ToString (MyList α) where
    toString := MyList.toString

  -- `toString` が正しく動作しているかテスト
  #guard (toString <| MyList.cons 1 (MyList.nil)) = "[1]"
  #guard (toString <| MyList.cons 1 (MyList.cons 2 (MyList.nil))) = "[1, 2]"

end MyList
