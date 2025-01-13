/-
# ToString
`ToString` は、文字列 `String` への変換方法を提供する型クラスです。`ToString` のインスタンスになっている型の項は、`toString` 関数で文字列に変換することができます。
-/
import Lean --#

/-- 標準ライブラリの `List` を真似て作った自前のリスト -/
inductive MyList (α : Type) where
  | nil : MyList α
  | cons (hd : α) (tl : MyList α) : MyList α

namespace MyList

  variable {α : Type}

  /-- リストをリストらしく `"[a₁, a₂, ..., aₙ]"` という文字列に変換する
  **注意**: `ToString.toString` と紛らわしいことがあるので `protected` で修飾している
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



/- ## Repr と ToString の違い

[`Repr`](#{root}/TypeClass/Repr.md) と [`ToString`](#{root}/TypeClass/ToString.md) はどちらも項の表示に関わる型クラスですが、使い分けのルールが存在しており、それは `Repr` のドキュメントコメントに書かれています。
-/

open Lean Elab Command in

/-- ドキュメントコメントを取得して表示するコマンド -/
elab "#doc " x:ident : command => do
  let name ← liftCoreM do realizeGlobalConstNoOverload x
  if let some s ← findDocString? (← getEnv) name then
  logInfo m!"{s}"

/--
info: A typeclass that specifies the standard way of turning values of some type into `Format`.

When rendered this `Format` should be as close as possible to something that can be parsed as the
input value.
-/
#guard_msgs in #doc Repr

/- `Repr` の出力は Lean のコードとしてパース可能なものに可能な限り近くなければならない、つまり Lean のコードとして実行可能であることが期待されます。一方で、`ToString` は単なる `String` への変換であってそのような制約はありません。 -/
