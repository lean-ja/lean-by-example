/- # Append

`Append` は `++` という二項演算子のための型クラスです。ここまで [`HAppend`](#{root}/TypeClass/HAppend.md) と同じですが、`HAppend` は異なるかもしれない型 `α, β, γ` に対して連結 `(· ++ ·) : α → β → γ` を定義することができる一方で、`Append` は同じ型 `α` に対して連結 `(· ++ ·) : α → α → α` を定義することしかできません。

`+` で表される演算は可換であることが期待される（`a + b = b + a`）のに対し、`++` で表される演算は一般に可換ではありません。たとえば、文字列やリストの連結は順序に依存するため非可換です。このような非可換な連結に `+` を使うと混乱を招くため、Lean では `++` という別の記法を用意しています。
-/

-- 文字列の連結は非可換: 順序が違うと結果が異なる
#guard ("Hello, " ++ "world!" ≠ "world!" ++ "Hello, ")

-- リストの連結も非可換
#guard ([1, 2] ++ [3, 4] ≠ [3, 4] ++ [1, 2])

-- 一方、自然数の足し算は可換
#guard 2 + 3 = 3 + 2

/- ## `Append` インスタンスを実装する -/

/-- 自前で定義したリスト -/
inductive MyList where
  | nil
  | cons (head : Nat) (tail : MyList)

namespace MyList

  def append (xs ys : MyList) : MyList :=
    match xs with
    | nil => ys
    | cons x xs => cons x (append xs ys)

  -- 記法が定義されていないので使えない
  #check_failure MyList.nil ++ MyList.nil

  -- `append` 関数を `++` の実装とする
  instance : Append MyList where
    append := append

  -- 連結記号が使えるようになった
  #check MyList.nil ++ MyList.nil

end MyList

/- ## 舞台裏
`Append` 型クラスは、内部的には [`HAppend`](#{root}/TypeClass/HAppend.md) に展開されています。 -/

-- #check コマンドの出力で記法を使わないようにする
set_option pp.notation false in

/-- info: HAppend.hAppend MyList.nil MyList.nil : MyList -/
#guard_msgs in --#
#check MyList.nil ++ MyList.nil
