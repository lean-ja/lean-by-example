/- # 左パイプ記法

**左パイプ記法(left pipe notation)** `<|` は、パイプ記号の右側の式を左側の関数の引数として渡します。

つまり `f <| a` と書くことで `f a` と同じ意味になります。
-/

example (a : α) (f : α → β) : (f <| a) = f a := by
  rfl

/-
複数組み合わせると右側が優先して結合されます。
したがって2つ組み合わせて `g <| f <| a` のように書くと `g (f a)` と同じ意味になります。
-/

example (a : α) (f : α → β) (g : β → γ) : (g <| f <| a) = g (f a) := by
  rfl

/- ## 用途

ただの関数適用として書いても左パイプ記法を使用しても順序は変わりませんが、パイプ記法を使うと括弧を省略できます。
-/

/-- 二次元リストの和を計算して、
ログだけ出して結果を捨てる関数 -/
def sumWithLog (dlist : List (List Nat)) : IO Unit := do
  let mut current := 0
  for (list, i) in dlist.zipIdx do
    IO.println <|
      s!"{i} 番目のリスト\n" ++
      s!"  合計値: {list.sum}\n" ++
      s!"  長さ: {list.length}"
    current := current + list.sum

/--
info:
0 番目のリスト
  合計値: 6
  長さ: 3
1 番目のリスト
  合計値: 9
  長さ: 2
2 番目のリスト
  合計値: 9
  長さ: 1
-/
#guard_msgs in --#
#eval sumWithLog [[1, 2, 3], [4, 5], [9]]

/- ## 補足

双対的な概念として[右パイプ記法](#{root}/Syntax/RightPipe.md)があります。
-/
