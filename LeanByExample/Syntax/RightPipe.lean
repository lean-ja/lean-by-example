/- # 右パイプ記法

**右パイプ記法(right pipe notation)** `|>` は、パイプ記号の左側の式を右側の関数の引数として渡します。

つまり `a |> f` は `f a` と同じ意味になります。
-/

example (a : α) (f : α → β) : (a |> f) = f a := by
  rfl

/-
複数組み合わせると左側が優先して結合されます。
したがって2つ組み合わせて `x |> f |> g` のように書くと、`g (f x)` と同じ意味になります。
-/

example (a : α) (f : α → β) (g : β → γ) : (a |> f |> g) = g (f a) := by
  rfl

/- ## 用途

関数適用として書くと、先に適用する関数を後に書くことになるので順序が逆になります。
一方で右パイプ記法を使用すると、先に適用する関数を先に書くことができます。
-/

/-- `n` 以下の奇数の自乗の和を計算する -/
def sumOfOddSquares (n : Nat) : Nat :=
  List.range (n + 1)
    |> List.filter (· % 2 = 1)
    |> List.map (· ^ 2)
    |> List.sum

#guard sumOfOddSquares 3 = 1^2 + 3^2
#guard sumOfOddSquares 10 = 1^2 + 3^2 + 5^2 + 7^2 + 9^2

/- ## 補足

双対的な概念として[左パイプ記法](#{root}/Syntax/LeftPipe.md)があります。
-/
